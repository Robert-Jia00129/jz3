from io import StringIO
import z3
import warnings
from . import run_solvers
from dataclasses import dataclass
from typing import *


class InequivalentConditionalConstraints(UserWarning):
    pass


@dataclass(frozen=True)
class CVRun:
    assignment: dict[str, bool]  # e.g. {"arith_range": True, "arith_split": False}
    smt2: str  # inner smt2 for this CV assignment
    sat: z3.CheckSatResult  # sat/unsat/unknown
    solver_results: Optional[Dict] = None  # solver -> (total_time, did_timeout, ans) from run_solvers


# child class to write push and pop to SMT2 file
class Solver(z3.Solver):
    def __init__(self, benchmark_mode=False, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.__history = []  # list of (operation, args). Records all assertions, push, pop, checks to generate smt2 str
        self.__assertions = []
        self.__global_constraints = z3.BoolVal(True)
        self.__canonical_smt_str: str = ""  # smt2 of the first cv comb we tried
        self.__condition_var_assignment_model = None
        self.__multi_solver_mode = benchmark_mode
        self.__CVs = set()  # condition variables
        self.__result = None
        self.__decls = {}
        self.__record_initialized = False
        self.__runs: List[CVRun] = []
    
    def __getattribute__(self, name):
        _allowed_methods = ['add', 'add_global_constraints', 'add_conditional_constraint',
                            'check_conditional_constraints', 'check', 'push', 'pop',
                            'generate_smtlib', '_allowed_methods',
                            'ctx', 'solver', 'set', 'assert_exprs', 'to_smt2', 'assertions',
                            'get_condition_var_assignment_model',
                            'get_var_assignments_and_solvers_performance']
        if name.startswith('_') or name in _allowed_methods:  # intentionally accessing a private variable
            return object.__getattribute__(self, name)
        else:
            warnings.warn(f"Method '{name}' is called.\n "
                          f"But this method might not be recorded to smt2 file and might incur potential logic errors"
                          f"Please use only the methods defined in Solver2SMT.\n"
                          f"If this is intentional, modified the _allowed_methods above")
            return super().__getattribute__(name)
    
    def start_recording(self):
        # deprecation warning
        warnings.warn("start_recording is deprecated; recording starts automatically upon Solver creation.",
                      DeprecationWarning, stacklevel=2)
        return
    
    def _collect_decls(self, e: z3.ExprRef):
        # Collect all uninterpreted symbols used in e (consts + uninterpreted functions).
        # This ignores built-in operators like +, <=, And, etc.
        decls = z3.z3util.get_decls(e)
        
        for d in decls:
            if d.kind() != z3.Z3_OP_UNINTERPRETED:
                continue
            
            name = d.name()
            
            # Const (arity 0)
            if d.arity() == 0:
                rng = d.range().sexpr()
                line = f"(declare-fun {name} () {rng})"
            else:
                dom = " ".join(d.domain(i).sexpr() for i in range(d.arity()))
                rng = d.range().sexpr()
                line = f"(declare-fun {name} ({dom}) {rng})"
            
            self.__decls.setdefault(name, line)
    
    def add_global_constraints(self, *constraints):
        """
        Sets global constraints that encodes rules/constraints for the condition variables.
        :param constraints: A list of Z3 constraints that define global conditions.
        """
        self.__global_constraints = z3.And(self.__global_constraints, *constraints)
    
    def add(self, *args):
        # self._conditional_constraints.append((args,condition))
        for arg in args:
            self._collect_decls(arg)
            self.__history.append(("add", str(arg.sexpr())))
        super().add(*args)
    
    def add_conditional_constraint(self, *args, condition: z3.BoolRef = z3.BoolVal(True)):
        """
        Adds conditional constraints that are only active when the specified condition variable is true.
        The condition variable MUST be an atomic Bool variable (not a composed expression).
        """
        if condition is None:
            condition = z3.BoolVal(True)
        
        # Validate CV: allow True; otherwise must be an atomic Bool const
        if not (z3.is_true(condition) or (
                z3.is_bool(condition)
                and z3.is_const(condition)
                and condition.decl().kind() == z3.Z3_OP_UNINTERPRETED
        )):
            raise TypeError(
                "condition must be z3.BoolVal(True) or an atomic Bool variable (e.g., z3.Bool('encoding1')). "
                "Composed expressions like z3.And(a, b) are not allowed."
            )
        
        for conditional_constraint in args:
            self.__assertions.append((conditional_constraint, condition))
            if not z3.is_true(condition):
                self.__CVs.add(condition)
        
        s = z3.Solver()
        s.add(self.__global_constraints)
        if s.check() != z3.sat:
            raise RuntimeError(
                "There is no way to satisfy all condition variables provided under global constraint"
            )
    
    def _eval_bool(self, m: z3.ModelRef, b: z3.BoolRef) -> bool:
        # b is atomic Bool (per your invariant) OR BoolVal(True)
        return z3.is_true(m.eval(b, model_completion=True))
    
    def _block_model(self, m: z3.ModelRef, cvs: list[z3.BoolRef]) -> z3.BoolRef:
        """
        Block exactly this CV assignment.
        For each CV v:
          - if m[v] is True, add ¬v
          - else add v
        Then OR them so at least one CV differs next time.
        """
        if not cvs:
            # No CVs to vary => only one assignment exists; blocking makes UNSAT to avoid infinite loop.
            return z3.BoolVal(False)
        
        lits = []
        for v in cvs:
            val = self._eval_bool(m, v)
            lits.append(z3.Not(v) if val else v)
        return z3.Or(lits)
    
    def check_conditional_constraints(self, *args, condition=z3.BoolVal(True), max_count=5):
        """
        Meta-solver approach: enumerate CV assignments satisfying __global_constraints (no duplicates),
        materialize enabled conditional constraints, and solve.

        In non-benchmark mode: runs the first satisfiable CV assignment only.
        In benchmark mode: runs up to max_count distinct CV assignments.
        """
        # reset all our CV -> solver result records
        self.__runs = []
        self.__canonical_smt_str = ""
        self.__result = None
        
        meta = z3.Solver()  # meta-solver over CVs only
        meta.add(self.__global_constraints)
        # Force CV==True, just for this check.
        if not z3.is_true(condition):
            meta.add(condition)
        
        cvs = list(self.__CVs)  # guaranteed atomic Bool CVs (no True)
        
        # Reset outputs for this call
        self.__condition_var_assignment_model = []
        
        count_limit = max_count if self.__multi_solver_mode else 1
        count = 0
        first_result = None
        
        cvs = sorted(cvs, key=lambda v: v.decl().name())  # consistent order
        
        while count < count_limit and meta.check() == z3.sat:
            m = meta.model()
            
            # Actual solver. Checks the enabled CV.
            inner = Solver()
            
            for (cc, cv) in self.__assertions:
                enabled = z3.is_true(cv) or self._eval_bool(m, cv)
                if enabled:
                    inner.add(cc)
            
            res = inner.check(*args)
            
            if count == 0:
                first_result = res
            
            # Store assignment (as a python dict for stability)
            assignment = {v.decl().name(): self._eval_bool(m, v) for v in cvs}
            self.__condition_var_assignment_model.append(assignment)
            
            smt2_str = inner.generate_smtlib()
            solver_results = None
            if self.__multi_solver_mode: # TODO: Maybe get rid of this. Instead configure how many solvers we want in run_sovlers
                solver_results = run_solvers.run_solvers(smt2_str=smt2_str, verbose=False)
                
                # Optional: keep your cross-assignment discrepancy
                if self.__result is None:
                    self.__result = res
                elif res != self.__result:
                    msg = ("Results of using different CVs differ. The conditional_constraints you added are not equivalent. \n"
                           "If this is intentional, you can supress warnings of InequivalentConditionalConstraints category\n")
                    warnings.warn(msg, InequivalentConditionalConstraints)
            run = CVRun(
                assignment=assignment,
                smt2=smt2_str,
                sat=res,
                solver_results=solver_results if self.__multi_solver_mode else None,
            )
            # Block this exact CV assignment to avoid duplicates
            meta.add(self._block_model(m, cvs))
            
            self.__runs.append(run) # record this CV assignment run
            
            if not self.__canonical_smt_str:
                self.__canonical_smt_str = smt2_str
            
            count += 1
        
        if count == 0:
            raise RuntimeError(
                "Impossible to find any way of setting CVs under global constraints "
                "(meta-solver over __global_constraints is UNSAT)."
            )
        
        return first_result
    
    def check_conditional_constraints_hamming(self, *args, condition=z3.BoolVal(True), max_count=5):
        """
        # TODO: BUGFIX: Not tested yet.
        Evaluates conditional constraints on a given model and records various solver results based on the conditions.
        
        conditions should be atomic boolean variables! composed expression like z3.And(a,b) is not allowed!
        
        This method checks the satisfiability of global constraints combined with additional conditional constraints,
        provided dynamically. It also handles the benchmark mode where it tries to find distinct solutions by
        maximizing the Hamming distance between successive models, thus exploring the space of possible solutions.

        Parameters:
        - args : tuple
            The arguments that represent additional constraints to be temporarily added for this check.
        - condition : z3.BoolVal, optional
            A Z3 boolean expression that must be satisfied for the conditional constraints to be added.
            Default is z3.BoolVal(True), which means all conditions are considered true.
        - max_count : int, optional
            The maximum number of distinct model solutions (if there exist) to find in benchmark mode. Default is 5.

        Returns:
        - z3.CheckSatResult
            The result of the final check with all conditional constraints applied.

        Notes:
        - In benchmark mode, this method also attempts to record and analyze differences in solver outputs by
          generating different variable assignments that maximize the Hamming distance between them.
        - This method internally manages several instances of the Solver class, depending on the mode of operation
          and whether additional checks are performed.

        """
        s = z3.Solver()
        s.add(self.__global_constraints)
        
        # temporarily add the constraint and conditional constraint to be checked.
        for arg in args:  # append the checked condition
            self.__assertions.append((arg, condition))
        
        if s.check() == z3.sat:
            # possible combination of condition variables
            model = s.model()
            
            solver_with_conditional_constraint = Solver()
            
            # add corresponding conditional constraints and try to solve
            for (conditional_constraint, condition) in self.__assertions:
                if condition == z3.BoolVal(True) or model.eval(condition):
                    self.__history.append(("add", str(conditional_constraint.sexpr())))
                    solver_with_conditional_constraint.add(conditional_constraint)
            
            # Don't really record the smt files
            solver_with_conditional_constraint.start_recording()
            result = solver_with_conditional_constraint.check()
            
            self.__condition_var_assignment_model = [model]
            
            # Only launch multiple solvers when in benchmark mode
            if self.__multi_solver_mode:
                self.__runs = []
                
                # find different combinations
                opt = z3.Optimize()
                opt.add(self.__global_constraints)
                
                # Only atomic Bool CVs
                cv_vars = [
                    v for v in self.__CVs
                    if z3.is_bool(v)
                       and z3.is_const(v)
                       and v.decl().kind() == z3.Z3_OP_UNINTERPRETED
                ]
                
                def eval_bool(m, v):
                    return z3.is_true(m.eval(v, model_completion=True))
                
                def block_assignment(assign_dict):
                    # Blocks exactly this assignment
                    lits = []
                    for v in cv_vars:
                        val = assign_dict[v]
                        lits.append(z3.Not(v) if val else v)
                    return z3.Or(lits) if lits else z3.BoolVal(False)
                
                prev_assignments = []  # list[dict[BoolRef,bool]]
                
                count = 0
                min_dist = z3.Int("min_hamdist")
                
                while count < max_count:
                    opt.push()
                    
                    # Objective: assignments as different as possible
                    if prev_assignments:
                        dists = []
                        for a in prev_assignments:
                            dists.append(z3.Sum([
                                z3.If(v != z3.BoolVal(a[v]), 1, 0)
                                for v in cv_vars
                            ]))
                        
                        opt.add(min_dist >= 0)
                        for d in dists:
                            opt.add(min_dist <= d)
                        
                        h = opt.maximize(min_dist)
                    else:  # First pick: no prior points, any sat assignment is fine
                        h = None
                    
                    if opt.check() != z3.sat:  # exhausted all assignments
                        opt.pop()
                        break
                    
                    m = opt.model()
                    
                    # Materialize current assignment into Python dict
                    curr = {v: eval_bool(m, v) for v in cv_vars}
                    
                    opt.pop()
                    
                    # Use 'curr' to build/run solver_with_conditional_constraint as you do now
                    solver_with_conditional_constraint = Solver()
                    for (conditional_constraint, condition) in self.__assertions:
                        if condition == z3.BoolVal(True) or curr[condition]:
                            solver_with_conditional_constraint.add(conditional_constraint)
                    
                    result = solver_with_conditional_constraint.check()
                    
                    prev_assignments.append(curr)
                    opt.add(block_assignment(curr))
                    count += 1
                
                # store smt file/str
                self.__canonical_smt_str = solver_with_conditional_constraint.generate_smtlib()
                
                with open("conditional_constraints.smt2", "w") as file:  # TODO
                    file.write(self.__canonical_smt_str)
                
                # launch multiple solvers and store resutls
            
            # pop the temporarily added conditional constraints
            for _ in args:
                self.__assertions.pop()
            
            self.__history.append(("result", str(solver_with_conditional_constraint.check(*args))))
            return result
        else:
            raise RuntimeError("Impossible to find any way of building constraints"
                               "The conditional constraints are not satisfiable under global constraints ")
    
    def push(self):
        self.__history.append(("push", None))
        super().push()
    
    def pop(self, *args, **kwargs):
        self.__history.append(("pop", None))
        super().pop(*args, **kwargs)
    
    def check(self, *args):
        if args:
            # Record assumptions distinctly (do NOT treat as asserts)
            for arg in args:
                assert z3.is_bool(arg), "Assumptions must be boolean expressions"
                self._collect_decls(arg)
            self.__history.append(("check_assuming", [str(a.sexpr()) for a in args]))
            
            res = super().check(*args)  # REAL assumptions semantics
            self.__history.append(("result", res))
            
            return res
        
        self.__history.append(("check", ""))
        res = super().check(*args)
        self.__history.append(("result", res))
        return res
    
    def get_runs(self) -> list[CVRun]:
        return list(self.__runs)
    
    def get_condition_var_assignment_model(self):
        return [r.assignment for r in self.__runs]
    
    def get_var_assignments_and_solvers_performance(self):
        return [
            {
                "assignment": r.assignment,
                "sat": str(r.sat),
                "solver_results": r.solver_results,
            }
            for r in self.__runs
        ]
    
    def get_smt2_per_assignment(self):
        return [
            {"assignment": r.assignment, "smt2": r.smt2, "sat": str(r.sat)}
            for r in self.__runs
        ]
    
    def generate_smtlib(self):
        if self.__canonical_smt_str:
            return self.__canonical_smt_str
        return self._generate_outer_replay_smtlib()
    
    def _generate_outer_replay_smtlib(self):
        output = StringIO()
        output.write(f"(set-logic QF_LIA)\n")
        for name in sorted(self.__decls):
            output.write(self.__decls[name] + "\n")
        for operation in self.__history:
            op, args = operation
            if op == "initial_state":
                output.write(args)
            elif op == "add":
                output.write(f"(assert {args})\n")
            elif op in ["push", "pop"]:
                output.write(f"({op} 1)\n")
            elif op == "check":
                output.write("(check-sat)\n")
            elif op == "result":
                output.write(f"; Result: {args}\n")
            elif op == "check_assuming":
                output.write(f"(check-sat-assuming ({' '.join(args)}))\n")
            else:
                raise RuntimeError(f"Unknown operation: {op} in z3_wrapper.Solver.generate_smtlib")
        
        smt_str = output.getvalue()
        output.close()
        return smt_str


def solver_demo():
    solver = Solver()
    
    time = z3.Int("time")
    
    # Encoding selector CVs
    arith_range = z3.Bool("arith_range")
    arith_split = z3.Bool("arith_split")
    bool_onehot = z3.Bool("bool_onehot")
    
    # Encoding 1: range [8,17] excluding 12
    solver.add_conditional_constraint(
        z3.And(8 <= time, time <= 17, time != 12),
        condition=arith_range,
    )
    
    # Encoding 2: split range excluding 12
    solver.add_conditional_constraint(
        z3.Or(
            z3.And(8 <= time, time < 12),
            z3.And(12 < time, time <= 17),
        ),
        condition=arith_split,
    )
    
    # Encoding 3: one-hot hours 8..17, excluding 12
    hours = list(range(8, 18))
    hour_is = {h: z3.Bool(f"hour_is_{h}") for h in hours}
    
    for h in hours:
        solver.add_conditional_constraint(
            z3.Implies(hour_is[h], time == h),
            condition=bool_onehot,
        )
    
    solver.add_conditional_constraint(
        z3.PbEq([(hour_is[h], 1) for h in hours], 1),
        condition=bool_onehot,
    )
    solver.add_conditional_constraint(z3.Not(hour_is[12]), condition=bool_onehot)
    
    # Exactly one encoding enabled
    solver.add_global_constraints(
        z3.PbEq([(arith_range, 1), (arith_split, 1), (bool_onehot, 1)], 1)
    )
    
    # SAT queries
    print("arith_range, time=11:", solver.check_conditional_constraints(time == 11, condition=arith_range))
    print("arith_split, time=11:", solver.check_conditional_constraints(time == 11, condition=arith_split))
    print("bool_onehot, hour_is_11:", solver.check_conditional_constraints(hour_is[11], condition=bool_onehot))
    
    # UNSAT queries
    print("arith_range, time=12:", solver.check_conditional_constraints(time == 12, condition=arith_range))
    print("arith_split, time=12:", solver.check_conditional_constraints(time == 12, condition=arith_split))
    print("bool_onehot, hour_is_12:", solver.check_conditional_constraints(hour_is[12], condition=bool_onehot))


if __name__ == '__main__':
    solver_demo()
