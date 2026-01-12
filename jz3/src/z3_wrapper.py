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



@dataclass
class _CVEnumCacheEntry:
    entries: List[Dict[str, Any]]          # [{"cv_assumptions": [...], "assignment": {...}}, ...]
    blocks: List[z3.BoolRef]               # blocking constraints to avoid repeats
    exhausted: bool = False

class Solver(z3.Solver):
    """
    Persistent incremental solver with:
      - Conditional constraints encoded as (=> CV constraint) asserted ONCE.
      - CV assignment selected via check-sat-assuming (assumptions).
      - Recording for two SMT2 exports:
          * snapshot: only the final user check (if current)
          * transcript: full incremental user session
      - Internal checks for CV enumeration are NOT recorded (bypass check override).
    """

    def __init__(self, benchmark_mode: bool = False, record_smt: bool = False, *args, **kwargs):
        super().__init__(*args, **kwargs)

        # Records all state-mutating ops AND user checks, in order.
        # Each entry is (op, payload):
        #   - ("add", "<sexpr>")
        #   - ("push", None)
        #   - ("pop", None)
        #   - ("check", None)
        #   - ("check_assuming", ["<sexpr>", ...])
        #   - ("result", "<sat|unsat|unknown>")
        self.__history: List[Tuple[str, Any]] = []

        # Conditional constraints registry (for CV enumeration reporting / runs)
        self.__assertions: List[Tuple[z3.BoolRef, z3.BoolRef]] = []  # (constraint, cv)

        # Global constraints over CVs only (meta space)
        self.__meta_solver = z3.Solver()

        self.__canonical_smt_str: str = ""  # smt2 of the first CV assignment run
        self.__multi_solver_mode = benchmark_mode
        self.__record_smt = record_smt # use jz3 to customize smt2 recording (includes push, pop, check-assuming)
        
        self.__CVs = set()  # atomic Bool CVs
        # --- CV enumeration cache ---
        # Keyed by (epoch, condition_sexpr, count_limit) -> list[{"cv_assumptions": [...], "assignment": {...}}]
        self.__cv_enum_cache: Dict[str, _CVEnumCacheEntry] = {}
        
        self.__result = None

        # For SMT2 emission
        self.__decls: Dict[str, str] = {}

        # For check_conditional_constraints outputs
        self.__runs: List[CVRun] = []
        self.__condition_var_assignment_model: List[dict[str, bool]] = []
        
        
    def __getattribute__(self, name):
        _allowed_methods = [
            'add', 'add_global_constraints', 'add_conditional_constraint',
            'check_conditional_constraints', 'check', 'push', 'pop',
            'generate_smtlib', 'generate_smt2_snapshot', 'generate_smt2_transcript',
            'get_condition_var_assignment_model',
            'get_var_assignments_and_solvers_performance', 'get_runs',
            'ctx', 'solver', 'set', 'assert_exprs', 'to_smt2', 'assertions',
            '_allowed_methods',
        ]
        if name.startswith('_') or name in _allowed_methods:
            return object.__getattribute__(self, name)
        warnings.warn(
            f"Method '{name}' is called.\n"
            f"This method might not be recorded to SMT2 and might incur potential logic errors.\n"
            f"Please use only methods defined in Solver.\n"
            f"If intentional, modify _allowed_methods."
        )
        return super().__getattribute__(name)

    # Collect declarations for the SMT2 header
    def _collect_decls(self, e: z3.ExprRef):
        def add_decl(d: z3.FuncDeclRef):
            if d.kind() != z3.Z3_OP_UNINTERPRETED:
                return
            name = d.name()
            if name in self.__decls:
                return
            if d.arity() == 0:
                rng = d.range().sexpr()
                line = f"(declare-fun {name} () {rng})"
            else:
                dom = " ".join(d.domain(i).sexpr() for i in range(d.arity()))
                rng = d.range().sexpr()
                line = f"(declare-fun {name} ({dom}) {rng})"
            self.__decls[name] = line

        seen = set()

        def walk(t: z3.AstRef):
            tid = t.get_id()
            if tid in seen:
                return
            seen.add(tid)
            if z3.is_app(t):
                add_decl(t.decl())
                for ch in t.children():
                    walk(ch)
                return
            if z3.is_quantifier(t):
                walk(t.body())
                return

        walk(e)

    # ----------------------------
    # Global CV constraints (meta only)
    # ----------------------------
    def add_global_constraints(self, *constraints):
        """
        Constraints over CVs (meta-space). These are NOT asserted into the main solver.
        They are used only for enumerating valid CV assignments in check_conditional_constraints.
        """
        if not constraints:
            return
        for c in constraints:
            self._collect_decls(c)
        self.__meta_solver.add(*constraints)
        self.__cv_enum_cache.clear()

        if self.__meta_solver.check() != z3.sat: # No valid CV assignment
            raise RuntimeError("Global CV constraints are UNSAT; no CV assignment is possible.")

    # Base operations (recorded)
    def add(self, *args):
        for arg in args:
            self._collect_decls(arg)
            self.__history.append(("add", arg.sexpr()))
        super().add(*args)

    def push(self):
        self.__history.append(("push", None))
        super().push()

    def pop(self, n=1):
        self.__history.append(("pop", int(n)))
        super().pop(n)

    # Conditional constraints: assert ONCE as guarded implications
    def add_conditional_constraint(self, *args, condition: z3.BoolRef = z3.BoolVal(True)):
        """
        Adds constraints that are active when `condition` is true.
        Encodes each arg (conditional constraint) as:
          - assert cc                                if condition is True
          - assert (condition=> condition cc)        otherwise
        """
        if condition is None:
            condition = z3.BoolVal(True)

        # Validate CV: allow True; otherwise must be atomic Bool const (uninterpreted)
        if not (z3.is_true(condition) or (
            z3.is_bool(condition)
            and z3.is_const(condition)
            and condition.decl().kind() == z3.Z3_OP_UNINTERPRETED
        )):
            raise TypeError(
                "condition must be z3.BoolVal(True) or an atomic Bool variable "
                "(e.g., z3.Bool('encoding1')). Composed expressions are not allowed."
            )

        # Track CVs (meta-space)
        if not z3.is_true(condition):
            if condition not in self.__CVs:
                self.__CVs.add(condition)
                self.__cv_enum_cache.clear()

        # Assert into the MAIN solver once, guarded by the CV.
        for cc in args:
            self.__assertions.append((cc, condition))
            if z3.is_true(condition):
                self.add(cc)
            else:
                self.add(z3.Implies(condition, cc))

        # Sanity: global constraints still satisfiable (meta)
        if self.__meta_solver.check() != z3.sat:
            raise RuntimeError(
                "There is no way to satisfy CVs under global constraints after adding this CV."
            )

    # ----------------------------
    # User-facing check (recorded)
    # ----------------------------
    def check(self, *args):
        if args:
            for a in args:
                if not z3.is_bool(a):
                    raise TypeError("Assumptions must be boolean expressions")
                self._collect_decls(a)
            self.__history.append(("check_assuming", [a.sexpr() for a in args]))
            res = super().check(*args)
            self.__history.append(("result", str(res)))
            return res

        self.__history.append(("check", None))
        res = super().check()
        self.__history.append(("result", str(res)))
        return res

    # Internal check that MUST NOT be recorded (bypass override)
    def _check_no_record(self, *assumptions: z3.BoolRef) -> z3.CheckSatResult:
        for a in assumptions:
            self._collect_decls(a)
        return z3.Solver.check(self, *assumptions)

    # ----------------------------
    # CV enumeration utilities
    # ----------------------------
    def _eval_bool(self, m: z3.ModelRef, b: z3.BoolRef) -> bool:
        return z3.is_true(m.eval(b, model_completion=True))

    def _block_model(self, m: z3.ModelRef, cvs: list[z3.BoolRef]) -> z3.BoolRef:
        if not cvs:
            return z3.BoolVal(False)
        lits = []
        for v in cvs:
            val = self._eval_bool(m, v)
            lits.append(z3.Not(v) if val else v)
        return z3.Or(lits)
    
    def _condition_key(self, condition: z3.BoolRef) -> str:
        return "true" if z3.is_true(condition) else condition.sexpr()
    
    def _ensure_cv_models(self, *, condition: z3.BoolRef, need: int) -> _CVEnumCacheEntry:
        """
        Ensure at least `need` distinct CV models are cached for this condition,
        unless the space is exhausted.
        Growth strategy: start at 5, then double.
        """
        assert need >= 1
        
        key = self._condition_key(condition)
        cache = self.__cv_enum_cache.get(key)
        if cache is None:
            cache = _CVEnumCacheEntry(entries=[], blocks=[], exhausted=False)
            self.__cv_enum_cache[key] = cache
        
        if cache.exhausted or len(cache.entries) >= need:
            return cache
        
        # Doubling target
        cur = len(cache.entries)
        target = max(5 if cur == 0 else 2 * cur, need)
        
        meta = self.__meta_solver
        cvs = sorted(list(self.__CVs), key=lambda v: v.decl().name())
        
        meta.push()
        try:
            if not z3.is_true(condition):
                meta.add(condition)
            
            # Re-add prior blocks for this condition to continue enumeration without repeats
            if cache.blocks:
                meta.add(*cache.blocks)
            
            while len(cache.entries) < target:
                if meta.check() != z3.sat:
                    cache.exhausted = True
                    break
                
                m = meta.model()
                cv_lits = [v if self._eval_bool(m, v) else z3.Not(v) for v in cvs]
                
                # Ensure `condition` itself is included as an assumption in the *main* check
                if not z3.is_true(condition) and condition not in cvs:
                    cv_lits = [condition] + cv_lits
                
                assignment = {v.decl().name(): self._eval_bool(m, v) for v in cvs}
                if not z3.is_true(condition) and z3.is_bool(condition) and z3.is_const(condition):
                    assignment[condition.decl().name()] = True
                
                cache.entries.append({"cv_assumptions": cv_lits, "assignment": assignment})
                
                blk = self._block_model(m, cvs)
                cache.blocks.append(blk)
                meta.add(blk)
            
            return cache
        finally:
            meta.pop()
    
    # ----------------------------
    # Conditional constraint checking (NOT recorded in transcript)
    # ----------------------------
    def check_conditional_constraints(self, *args, condition=z3.BoolVal(True), max_count=3):
        """
        Enumerate CV assignments satisfying global constraints, then check the MAIN solver
        under assumptions (CV literals + user assumptions).

        Important: The checks performed inside this method are NOT appended to __history,
        so transcripts do not include CV-assignment checks.
        """
        self.__runs = []
        self.__canonical_smt_str = ""
        self.__result = None
        self.__condition_var_assignment_model = []

        for a in args:
            if not z3.is_bool(a):
                raise TypeError("Assumptions passed to check_conditional_constraints must be Bool expressions")

        count_limit = max_count if self.__multi_solver_mode else 1
        
        cache = self._ensure_cv_models(condition=condition, need=count_limit)
        entries = cache.entries[:count_limit]
        
        if not entries:
            raise RuntimeError("Not possible to find a CV assignment under global constraints.")
        
        first_result = None
        
        
        for entry in entries:
            assumptions = entry["cv_assumptions"] + list(args)

            # Do NOT record this check in history.
            res = self.check(*assumptions)
            if first_result is None:
                first_result = res

            assignment = entry["assignment"]
            if not z3.is_true(condition):
                # condition forced True; include it in the assignment dict if it is a CV
                if z3.is_bool(condition) and z3.is_const(condition):
                    assignment[condition.decl().name()] = True

            self.__condition_var_assignment_model.append(assignment)
            
            if self.__record_smt or self.__multi_solver_mode:
                smt2_str = self._build_snapshot_for_assumptions(assumptions=assumptions, result=res)

                solver_results = None
                if self.__multi_solver_mode:
                    solver_results = run_solvers.run_solvers(smt2_str=smt2_str, verbose=False)
                    if self.__result is None:
                        self.__result = res
                    elif res != self.__result:
                        warnings.warn(
                            "Results differ across CV assignments; conditional constraints may be inequivalent.\n"
                            "Suppress with InequivalentConditionalConstraints if intentional.\n",
                            InequivalentConditionalConstraints
                        )

                self.__runs.append(CVRun(
                    assignment=assignment,
                    smt2=smt2_str,
                    sat=res,
                    solver_results=solver_results if self.__multi_solver_mode else None,
                ))

                if not self.__canonical_smt_str:
                    self.__canonical_smt_str = smt2_str


        return first_result

    # ----------------------------
    # Runs/introspection
    # ----------------------------
    def get_runs(self) -> list[CVRun]:
        return list(self.__runs)

    def get_condition_var_assignment_model(self):
        return [r.assignment for r in self.__runs]

    def get_var_assignments_and_solvers_performance(self):
        return [
            {"assignment": r.assignment, "sat": str(r.sat), "solver_results": r.solver_results}
            for r in self.__runs
        ]

    # ----------------------------
    # SMT2 export helpers
    # ----------------------------
    def _emit_header(self, out: StringIO):
        out.write("(set-logic ALL)\n")
        for name in sorted(self.__decls):
            out.write(self.__decls[name] + "\n")

    def _emit_ops(self, out: StringIO, ops: List[Tuple[str, Any]]):
        for op, payload in ops:
            if op == "add":
                out.write(f"(assert {payload})\n")
            elif op == "push":
                out.write(f"(push 1)\n")
            elif op == "pop":
                out.write(f"(pop {payload})\n")
            elif op == "check":
                out.write("(check-sat)\n")
            elif op == "check_assuming":
                out.write(f"(check-sat-assuming ({' '.join(payload)}))\n")
            elif op == "result":
                out.write(f"; Result: {payload}\n")
            else:
                raise RuntimeError(f"Unknown history op: {op}")
    
    def _state_ops_only(self) -> List[Tuple[str, Any]]:
        """Return only state-mutating operations (no checks/results)."""
        return [(op, p) for (op, p) in self.__history if op in ("add", "push", "pop")]
    
    def _final_check_block_if_last(self) -> Optional[List[Tuple[str, Any]]]:
        """
        If the LAST recorded op is a check (check or check_assuming),
        return [that check op] plus any immediately following result comment(s).
        Otherwise return None.
        """
        if not self.__history:
            return None
        
        last_op, last_payload = self.__history[-1]
        if last_op not in ("check", "check_assuming"):
            return None
        
        block = [(last_op, last_payload)]
        
        return block
    
    def _final_check_and_results_block(self) -> Optional[List[Tuple[str, Any]]]:
        """
        Returns the final (check/check_assuming) plus its trailing result comment(s),
        but ONLY if that check is the final check in history AND there are no events
        after its result(s).

        Concretely, supports either tail shape:
          ... ("check_assuming", [...]), ("result", "sat")
          ... ("check", None), ("result", "unsat")

        If the history does not end with a result right after a check, returns None.
        """
        if not self.__history:
            return None
        
        # Typical case: history ends with ("result", ...)
        if self.__history[-1][0] == "result":
            # Scan backward to find the check that produced this result
            i = len(self.__history) - 1
            # collect all trailing results (usually exactly 1)
            results = []
            while i >= 0 and self.__history[i][0] == "result":
                results.append(self.__history[i])
                i -= 1
            if i >= 0 and self.__history[i][0] in ("check", "check_assuming"):
                check_evt = self.__history[i]
                # Return in forward order: check then results
                return [check_evt] + list(reversed(results))
            return None
        
        # Edge case: history ends with a check and no recorded result
        if self.__history[-1][0] in ("check", "check_assuming"):
            return [self.__history[-1]]
        
        return None
    
    def generate_smt2_snapshot(self) -> str:
        """
        Snapshot policy:
          - Replay declarations + all state ops (add/push/pop).
          - Include ONLY the final recorded user check if the session ends with that check (+ its results).
          - Otherwise append a final '(check-sat)' to make it runnable.
        """
        out = StringIO()
        self._emit_header(out)
        
        # 1) State-only ops
        self._emit_ops(out, self._state_ops_only())
        
        # 2) Final check only (if last events are check(+result))
        final_block = self._final_check_and_results_block()
        if final_block is not None:
            # Only include the last check (and its results), not any earlier checks.
            self._emit_ops(out, final_block)
        else:
            # Append a runnable final check
            out.write("(check-sat)\n")
        
        s = out.getvalue()
        out.close()
        return s
    
    def generate_smt2_transcript(self) -> str:
        """
        Transcript = declarations + full recorded history of user operations, including all user checks in order.
        Internal CV enumeration checks are excluded because they bypass the overridden check() and are not recorded.
        """
        out = StringIO()
        self._emit_header(out)
        self._emit_ops(out, self.__history)
        s = out.getvalue()
        out.close()
        return s

    def _build_snapshot_for_assumptions(self, assumptions: List[z3.BoolRef], result: Optional[z3.CheckSatResult] = None) -> str:
        """
        Build an SMT2 snapshot of current state + a single check-sat-assuming(assumptions).
        Does NOT modify __history. Used for CVRun smt2 output.
        """
        for a in assumptions:
            self._collect_decls(a)

        out = StringIO()
        self._emit_header(out)

        # Replay only state operations
        state_ops = [(op, p) for (op, p) in self.__history if op in ("add", "push", "pop")]
        self._emit_ops(out, state_ops)

        # Add the check line for these assumptions
        out.write(f"(check-sat-assuming ({' '.join(a.sexpr() for a in assumptions)}))\n")
        if result is not None:
            out.write(f"; Result: {result}\n")

        s = out.getvalue()
        out.close()
        return s

    # Backward-compatible API
    def generate_smtlib(self):
        # After check_conditional_constraints(), return canonical run SMT2.
        if self.__canonical_smt_str:
            return self.__canonical_smt_str
        return self.generate_smt2_snapshot()

    # Optional alias if you used to call to_smt2 elsewhere
    def to_smt2(self) -> str:
        if not self.__record_smt:
            return super().to_smt2()
        return self.generate_smt2_snapshot()



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
