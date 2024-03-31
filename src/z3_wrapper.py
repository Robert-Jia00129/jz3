from io import StringIO
import z3
import run_solvers


# child class to write push and pop to SMT2 file
class Solver2SMT(z3.Solver):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._start_recording = False
        self._history = []
        self.assertions = []
        self.global_constraints = z3.BoolVal(True)
        self.smt_str = ""
        self.condition_var_assignment_model = None
        self.latest_solvers_results = None

    def add_global_constraints(self, *constraints):
        """
        Sets global constraints that encodes rules/constraints for the condition variables.
        :param constraints: A list of Z3 constraints that define global conditions.
        """
        self.global_constraints = z3.And(self.global_constraints, *constraints)

    def add(self, *args):
        # self._conditional_constraints.append((args,condition))
        if self._start_recording:
            for arg in args:
                self._history.append(("add", str(arg.sexpr())))
        super().add(*args)
        self.add_global_constraints(*args)

    def add_conditional_constraint(self, *args, condition=z3.BoolVal(True)):
        if condition is None:
            condition = z3.BoolVal(True)
        for conditional_constraint in args:
            self.assertions.append((conditional_constraint, condition))
        s = z3.Solver()
        s.add(self.global_constraints)
        for _, condition in self.assertions:
            s.add(condition)
        if s.check() != z3.sat:
            raise "There is no way to satisfy all condition variables provided under global constraint"

    def check_conditional_constraints(self, *args, condition=z3.BoolVal(True)):
        s = z3.Solver() # no smt file recording required
        s.add(self.global_constraints)

        # temporarily add the constraint and conditional constraint to be checked.
        self.assertions.append((args,condition))
        conditional_expressions = [cond for (_, cond) in self.assertions]
        for expr in conditional_expressions:
            s.add(expr)


        if s.check() == z3.sat:
            # possible combination of condition variables
            model = s.model()

            # solve under s.model() and record the smt file
            solver_with_conditional_constraint = Solver2SMT()
            # TODO, not really necessary, believe I can remove this @sj
            solver_with_conditional_constraint.add_global_constraints(self.global_constraints)

            # add corresponding conditional constraints and try to solve
            for (conditional_constraint, condition) in self.assertions:
                if condition == z3.BoolVal(True) or model.eval(condition):
                    if self._start_recording:
                        self._history.append(("add", str(conditional_constraint.sexpr())))
                    solver_with_conditional_constraint.add(conditional_constraint)

            # Don't really record the smt files
            solver_with_conditional_constraint.start_recording()
            result = solver_with_conditional_constraint.check()

            # store smt file/str
            self.smt_str = solver_with_conditional_constraint.generate_smtlib("conditional_constraints.smt2")
            # TODO: don't necessarily need to write to file, might need it in the future
            # with open("conditional_constraints.smt2", "w") as file:
            #     file.write(self.smt_str)
            self.condition_var_assignment_model = model

            # launch multiple solvers and store resutls
            self.latest_solvers_results = run_solvers.run_solvers("conditional_constraints.smt2")

            # pop the temporarily added conditional constraints
            self.assertions.pop()

            if self._start_recording:
                self._history.append(("result", str(solver_with_conditional_constraint.check(*args))))
            return result
        else:
            raise ("Impossible to find any way of building constraints"
                   "The conditional constraints are not satisfiable under global constraints ")


    def push(self, *args, **kwargs):
        if self._start_recording:
            self._history.append(("push", None))
        super().push(*args, **kwargs)

    def pop(self, *args, **kwargs):
        if self._start_recording:
            self._history.append(("pop", None))
        super().pop(*args, **kwargs)

    def check(self, *args, **kwargs):
        if self._start_recording:
            if args:
                for arg in args:
                # Format the args in SMT-LIB syntax
                    self._history.append(("push", ""))
                    self._history.append(("add", str(arg.sexpr())))
                    self._history.append(("check", ""))
                    result = super().check(*args)
                    self._history.append(("result", result))
                    self._history.append(("pop", ""))
            else:
                self._history.append(("check", ""))
                result = super().check(*args)
                self._history.append(("result", result))
            return result
        else:
            return super().check(*args)

    def start_recording(self):
        self._start_recording = True
        initial_state = self.to_smt2()
        # Remove the last "(check-sat)" from the initial state
        initial_state = initial_state.rsplit("(check-sat)", 1)[0]
        self._history.append(("initial_state", initial_state))

    def generate_smtlib(self, filename):
        output = StringIO()
        output.write(f"(set-logic QF_LIA)\n")
        for operation in self._history:
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

        smt_str = output.getvalue()
        output.close()
        return smt_str
