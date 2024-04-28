from io import StringIO
import z3
import jz3.src.run_solvers as run_solvers
import warnings


# child class to write push and pop to SMT2 file
class Solver(z3.Solver):
    def __init__(self, benchmark_mode=False, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.__start_recording = False
        self.__history = []
        self.__assertions = []
        self.__global_constraints = z3.BoolVal(True)
        self.__smt_str = ""
        self.__condition_var_assignment_model = None
        self.__latest_solvers_results = None
        self.__benchmark_mode = benchmark_mode
        self.__variables = set()

    def __getattribute__(self, name):
        _allowed_methods = ['add', 'add_global_constraints', 'add_conditional_constraint',
                            'check_conditional_constraints', 'check', 'push', 'pop',
                            'start_recording', 'generate_smtlib', '_allowed_methods',
                            'ctx', 'solver', 'set', 'assert_exprs', 'to_smt2', 'assertions',
                            'get_condition_var_assignment_model',
                            'get_latest_solvers_results']
        if name.startswith('_') or name in _allowed_methods:  # intentionally accessing a private variable
            return object.__getattribute__(self, name)
        else:
            warnings.warn(f"Method '{name}' is called.\n "
                          f"But this method might not be recorded to smt2 file and might incur potential logic errors"
                          f"Please use only the methods defined in Solver2SMT.\n"
                          f"If this is intentional, modified the _allowed_methods above")
            return super().__getattribute__(name)

    def add_global_constraints(self, *constraints):
        """
        Sets global constraints that encodes rules/constraints for the condition variables.
        :param constraints: A list of Z3 constraints that define global conditions.
        """
        self.__global_constraints = z3.And(self.__global_constraints, *constraints)

    def add(self, *args):
        # self._conditional_constraints.append((args,condition))
        if self.__start_recording:
            for arg in args:
                self.__history.append(("add", str(arg.sexpr())))
        super().add(*args)

    def add_conditional_constraint(self, *args, condition=z3.BoolVal(True)):
        if condition is None:
            condition = z3.BoolVal(True)
        for conditional_constraint in args:
            self.__assertions.append((conditional_constraint, condition))
            self.__variables.add(condition)
        s = z3.Solver()
        s.add(self.__global_constraints)

        if s.check() != z3.sat:
            raise "There is no way to satisfy all condition variables provided under global constraint"

    def check_conditional_constraints(self, *args, condition=z3.BoolVal(True),max_count=5):
        s = z3.Solver()  # no smt file recording required
        s.add(self.__global_constraints)

        # temporarily add the constraint and conditional constraint to be checked.
        if args:  # append the checked condition
            self.__assertions.append((args, condition))

        if s.check() == z3.sat:
            # possible combination of condition variables
            model = s.model()

            solver_with_conditional_constraint = Solver()

            # add corresponding conditional constraints and try to solve
            for (conditional_constraint, condition) in self.__assertions:
                if condition == z3.BoolVal(True) or model.eval(condition):
                    if self.__start_recording:
                        self.__history.append(("add", str(conditional_constraint.sexpr())))
                    solver_with_conditional_constraint.add(conditional_constraint)

            # Don't really record the smt files
            solver_with_conditional_constraint.start_recording()
            result = solver_with_conditional_constraint.check()

            self.__condition_var_assignment_model = [model]

            # Only launch multiple solvers when in benchmark mode
            if self.__benchmark_mode:
                self.__condition_var_assignment_model = []
                self.__latest_solvers_results = []

                # find different combinations
                opt = z3.Optimize()
                opt.add(self.__global_constraints)
                dist = 1
                count = 0
                while (count < max_count) and (dist > 0):
                    solver_with_conditional_constraint = Solver()

                    # add corresponding conditional constraints and try to solve
                    for (conditional_constraint, condition) in self.__assertions:
                        if model.eval(condition):
                            if self.__start_recording:
                                self.__history.append(("add", str(conditional_constraint.sexpr())))
                            solver_with_conditional_constraint.add(conditional_constraint)

                    # append the combination to the results
                    # solver_with_conditional_constraint.start_recording()
                    result = solver_with_conditional_constraint.check()
                    self.__latest_solvers_results.append(run_solvers.run_solvers("conditional_constraints.smt2"))
                    self.__condition_var_assignment_model.append(model)
                    min_hamdist = z3.Int("min_hamdist")

                    opt.add(min_hamdist <= z3.Sum(
                        tuple(z3.If((var == bool(model[var])), 0, 1) for var in self.__variables)))
                    # opt.add(min_hamdist <= z3.Sum([0,1,0,1]))

                    opt.maximize(min_hamdist)
                    opt.check()
                    model = opt.model()
                    dist = model[min_hamdist].as_long()
                    count += 1

                # store smt file/str
                self.__smt_str = solver_with_conditional_constraint.generate_smtlib()

                with open("conditional_constraints.smt2", "w") as file:
                    file.write(self.__smt_str)

                # launch multiple solvers and store resutls

            # pop the temporarily added conditional constraints
            if args:
                self.__assertions.pop()

            if self.__start_recording:
                self.__history.append(("result", str(solver_with_conditional_constraint.check(*args))))
            return result
        else:
            raise ("Impossible to find any way of building constraints"
                   "The conditional constraints are not satisfiable under global constraints ")

    def push(self):
        if self.__start_recording:
            self.__history.append(("push", None))
        super().push()

    def pop(self, *args, **kwargs):
        if self.__start_recording:
            self.__history.append(("pop", None))
        super().pop(*args, **kwargs)

    def check(self, *args, **kwargs):
        result = None
        if self.__start_recording:
            if args:
                for arg in args:
                    # Format the args in SMT-LIB syntax
                    self.__history.append(("push", ""))
                    self.__history.append(("add", str(arg.sexpr())))
                    self.__history.append(("check", ""))
                    result = super().check(*args)
                    self.__history.append(("result", result))
                    self.__history.append(("pop", ""))
            else:
                self.__history.append(("check", ""))
                result = super().check(*args)
                self.__history.append(("result", result))
            return result
        else:
            return super().check(*args)

    def start_recording(self):
        self.__start_recording = True
        self.check()
        initial_state = self.to_smt2()
        # Remove the last "(check-sat)" from the initial state
        initial_state = initial_state.rsplit("(check-sat)", 1)[0]
        self.__history.append(("initial_state", initial_state))

    def generate_smtlib(self):
        output = StringIO()
        output.write(f"(set-logic QF_LIA)\n")
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

        smt_str = output.getvalue()
        output.close()
        return smt_str

    def get_condition_var_assignment_model(self):
        return self.__condition_var_assignment_model

    def get_latest_solvers_results(self):
        return self.__latest_solvers_results


def simple_test():
    solver = Solver(benchmark_mode=True)

    x = z3.Int('x')
    y = z3.Int('y')

    solver.add(x > 0)
    solver.add(y > 0)

    condition1 = z3.Bool('condition1')
    condition2 = z3.Bool('condition2')

    solver.add_global_constraints(z3.Or(condition1, condition2))

    solver.add_conditional_constraint(x < 5, condition=condition1)
    solver.add_conditional_constraint(x > 5, condition=condition2)

    solver.start_recording()
    result = solver.check_conditional_constraints()
    print(result)

    # Access the recorded combinations and performance results
    print("Condition Variable Assignment Models:")
    print(solver.get_condition_var_assignment_model())
    print("Latest Solvers Results:")
    print(solver.get_latest_solvers_results())


def optimizer_test():
    # Create variables
    x = z3.Int('x')
    y = z3.Int('y')
    z = z3.Int('z')

    # Create conditions
    cond1 = z3.Bool('cond1')
    cond2 = z3.Bool('cond2')
    cond3 = z3.Bool('cond3')

    # Create constraints
    constraints = [
        z3.Implies(cond1, x > 0),
        z3.Implies(cond2, y > 0),
        z3.Implies(cond3, z > 0)
    ]

    # Create optimizer
    opt = z3.Optimize()

    # Add constraints to the optimizer
    for constraint in constraints:
        opt.add(constraint)

    # Add conditions to the optimizer
    opt.add(z3.Or(cond1, cond2, cond3))

    # First combination (maximize)
    opt.push()
    opt.maximize(z3.Sum([z3.If(cond, 1, 0) for cond in [cond1, cond2, cond3]]))
    opt.check()
    combination1 = opt.model()
    opt.pop()

    # Second combination (minimize)
    opt.push()
    opt.minimize(z3.Sum([z3.If(cond, 1, 0) for cond in [cond1, cond2, cond3]]))
    combination2 = opt.model()
    opt.pop()

    # Print the combinations
    print("Combination 1:")
    print(combination1)
    print("Combination 2:")
    print(combination2)


if __name__ == '__main__':
    # simple_test()
    optimizer_test()
