# found a way to avoid these: just create a super class
## Functions that the classes share:
# obj.z3():
#   get the z3 version of the formula obj (to hand to the z3 solver)
# obj.compute(dict):
#   get a true/false value based on obj by looking up the variables in dict
# obj.predicates():
#   get the set of predicates occurring in obj
from abc import ABC, abstractmethod
import z3
from typing import Tuple, Dict, List


class Expression(ABC):
    """Abstract base class for all expressions."""

    @abstractmethod
    def get_predicate_name(self):
        """Returns the variable(s) name(s). involved in the expression"""
        pass

    @abstractmethod
    def to_z3_expr(self):
        """Convert to z3 expression."""
        pass

    @abstractmethod
    def evaluate_assigned_value(self, value_dct):
        """return the assigned value for this variable/predicate in value_dct"""
        pass


class BoolVal(Expression):
    def __init__(self, value):
        self.value = value

    def get_predicate_name(self):
        return {}

    def evaluate_assigned_value(self, _values):
        return self.value

    def to_z3_expr(self):
        return z3.BoolVal(self.value)


class Bool(Expression):
    """Wrapper for boolean variable."""

    def __init__(self, name):
        self.name = name

    def get_predicate_name(self):
        return self.name

    def to_z3_expr(self):
        return z3.Bool(self.name)

    def evaluate_assigned_value(self, value_dct):
        return value_dct[self.name]


class Int(Expression):
    """Wrapper for integer variable."""

    def __init__(self, name):
        self.name = name

    def get_predicate_name(self):
        return self.name

    def to_z3_expr(self):
        return z3.Int(self.name)

    def evaluate_assigned_value(self, value_dct):
        return value_dct[self.name]


class Not(Expression):
    """Wrapper for logical NOT operation."""

    def __init__(self, *args):
        self.args = args

    def get_predicate_name(self):
        names = set()
        for arg in self.args:
            names.update(*arg.get_predicate_name())
        return names

    def to_z3_expr(self):
        return z3.Not(self.arg.to_z3_expr())

    def evaluate_assigned_value(self, value_dct):
        return not self.arg.evaluate_assigned_value(value_dct)


class Or(Expression):
    """Wrapper for logical OR operation between multiple expressions."""

    def __init__(self, *args):
        self.args = args

    def get_predicate_name(self):
        names = set()
        for arg in self.args:
            names.update(*arg.get_predicate_name())
        return names

    def to_z3_expr(self):
        return z3.Or([arg.to_z3_expr() for arg in self.args])

    def evaluate_assigned_value(self, value_dct):
        return any(arg.evaluate_assigned_value(value_dct) for arg in self.args)


class And(Expression):
    """Wrapper for logical AND operation between multiple expressions."""

    def __init__(self, *args):
        self.args = args

    def get_predicate_name(self):
        names = set()
        for arg in self.args:
            names.update(*arg.get_predicate_name())
        return names

    def to_z3_expr(self):
        for arg in self.args:
            print(arg)
        return z3.And([arg.to_z3_expr() for arg in self.args])

    def evaluate_assigned_value(self, value_dct):
        return all(arg.evaluate_assigned_value(value_dct) for arg in self.args)


class Distinct(Expression):
    """...."""

    def __init__(self, *args):
        self.args = args

    def get_predicate_name(self):
        names = set()
        for arg in self.args:
            names.update(*arg.get_predicate_name())
        return names

    def to_z3_expr(self):
        return z3.Distinct([arg.to_z3_expr() for arg in self.args])

    def evaluate_assigned_value(self, value_dct):
        all_predicates = [arg.evaluate_assigned_value(value_dct) for arg in self.args]
        return len(set(all_predicates)) == len(all_predicates)



class PbEq(Expression):
    """...."""

    def __init__(self, expr_weights: List[Tuple[Expression, int]], equal_val: int):
        self.expr_weights = expr_weights
        self.equal_val = equal_val


    def get_predicate_name(self):
        # Implementation depends on specifics of PbEq.
        names = set()
        for name,_ in self.expr_weights:
            names.update(name.get_predicate_name())
        return names

    def to_z3_expr(self):
        # Implementation depends on specifics of PbEq.
        return z3.PbEq(self.expr_weights,self.equal_val)

    def evaluate_assigned_value(self, value_dct):
        sum_values = sum(expr.evaluate_assigned_value(value_dct) * weight for expr, weight in self.expr_weights)
        return sum_values==self.equal_val


class Const(Expression):
    """Wrapper for constant value."""

    def __init__(self, value):
        self.value = value

    def get_predicate_name(self):
        return set()

    def to_z3_expr(self):
        # Directly return the constant value as its Z3 expression equivalent
        return z3.Const(self.value)

    def evaluate_assigned_value(self, value_dct):
        # The evaluation of a constant is the constant itself
        return self.value


class Eq(Expression):

    def __init__(self, expr1, expr2):
        self.expr1 = expr1
        self.expr2 = expr2

    def get_predicate_name(self):
        return (self.expr1, self.expr2)

    def to_z3_expr(self):
        return z3.eq(self.expr1.to_z3_expr(), self.expr2.to_z3_expr())

    def evaluate_assigned_value(self, value_dct):
        return value_dct[self.expr1] == value_dct[self.expr2]

class PbLe(Expression):
    """...."""

    def __init__(self, expr_weights: List[Tuple[Expression, int]], equal_val: int):
        self.expr_weights = expr_weights
        self.equal_val = equal_val


    def get_predicate_name(self):
        # Implementation depends on specifics of PbEq.
        names = set()
        for name,_ in self.expr_weights:
            names.update(name.get_predicate_name())
        return names

    def to_z3_expr(self):
        # Implementation depends on specifics of PbEq.
        return z3.PbEq(self.expr_weights,self.equal_val)

    def evaluate_assigned_value(self, value_dct):
        sum_values = sum(expr.evaluate_assigned_value(value_dct) * weight for expr, weight in self.expr_weights)
        return sum_values<=self.equal_val

class Implies(Expression):
    """Represents a logical implication between two expressions."""

    def __init__(self, premise, conclusion):
        self.premise = premise
        self.conclusion = conclusion

    def get_predicate_name(self):
        return self.premise.get_predicate_name(), self.conclusion.get_predicate_name()

    def to_z3_expr(self):
        return z3.Implies(self.premise.to_z3_expr(), self.conclusion.to_z3_expr())

    def evaluate_assigned_value(self, value_dct):
        return not self.premise.evaluate_assigned_value(value_dct) or self.conclusion.evaluate_assigned_value(value_dct)


def true():
    return BoolVal(True)


def false():
    return BoolVal(False)


class Solver:
    def __init__(self):
        self.assertions: List[Tuple[Expression, Expression]] = []  # (conditional_constraint, condition)
        self.modelVariables = {}  # no_num, distinct, etc
        self.global_constraints = true()  # no_num and distinct cannot be true at the same time
        self.model = None

    def add(self, *args, condition: Expression = None) -> None:
        """
        Adds an expression as a constraint to the solver, optionally conditioned on another expression.

        Parameters:
            expression (Expression): The constraint to be added.
            condition (Expression, optional): The condition under which the constraint is applied.
        """

        if condition is None:
            condition = true()
        for conditional_constraint in args:
            # TODO: check the the constraints are validly typed @sj is this what you mean?
            self.assertions.append((conditional_constraint, condition))
        s = z3.Solver()
        s.add(self.global_constraints.to_z3_expr())
        for _, condition in self.assertions:
            # Check if the condition is an instance of your Expression class
            # and convert it to a Z3 expression if so. Otherwise, use it as is.
            if isinstance(condition, Expression):
                z3_condition = condition.to_z3_expr()
            else:
                z3_condition = condition
            s.add(z3_condition)
        if s.check() != z3.sat:
            raise "The conditions provided are not satisfiable"

    def check(self, *args, condition: Expression = true()):
        """
        Finds a satisfiable set of conditional variables that satisfies the global constraints
        and an optional specific condition. It then applies corresponding constraints based on this set
        and checks for overall satisfiability.

        """
        s = z3.Solver()
        s.add(self.global_constraints.to_z3_expr())
        # unconditional constraint

        # adding all conditions to solver to determine if they
        # can satisfy the global constraint
        conditional_expressions = [cond.to_z3_expr() for (_, cond) in self.assertions]
        for expr in conditional_expressions:
            s.add(expr)

        if s.check() == z3.sat:
            # find a specific combination
            model = s.model()  # [cond1==True, cond2==False, cond3==False, ...]

            solver_with_conditional_constraint = z3.Solver()
            modelValues = {}
            # todo: launch multiple solvers in parallel, get first response

            # {var: makeTF(model[var]) for var in self.modelVariables}
            # assignment dict of condition:True/False: z3.z3.BoolRef
            self.assertions: List[Expression, Expression]
            for (conditional_constraint, condition) in self.assertions:
                # for unconditional conditions, or conditions that we assign to be true
                if condition == BoolVal(True) or model.eval(condition.to_z3_expr()):
                    # modelValues[condition] = BoolVal(True)
                    solver_with_conditional_constraint.add(conditional_constraint.to_z3_expr())
            solver_with_conditional_constraint.check()
            self.model = solver_with_conditional_constraint.model()
            return solver_with_conditional_constraint.check(*args)  # todo convert z3.sat to ours???? @sj, this would impact the current program using z3.sat tho

        else:
            raise "Impossible to find any way of building constraints"

    def model(self):
        return self.model()


sat = "sat"
unsat = "unsat"
timeout = "timeout"
unknown = "unknown"

def my_test():
    solver = Solver()
    # Adding unconditional constraints
    solver.add(Bool("x"), condition=BoolVal(True))  # Unconditionally true
    solver.add(Bool("y"), condition=BoolVal(True))  # Unconditionally true

    # Should be satisfiable without additional conditions
    result = solver.check()
    assert result==z3.sat


if __name__ == '__main__':
    s = Solver()
    # s.add(Or(Bool("x"), Bool("y")), Eq(Bool("x"), Bool("y")))
    s.add(Or(Bool("x"), Bool("y")))
    s.add(Implies(Bool("x"), Bool("y")), Bool("redundant_implies"))
    if s.check() == z3.sat:
        m = s.model
        print(m)
        # assert (m['x'])
        # assert (m['y'])
        print('test passed')
    else:
        print('something is very wrong')
    my_test()


