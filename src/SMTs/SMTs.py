import z3

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


class BoolVal(Expression):
    def __init__(self, value):
        self.value = value

    def predicates(self):
        return {}

    def compute(self, _values):
        return self.value

    def z3(self):
        return z3.BoolVal(self.value)

class Expression(ABC):
    """Abstract base class for all expressions."""

    @abstractmethod
    def get_predicate_name(self):
        """Returns the variable(s) name(s)."""
        pass

    @abstractmethod
    def to_z3_expr(self):
        """Convert to z3 expression."""
        pass

    @abstractmethod
    def evaluate_assigned_value(self, value_dct):
        """return the assigned value for this variable/predicate in value_dct"""
        pass


class Bool(Expression):
    """Represents a boolean variable."""

    def __init__(self, name):
        self.name = name

    def get_predicate_name(self):
        return self.name

    def to_z3_expr(self):
        return z3.Bool(self.name)

    def evaluate_assigned_value(self, value_dct):
        return value_dct[self.name]


class Int(Expression):
    """Represents an integer variable."""

    def __init__(self, name):
        self.name = name

    def get_predicate_name(self):
        return self.name

    def to_z3_expr(self):
        return z3.Int(self.name)

    def evaluate_assigned_value(self, value_dct):
        return value_dct[self.name]


class Not(Expression):
    """Represents a logical NOT operation."""

    def __init__(self, arg):
        self.arg = arg

    def get_predicate_name(self):
        return self.arg.get_predicate_name()

    def to_z3_expr(self):
        return z3.Not(self.arg.to_z3_expr())

    def evaluate_assigned_value(self, value_dct):
        return not self.arg.evaluate_assigned_value(value_dct)


class Or(Expression):
    """Represents a logical OR operation between multiple expressions."""

    def __init__(self, *args):
        self.args = args

    def get_predicate_name(self):
        return set.union(*(arg.get_predicate_name() for arg in self.args))

    def to_z3_expr(self):
        return z3.Or([arg.to_z3_expr() for arg in self.args])

    def evaluate_assigned_value(self, value_dct):
        return any(arg.evaluate_assigned_value(value_dct) for arg in self.args)


class And(Expression):
    """Represents a logical OR operation between multiple expressions."""

    def __init__(self, *args):
        self.args = args

    def get_predicate_name(self):
        return set.union(*(arg.get_predicate_name() for arg in self.args))

    def to_z3_expr(self):
        return z3.And([arg.to_z3_expr() for arg in self.args])

    def evaluate_assigned_value(self, value_dct):
        return all(arg.evaluate_assigned_value(value_dct) for arg in self.args)





class Distinct(Expression):
    """Represents a distinct constraint on a set of expressions."""

    def __init__(self, *args):
        self.args = args

    def get_predicate_name(self):
        pass

    def to_z3_expr(self):
        return z3.Distinct([arg.to_z3_expr() for arg in self.args])

    def evaluate_assigned_value(self, value_dct):
        pass


# PbEq implementation would depend on the specific requirements for pseudo-boolean equality.
# Here's a placeholder for its structure:
class PbEq(Expression):
    """Placeholder for a pseudo-boolean equality operation."""

    def __init__(self, *args, equals):
        self.args = args
        self.equals = equals

    def get_predicate_name(self):
        # Implementation depends on specifics of PbEq.
        pass

    def to_z3_expr(self):
        # Implementation depends on specifics of PbEq.
        pass

    def evaluate_assigned_value(self, value_dct):
        pass


class Const(Expression):
    """Represents a constant value."""
    def __init__(self, value):
        self.value = value

    def get_predicate_name(self):
        # Constants do not have a variable name, return an empty set
        return set()

    def to_z3_expr(self):
        # Directly return the constant value as its Z3 expression equivalent
        return z3.Const(self.value)

    def evaluate_assigned_value(self, value_dct):
        # The evaluation of a constant is the constant itself
        return self.value




class Const:
    ...

    def z3(self):
        pass
        # return z3.Const(..)


def true():
    return BoolVal(True)


def false():
    return BoolVal(False)


class Solver:
    def __init__(self):
        self.assertions = []
        self.modelVariables = {}  # no_num, distinct, etc
        self.modelConstraints = true()  # no_num and distinct cannot be true at the same time

    def add(self, *args, constraint: Expression=None):
        if constraint is None:
            constraint = true()
        for assertion in args:
            # TODO: check the the constraints are validly typed
            # (it's better to get the error here rather than upon 'check'
            self.assertions.append((assertion, constraint))

    def check(self, condition=None):
        if condition is None:
            condition = true()

        def makeTF(v):
            if v:
                return True
            else:
                return False

        s = z3.Solver()
        res = s.check(self.modelConstraints.z3())
        if res == z3.sat:
            model = s.model()

            modelValues = {var: makeTF(model[var]) for var in self.modelVariables}
            s.add()
            # todo: launch multiple solvers in parallel, get first response
            # also, use modelValues and z3.Optimize() to make the second solver
            # as different from the first as possible
            s = z3.Solver()
            for (assertion, constraint) in self.assertions:
                if constraint.evaluate_assigned_value(modelValues):
                    s.add(assertion.z3())
            return s.check(condition.z3())  # todo: convert z3s answer to ours
        else:
            raise "Impossible to find any way of building constraints"


sat = "sat"
unsat = "unsat"
timeout = "timeout"
unknown = "unknown"

if __name__ == '__main__':
    s = Solver()
    s.add(Or(Bool("x"), Bool("y")), Eq(Bool("x"), Bool("y")))
    s.add(Implies(Bool("x"), Bool("y")), Bool("redundant_implies"))
    if s.check() == sat:
        m = s.model()
        assert (m['x'])
        assert (m['y'])
        print('test passed')
    else:
        print('something is very wrong')
