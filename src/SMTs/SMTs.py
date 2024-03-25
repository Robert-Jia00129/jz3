import z3

# found a way to avoid these: just create a super class
## Functions that the classes share:
# obj.z3():
#   get the z3 version of the formula obj (to hand to the z3 solver)
# obj.compute(dict):
#   get a true/false value based on obj by looking up the variables in dict
# obj.predicates():
#   get the set of predicates occurring in obj


class Expression:
    def get_predicate_name(self):
        """Returns the variable(s) name(s)."""
        pass

    def to_z3_expr(self):
        """conver to z3 expression"""

    def evaluate_assigned_value(self,value_dct):
        """Assign/evaluate the variable from the value assigned in value_dct"""
        pass
class Bool:
    def __init__(self, name):
        self.name = name
    def predicates(self):
        return {self.name}
    def z3(self):
        return z3.Bool(self.name)
    def compute(self, values):
        return values[self.name]

class BoolVal:
    def __init__(self,value):
        self.value = value
    def predicates(self):
        return {}
    def compute(self, _values):
        return self.value
    def z3(self):
        return z3.BoolVal(self.value)

class Const:
    ...
    def z3(self):
        return z3.Const(..)


def true():
    return BoolVal(True)


def false():
    return BoolVal(False)


class Solver:
    def __init__(self):
        self.assertions = []
        self.modelVariables = {} # no_num, distinct, etc
        self.modelConstraints = true() # no_num and distinct cannot be true at the same time
    def add(self, *args, constraint=None):
        if constraint is None:
            constraint = true()
        for assertion in args:
            # TODO: check the the constraints are validly typed
            # (it's better to get the error here rather than upon 'check'
            self.assertions.append((assertion, constraint))

    def check(self, condition = None):
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

            modelValues = {var:makeTF(model[var]) for var in self.modelVariables}
            s.add()
            # todo: launch multiple solvers in parallel, get first response
            # also, use modelValues and z3.Optimize() to make the second solver
            # as different from the first as possible
            s = z3.Solver()
            for (assertion,constraint) in self.assertions:
                if constraint.compute(modelValues):
                    s.add(assertion.z3())
            return s.check(condition.z3()) # todo: convert z3s answer to ours
        else:
            raise "Impossible to find any way of building constraints"
sat = "sat"
unsat = "unsat"
timeout = "timeout"
unknown = "unknown"

if __name__ == '__main__':
    s = Solver()
    s.add(Or(Bool("x"),Bool("y")),Eq(Bool("x"),Bool("y")))
    s.add(Implies(Bool("x"),Bool("y")), Bool("redundant_implies"))
    if s.check()==sat:
        m = s.model()
        assert(m['x'])
        assert(m['y'])
        print('test passed')
    else:
        print('something is very wrong')
