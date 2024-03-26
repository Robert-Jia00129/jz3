from z3 import *


s = Solver()
x = Bool('x')
y = Bool('y')

s.add(And([x,Not(y)]))
s.add(Or([x,y]))
s.check()
print(s.model())