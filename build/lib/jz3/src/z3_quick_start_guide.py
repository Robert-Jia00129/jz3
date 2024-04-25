from src.z3_wrapper import Solver2SMT
# Create solver instance
s = Solver2SMT.Solver()
# Define variables
x = Solver2SMT.Int('x')
y =Solver2SMT. Int('y')
# Add constraints
s.add(x > 2, y < 10, x + 2*y == 7)
if s.check() == Solver2SMT.sat: # checking constraints sat
    print(s.model()) # [y = 0, x = 7]
else:
    print("No solution")
