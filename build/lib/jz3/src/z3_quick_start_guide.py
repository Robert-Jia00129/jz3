import jz3 as z3
# Create solver instance
s = z3.Solver()
# Define variables
x = z3.Int('x')
y =z3. Int('y')
# Add constraints
s.add(x > 2, y < 10, x + 2*y == 7)
if s.check() == z3.sat: # checking constraints sat
    print(s.model()) # [y = 0, x = 7]
else:
    print("No solution")
