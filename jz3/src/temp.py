from z3 import *

# 1. Define variables and a solver instance
a, b, c = Ints("a b c")
s = Solver()
s.add(5 * a + 4 * b - 3 * c == 0)
s.add(a > 0, b > 0, c > 0) # Add constraints to ensure a 'sat' result

# 2. Check for satisfiability and get the model
if s.check() == sat:
    m = s.model()
    print(f"Model: {m}")

    # 3. Use m.decls() to get all declarations in the model
    print("\nDeclarations in the model:")
    for decl in m.decls():
        # Get the name of the declaration (variable name as a string)
        decl_name = decl.name()
        # Get the interpreted value of the declaration in the model
        decl_value = m[decl]
        print(f"* Variable name: {decl_name}, Value: {decl_value}. Type: {decl.kind() == z3.Z3_OP_UNINTERPRETED}")
else:
    print("Solver did not find a solution.")
