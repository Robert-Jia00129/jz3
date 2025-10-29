import jz3 as z3

# Initialize a solver instance
solver = z3.Solver(benchmark_mode=True)

# Create an integer variable to represent time
x = z3.Int('x')

# Create condition variables for two different encodings
condition1 = z3.Bool('encoding1')
condition2 = z3.Bool('encoding2')

# Define the first encoding: Time `x` between 8 and 17 but not equal to 12
solver.add_conditional_constraint(z3.And(8 <= x, x <= 17, x != 12), condition=condition1)

# Define the second encoding: Time `x` is either between 8 and 12, or between 12 and 17, excluding 12 itself
solver.add_conditional_constraint(
    z3.Or(z3.And(8 <= x, x < 12), z3.And(12 < x, x <= 17)),
    condition=condition2
)

# Ensure the two encoding styles are distinct
solver.add_global_constraints(z3.Or(condition1, condition2))
solver.add_global_constraints(z3.Distinct(condition1, condition2))

# Start recording and solve the problem
solver.start_recording()
result = solver.check_conditional_constraints()

# Display recorded combinations and performance results
print("Condition Variable Assignment Models:")
print(solver.get_condition_var_assignment_model())
print("Solvers Results for each variable assignment:")
print(solver.get_var_assignments_and_solvers_performance())