import z3

x = z3.Int('x')
y = z3.Int('y')

s = z3.Solver()

s.add(x > 0)
print(s.to_smt2())
# def func(*args, **kwargs):
#     print(args)
print(s.check(x == 2, x <= 1))
print(s.to_smt2())
