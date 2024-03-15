import z3
from z3 import *

class Solver2SMT(z3.Solver):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._start_recording = False
        self._history = []

    def add(self, *args, **kwargs):
        if self._start_recording:
            for arg in args:
                self._history.append(("add", str(arg.sexpr())))
        super().add(*args, **kwargs)

    def push(self, *args, **kwargs):
        if self._start_recording:
            self._history.append(("push", None))
        super().push(*args, **kwargs)

    def pop(self, *args, **kwargs):
        if self._start_recording:
            self._history.append(("pop", None))
        super().pop(*args, **kwargs)

    def check(self, *args, **kwargs):
        if self._start_recording:
            self._history.append(("check", args))
            result = super().check(*args, **kwargs)
            self._history.append(("result", result))
            return result
        else:
            return super().check(*args, **kwargs)

    def start_recording(self):
        self._start_recording = True
        initial_state = self.to_smt2()
        # Remove the last "(check-sat)" from the initial state
        initial_state = initial_state.rsplit("(check-sat)", 1)[0].strip()
        self._history.append(("initial_state", initial_state))

    def generate_smtlib(self, filename):
        with open(filename, "w") as file:
            for operation in self._history:
                op, args = operation
                if op == "initial_state":
                    file.write(args)
                elif op == "add":
                    file.write(f"(assert {args})\n")
                elif op in ["push", "pop"]:
                    file.write(f"({op} 1)\n")
                elif op == "check":
                    file.write(f"(check-sat)\n")
                elif op == "result":
                    file.write(f"; Result: {args}\n")

if __name__ == '__main__':
    s = Solver2SMT()
    x = Int('x')
    y = Int('y')
    s.add(x > 10, y == x + 2)
    s.start_recording()
    s.push()
    s.add((x < 10))
    s.check()
    s.pop()
    s.check()

    smt_str = s.to_smt2()
    # with open('correct-smt.txt','w') as f:
    #     f.write(smt_str)

    s.generate_smtlib('my-smt.txt')