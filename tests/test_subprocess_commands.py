import subprocess
import time

smt_file_path = "/Users/jiazhenghao/Desktop/CodingProjects/ArgyleSudoku/Sudoku/smt-logFiles/09_28_00_27_101695878830.7237408"
time_out = 3
# result = subprocess.run(["./cvc5-macOS-arm64", smt_file_path, "--lang", "smt2", "--tlimit","1000"],capture_output=True,text=True)
result = subprocess.run(["z3", "-smt2", smt_file_path, f"-T:{time_out}"],capture_output=True,text=True)


print(result)
print("STDOUT")
print(result.stdout)
print("STDERR")
print(result.stderr)
combined_output = result.stdout + result.stderr
print("timeout" in combined_output)

