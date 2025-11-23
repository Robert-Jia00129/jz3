import subprocess
import time
import os
import sys
from pathlib import Path
import warnings

class SMTFileErrorWarning(UserWarning):
    pass

def run_cvc5(smt2_file, time_out: int = 5):
    if sys.platform == "darwin":  # macOS
        cvc_path = get_executable_path("cvc5-macOS-arm64")
    elif sys.platform == "linux":  # linux
        cvc_path = get_executable_path("cvc5-linux-x86")
    else:
        raise NotImplementedError(f"{sys.platform} is not currently supported")
    command = [cvc_path, smt2_file, "--lang", "smt2"]
    start_time = time.time()
    did_timeout = False
    try:
        result = subprocess.run(command,
                                capture_output=True, text=True, timeout=time_out)
        combined_output = ((result.stdout if result.stdout is not None else "") +
                           (result.stderr if result.stderr is not None else ""))  # capture all output
    except subprocess.TimeoutExpired as exc:
        did_timeout = True
        combined_output = ((exc.stdout.decode('utf-8') if exc.stdout else "") +
                           (exc.stderr.decode('utf-8') if exc.stderr else ""))  # capture all output
    ans = "timeout"

    end_time = time.time()
    total_time = end_time - start_time
    if not did_timeout:
        if "unsat" in combined_output:
            ans = "unsat"
        elif "sat" in combined_output:
            ans = "sat"
        elif "error" in combined_output.lower() or "unsupported" in combined_output.lower():
            ans = "error"
            warning_message = f"CVC5 encountered an error while processing {smt2_file}:\n{combined_output}"
            warnings.warn(warning_message, SMTFileErrorWarning)
        else:
            ans = "unknown"
    else:
        total_time = time_out
    return (total_time, did_timeout, ans)


def run_z3(smt2_file: str, time_out: int = 5):
    """
    :param smt_log_file_path:
    :param time_out: in seconds
    :return:
    """
    start_time = time.time()
    did_timeout = False
    try:
        result = subprocess.run(["z3", "-smt2", smt2_file],
                                capture_output=True, text=True, timeout=time_out)
        combined_output = ((result.stdout if result.stdout is not None else "") +
                           (result.stderr if result.stderr is not None else ""))  # capture all output
        # print(f'z3 std output: {result.stdout}'
        #       f'z3 stderr output: {result.stderr}')
    except subprocess.TimeoutExpired as exc:
        did_timeout = True
        combined_output = ''
        result = exc
    return shared_code("Z3",start_time,did_timeout,combined_output,smt2_file,time_out)
def shared_code(solvername,start_time,did_timeout,combined_output,smt2_file,time_out):
    ans = "timeout"
    end_time = time.time()
    total_time = end_time - start_time
    if not did_timeout:
        if "unsat" in combined_output:
            ans = "unsat"
        elif "sat" in combined_output:
            ans = "sat"
        elif "error" in combined_output.lower() or "unsupported" in combined_output.lower():
            ans = "error"
            warning_message = f"{solvername} encountered an error while processing {smt2_file}:\n{combined_output}"
            warnings.warn(warning_message, SMTFileErrorWarning)
        else:
            ans = "unknown"
    else:
        total_time = time_out
    return total_time, did_timeout, ans


def run_yices(smt2_file):
    command = f"yices-smt2 {smt2_file}"
    try:
        result = subprocess.run(command, shell=True, capture_output=True, text=True, check=True)
        return result.stdout.strip()
    except subprocess.CalledProcessError as e:
        return f"Error: {e}"


# Dictionary to map solver names to their corresponding functions
solvers = {
    "cvc5": run_cvc5,
    "z3": run_z3
    # "yices": run_yices
}


def run_solvers(smt2_file:str='', smt2_str:str='', verbose=False, time_out=5, solvers = solvers):
    """
    time_out: in seconds
    solver: user defined dict that's similar to "solver", and they can call shared_func to define their own
    """
    results = {}
    if smt2_str and smt2_file=='':
        smt2_file = os.path.join(os.path.dirname(__file__), 'smt_file.smt2')
        with open(smt2_file, 'w') as f:
            f.truncate()
            f.write(smt2_str)

    for solver, run_function in solvers.items():
        if verbose:
            print(f"Running {solver}...")
        result = run_function(smt2_file,time_out=time_out)
        results[solver] = result

    return results


def get_executable_path(solver_path_in_solvers_dir):
    # Get the directory of the current file (__file__ refers to the script in which this code is written)
    dir_of_jz3 = Path(os.path.dirname(__file__)).parent

    # Build the path to the executable
    executable_path = os.path.join(dir_of_jz3, "solvers/" + solver_path_in_solvers_dir)

    return executable_path


if __name__ == '__main__':
    print(run_cvc5(
        '/Users/jiazhenghao/Desktop/CodingProjects/jz3/jz3/problems_instances/particular_hard_instances_records/smt2_files/04_25_00_58_021714024682.151314'))
