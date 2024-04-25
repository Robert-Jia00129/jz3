import os
import subprocess
import time
import zipfile
from pathlib import Path
from typing import List, Hashable

from jz3.src.Sudokus import Sudoku

FULL_CONDITIONS = [(classic, distinct, percol, nonum, prefill)  # must be hashable
                   for classic in (True, False)
                   for distinct in (True, False)
                   for percol in (True, False)
                   for nonum in (True, False) if not (distinct and nonum)
                   for prefill in (True, False)]
assert isinstance(FULL_CONDITIONS[0], Hashable), "Conditions MUST be HASHABLE"
SOLVER_LIST = ("z3", "cvc5")


# Remember to reset the dict in curr_line_of_solving_full_sudokus.txt if the file exist


def write_file(condition_name, arr_time):
    file_path = condition_name + "-" + time.strftime("%Y_%m_%d_%H_%M_%S")
    with zipfile.ZipFile(f'../{file_path}.zip', 'w') as my_zip:
        files = os.listdir('ArgyleSudoku/Sudoku')
        for f in files:
            my_zip.write(f)
        with my_zip.open(f"{condition_name}.txt", "w") as new_hello:
            new_hello.write(bytes(f'{arr_time}', 'utf-8'))


def to_str(bool_list) -> str:
    if len(bool_list) == 6:
        return ''.join(("classic-" if bool_list[0] else "argyle-",
                        "distinct-" if bool_list[1] else "PbEq-",
                        "percol-" if bool_list[2] else "inorder-",
                        "is_bool-" if bool_list[3] else "is_num-",
                        "prefill-" if bool_list[4] else "no_prefill-",
                        "gen_time" if bool_list[5] else "solve_time"))
    if len(bool_list) == 5:
        return ''.join(("classic-" if bool_list[0] else "argyle-",
                        "distinct-" if bool_list[1] else "PbEq-",
                        "percol-" if bool_list[2] else "inorder-",
                        "is_bool-" if bool_list[3] else "is_num-",
                        "prefill-" if bool_list[4] else "no_prefill-"))


def to_bool(condition_str: str) -> list[bool]:
    condition_lst = condition_str.split('-')
    assert len(condition_lst) >= 4, "Cannot convert condition string"
    if len(condition_lst) == 4:
        return [True if condition_lst[0].lower() == "classic" else False,
                True if condition_lst[1].lower() == "distinct" else False,
                True if condition_lst[2].lower() == "percol" else False,
                True if condition_lst[3].lower() == "is_bool" else False,
                True if condition_lst[4].lower() == "prefill" else False,
                True if condition_lst[5].lower() == "gen_time" else False]
    pass

def generate_smt2_filename(problem_type, constraint):
    return f"{problem_type}-{constraint}-{time.time()}.smt2"

def save_smt2_file(smt2_str, filename, directory="problems_instances/whole_problem_records/smt2_files"):
    if not os.path.exists(directory):
        os.makedirs(directory)
    file_path = os.path.join(directory, filename)
    with open(file_path, 'w') as file:
        file.write(smt2_str)
    return file_path

def update_mapping(mapping_file_path, grid, constraint, smt2_file_path):
    mapping_dict = {
        "problem": {
            "grid": grid,
        },
        constraint: {
            "smt_path": smt2_file_path,
        }
    }


def run_experiment_once(single_condition: bool, *args,
                        start_condition: List[bool] = [],
                        start_from_next: bool = False,
                        curr_line_path: str = '../sudoku_database/curr_line_of_solving_full_sudokus.txt',
                        classic_full_path: str = '../sudoku_database/classic_full_sudokus.txt',
                        argyle_full_path: str = '../sudoku_database/argyle_full_sudokus.txt',
                        classic_holes_path: str = '../sudoku_database/classic_holes_sudokus.txt',
                        argyle_holes_path: str = '../sudoku_database/argyle_holes_sudokus.txt',
                        hard_sudoku_dir: str = "../../problems_instances/particular_hard_instances_records/txt_files/",
                        time_record_dir: str = '../time-record/whole_problem_time_records',
                        hard_smt_logPath: str = '',
                        verbose: bool = False):
    """
    Generate full sudokus and holes sudokus under different constraints and store the time to a specific location.

    Args:
        single_condition (bool): If True, only the start_condition is used. If False, all conditions are used.
        *args: Additional arguments passed to the function.
        start_condition (List[bool]): The starting condition. If empty, all conditions are used.
        start_from_next (bool): If True, starts from the next condition after start_condition.
        curr_line_path (str): Path to the file storing the current line of solving full sudokus.
        classic_full_path (str): Path to the file storing classic full sudokus.
        argyle_full_path (str): Path to the file storing argyle full sudokus.
        classic_holes_path (str): Path to the file storing classic holes sudokus.
        argyle_holes_path (str): Path to the file storing argyle holes sudokus.
        hard_sudoku_dir (str): Directory path for storing hard sudoku instances.
        time_record_dir (str): Directory path for storing time records.
        hard_smt_logPath (str): Path for storing hard SMT logs.
        verbose (bool): If True, prints verbose output.

    Returns:
        None
    """
    try:
        with open(curr_line_path, 'r') as f:
            curr_line = eval(f.readline())
    except IOError:
        curr_line = {}  # Keep track of which full sudoku to continue_reading with

    if single_condition:
        conditions = [start_condition]
    else:
        conditions = FULL_CONDITIONS
        if start_condition:
            conditions = conditions[conditions.index(tuple(start_condition)) + start_from_next:]

    seed = time.time()
    print(f'Generating full sudokus: \n'
          f'{"-" * len(conditions)}Total Conditions: {len(conditions)}')
    for condition in conditions:
        if condition[0]:
            full_sudoku_path = classic_full_path
            hard_sudoku_path = os.path.join(hard_sudoku_dir, 'hard_classic_instances.txt')
        else:
            full_sudoku_path = argyle_full_path
            hard_sudoku_path = os.path.join(hard_sudoku_dir, 'hard_argyle_instance.txt')

        condition_name = to_str(condition) + 'full_time'
        print('-', end="")

        full_time, full_penalty = Sudoku.gen_full_sudoku(*condition, hard_smt_logPath=hard_smt_logPath,
                                                         hard_sudoku_logPath=hard_sudoku_path,
                                                         store_sudoku_path=full_sudoku_path, seed=seed)
        with open(os.path.join(time_record_dir, condition_name + '.txt'), 'a') as f:
            os.makedirs(time_record_dir, exist_ok=True)
            f.write(f'{full_time},{full_penalty}\n')

    print("\nGenerating holes sudokus: \n"
          f'{"-" * len(conditions)}Total Conditions: {len(conditions)}')

    with open(classic_full_path, 'r') as f:
        if classic_full_path in curr_line:
            f.seek(curr_line[classic_full_path])
        classic_sudoku_lst = f.readline()[:-1]  # get rid of new line character
    classic_hard_sudoku_path = os.path.join(hard_sudoku_dir, 'hard_classic_instances.txt')

    with open(argyle_full_path, 'r') as f:
        if argyle_full_path in curr_line:
            f.seek(curr_line[argyle_full_path])
        argyle_sudoku_lst = f.readline()[:-1]  # get rid of new line character
    argyle_hard_sudoku_path = os.path.join(hard_sudoku_dir, 'hard_argyle_instance.txt')

    for condition in conditions:
        if condition[0]:
            sudoku_lst = classic_sudoku_lst
            holes_sudoku_path = classic_holes_path
            hard_sudoku_path = classic_hard_sudoku_path
        else:
            sudoku_lst = argyle_sudoku_lst
            holes_sudoku_path = argyle_holes_path
            hard_sudoku_path = argyle_hard_sudoku_path

        condition_name = to_str(condition) + 'holes_time'
        if verbose:
            print(f'Processing holes sudoku {condition_name}')
        print('-', end="")
        holes_time, holes_penalty = Sudoku.gen_holes_sudoku(eval(sudoku_lst), *condition,
                                                            hard_smt_logPath=hard_smt_logPath,
                                                            hard_sudoku_logPath=hard_sudoku_path,
                                                            store_sudoku_path=holes_sudoku_path, seed=seed)
        if verbose:
            print(f'\tTime taken: {holes_time}')
        with open(os.path.join(time_record_dir, condition_name + '.txt'), 'a+') as f_holes:
            f_holes.write(f'{holes_time},{holes_penalty}\n')

    par_dir = Path(curr_line_path).parent
    os.makedirs(par_dir, exist_ok=True)
    with open(curr_line_path, 'w') as f:
        f.truncate()
        f.write(str(curr_line))
    print("Ran experiment once")


def solve_with_z3(smt_log_file_path: str, time_out: int) -> (int, int, str):
    """
    :param smt_log_file_path:
    :param time_out: in seconds
    :return:
    """
    start_time = time.time()
    did_timeout = False
    try:
        result = subprocess.run(["z3", "-smt2", smt_log_file_path],
                                capture_output=True, text=True, timeout=time_out)
        combined_output = ((result.stdout if result.stdout is not None else "") +
                           (result.stderr if result.stderr is not None else ""))  # capture all output
    except subprocess.TimeoutExpired as exc:
        did_timeout = True
        result = exc
    ans = "timeout"
    end_time = time.time()

    if not did_timeout:
        if "unsat" in combined_output:
            ans = "unsat"
        elif "sat" in combined_output:
            ans = "sat"
        else:
            ans = "unknown"
    return (end_time - start_time, did_timeout, ans)


def solve_with_cvc5(smt_log_file_path: str, time_out: int) -> (int, int, str):
    start_time = time.time()
    did_timeout = False
    try:
        result = subprocess.run(["../../solvers/cvc5-macOS-arm64", smt_log_file_path, "--lang", "smt2"],
                                capture_output=True, text=True, timeout=time_out)
        combined_output = ((result.stdout if result.stdout is not None else "") +
                           (result.stderr if result.stderr is not None else ""))  # capture all output
    except subprocess.TimeoutExpired as exc:
        did_timeout = True
        combined_output = ((exc.stdout.decode('utf-8') if exc.stdout else "") +
                           (exc.stderr.decode('utf-8') if exc.stderr else ""))  # capture all output
    ans = "timeout"

    end_time = time.time()

    # TODO this might not work. maybe some outputs are not in "sat" or "unsat"??
    if not did_timeout:
        if "unsat" in combined_output:
            ans = "unsat"
        elif "sat" in combined_output:
            ans = "sat"
        else:
            ans = "unknown"
    return (end_time - start_time, did_timeout, ans)


def solve_with_yices(smt_log_file_path: str, time_out: int) -> (int, int, str):
    start_time = time.time()
    did_timeout = False
    try:
        result = subprocess.run(["yices", smt_log_file_path, "--lang", "smt2"],
                                capture_output=True, text=True, timeout=time_out)
        combined_output = ((result.stdout if result.stdout is not None else "") +
                           (result.stderr if result.stderr is not None else ""))  # capture all output
    except subprocess.TimeoutExpired as exc:
        did_timeout = True
        combined_output = ((exc.stdout.decode('utf-8') if exc.stdout else "") +
                           (exc.stderr.decode('utf-8') if exc.stderr else ""))  # capture all output
    ans = "timeout"

    end_time = time.time()

    # TODO this might not work. maybe some outputs are not in "sat" or "unsat"??
    if not did_timeout:
        if "unsat" in combined_output:
            ans = "unsat"
        elif "sat" in combined_output:
            ans = "sat"
        else:
            ans = "unknown"
    return end_time - start_time, did_timeout, ans


def solve_with_solver(solver_name: str, smt_file_path, time_out=5) -> (int, int, str):
    """
    solve an smt file with particular solver
    :param solver_name:
    :param smt_file_path:
    :return: (time, did_time_out)
    """
    if solver_name == 'z3':
        return solve_with_z3(smt_file_path, time_out=time_out)
    elif solver_name == 'cvc5':
        return solve_with_cvc5(smt_file_path, time_out=time_out)
    # Add more elif blocks for other solvers
    raise ValueError(f"Unknown solver: {solver_name}, please implement the corresponding code")


def load_and_alternative_solve_hard(hard_instances_txt_log_dir: str, is_classic: bool, num_iter: int,
                                    currline_path="curr_instance_line.txt", timeout=5,
                                    hard_smt_dir="../../problems_instances/particular_hard_instances_records/smt2_files/",
                                    time_record_dir:str=""):
    """
    Writes a dictionary with {problem: , cond_1_time: , cond_2_time: cond_3_time: cond_4_time: ...}
    Condition[0] MUST be TRUE when classic and FALSE when argyle
    :param file_path:
    :return: None
    """
    if not os.path.exists(hard_instances_txt_log_dir):
        print(f"Provided directory does not exist, creating new directory: {hard_instances_txt_log_dir}")
        os.makedirs(hard_instances_txt_log_dir)

    if is_classic:
        hard_instances_file_path = os.path.join(hard_instances_txt_log_dir, "hard_classic_instances.txt")
        store_comparison_file_path = os.path.join(time_record_dir,"classic_time.txt")
    else:
        hard_instances_file_path = os.path.join(hard_instances_txt_log_dir, "hard_argyle_instance.txt")
        store_comparison_file_path = os.path.join(time_record_dir,"argyle_time.txt")

    with open(hard_instances_file_path, 'r+') as fr:
        with open(currline_path, "r") as ftempr:
            argyle_and_classic_time_dict = ftempr.readline()
            if argyle_and_classic_time_dict == '':
                argyle_and_classic_time_dict = {"classic": 0, "argyle": 0, "seed": 40}
            else:
                argyle_and_classic_time_dict = eval(argyle_and_classic_time_dict)
        curr_line_num: int = argyle_and_classic_time_dict.get("classic" if is_classic else "argyle", 0)
        argyle_and_classic_time_dict[
            "classic" if is_classic else "argyle"] += curr_line_num + num_iter  # record read lines up till now

        # skip current line numbers
        for _ in range(curr_line_num):
            fr.readline()

        for _ in range(num_iter):
            line_to_solve = fr.readline().strip()
            if not line_to_solve:
                print("Not enough hard instances for experiment/Encountered an empty new line\n\n\n")
            store_result_dict = {}
            try:
                tgrid, tcondition, tindex, ttry_Val, tis_sat = line_to_solve.split("\t")
            except ValueError:
                continue
            tcondition = eval(tcondition)

            # store problem and smt path
            store_result_dict["problem"] = {
                "grid": tgrid,
                "index": eval(tindex),
                "try_Val": eval(ttry_Val),
                "is_sat": tis_sat == "sat"
            }
            seed = time.time()
            # solve with other conditions
            CorAconditions = [ele for ele in FULL_CONDITIONS if ele[0] == tcondition[0]]
            for CorAcondition in CorAconditions:
                if (CorAcondition) not in store_result_dict:
                    store_result_dict[CorAcondition] = {}  # initialize the dictionary
                if "smt_path" not in store_result_dict[CorAcondition]:
                    single_condition_smt_path = Sudoku.generate_smt_for_particular_instance(store_result_dict["problem"]["grid"],
                                                                                            CorAcondition,
                                                                                            store_result_dict["problem"]["index"],
                                                                                            store_result_dict["problem"]["try_Val"],
                                                                                            store_result_dict["problem"]["is_sat"],
                                                                                            smt_dir=hard_smt_dir,seed=seed)
                    store_result_dict[CorAcondition]["smt_path"] = single_condition_smt_path
                else:
                    single_condition_smt_path = store_result_dict["smt_path"]

                for SOLVER in SOLVER_LIST:
                    instances_lst = store_result_dict[CorAcondition].get(SOLVER, [])
                    instances_lst.append(solve_with_solver(SOLVER, single_condition_smt_path, time_out=timeout))
                    store_result_dict[CorAcondition][SOLVER] = instances_lst

            # write time dictionary to file
            with open(store_comparison_file_path, 'a+') as fw:
                fw.write(str(store_result_dict) + '\n')
        with open(currline_path, 'w') as fw:
            fw.truncate()
            fw.write(str(argyle_and_classic_time_dict))


def record_whole_problem_performance(num_iter: int=1,
                                     timeout=5,
                                     smt_log_dir="../../problems_instances/whole_problem_records/smt2_files/",
                                     time_record_dir: str = ""
                                     ):
    seed = time.time()

    time_record_whole_problem_dir = os.path.join(time_record_dir,"whole_problem_time_records")
    if not os.path.exists(time_record_whole_problem_dir):
        print(f"Provided directory does not exist, creating new directory: {time_record_whole_problem_dir}")
        os.makedirs(time_record_whole_problem_dir)
    store_time_comparison_path = os.path.join(time_record_whole_problem_dir,"time.txt")

    # Iterate through all possible condition combinations
    for _ in range(num_iter):
        store_result_dict = {}
        empty_list = [0 for i in range(9) for j in range(9)]

        store_result_dict["problem"] = {
            "grid": str(empty_list)
        }
        # iterate through possible combinations
        for condition in FULL_CONDITIONS:
            for single_condition in FULL_CONDITIONS:
                if single_condition not in store_result_dict:
                    store_result_dict[single_condition] = {}
                if "smt_path" not in store_result_dict[single_condition]:
                    # generate the smt file corresponding to the problem
                    s_full = Sudoku.Sudoku(empty_list,*condition,seed=seed)
                    single_condition_smt_path = s_full.gen_full_and_write_smt2_to_file(smt_dir=smt_log_dir) # write
                    store_result_dict[single_condition]["smt_path"] = single_condition_smt_path
                else:
                    single_condition_smt_path = store_result_dict[single_condition]["smt_path"]

                # launch multiple solvesr
                for SOLVER in SOLVER_LIST:
                    instances_lst = store_result_dict[single_condition].get(SOLVER, [])
                    instances_lst.append(solve_with_solver(SOLVER, single_condition_smt_path, time_out=timeout))
                    store_result_dict[single_condition][SOLVER] = instances_lst
                with open(store_time_comparison_path, 'a+') as fw:
                    fw.write(str(store_result_dict) + '\n')
    # TODO: @sj Cannot implement this for holes

            # Generate holes sudoku, to be implemented
            #
            # s_holes = Sudoku(s_full._nums, *condition, seed=seed)
            # smt_str_holes = s_holes.generate_holes_smt2(os.path.join(hard_smt_dir, f"holes_{to_str(condition)}.smt2"))
            #
            # # Record the performance of different solvers for generating holes sudoku
            # for SOLVER in SOLVER_LIST:
            #     holes_time, holes_timeout, holes_result = solve_with_solver(SOLVER, smt_str_holes, time_out=timeout)
            #     # Record the results
            #     # ...



if __name__ == '__main__':
    # dictionary of file paths to feed into `run_experiment`
    TIME_OUT = 5
    # dct = {"curr_line_path": '../../sudoku_database/curr_line_of_solving_full_sudokus.txt',
    #        "classic_full_path": '../../sudoku_database/classic_full_sudokus.txt',
    #        "argyle_full_path": '../../sudoku_database/argyle_full_sudokus.txt',
    #        "classic_holes_path": '../../sudoku_database/classic_holes_sudokus.txt',
    #        "argyle_holes_path": "../../sudoku_database/argyle_holes_sudokus.txt",
    #        "hard_sudoku_dir": "../../problems_instances/particular_hard_instances_records/txt_files/",
    #        "time_record_dir": '../../time-record/whole_problem_time_records/',
    #        "hard_smt_logPath": '../../problems_instances/particular_hard_instances_records/smt2_files/'}
    #
    # # # Left off with argyle-distinct-inorder-is_num-no_prefill-full_timeTotal
    # #
    # time_record_dir = "../../time-record/particular_hard_instance_time_record/"
    # currline_path = "../../problems_instances/particular_hard_instances_records/txt_files/curr_instance_line.txt"
    # hard_instances_txt_log_dir = "../../problems_instances/particular_hard_instances_records/txt_files/"
    # # load_and_alternative_solve(hard_instances_time_record_dir, is_classic=True, num_iter=10,
    # #                            currline_path=alternative_solve_curr_line_path, timeout=TIME_OUT)
    # load_and_alternative_solve_hard(hard_instances_txt_log_dir=hard_instances_txt_log_dir, time_record_dir=time_record_dir, is_classic=False, num_iter=1,
    #                                 currline_path=currline_path, timeout=TIME_OUT)
    record_whole_problem_performance(time_record_dir="../../time-record/",timeout=30)
    # for i in range(1):
    #     run_experiment_once(False,
    #                         **dct
    #                         )
    # run_experiment(single_condition=False, full_iter=20, holes_iter=20,
    #                total_time_per_condition=1 * 60 * 1000)
    # run_experiment(True, [False, False, True, True, True], run_full=True, run_holes=False, full_iter=1000,
    #                total_time_per_condition = 5 * 60 * 10000000)

    print("Process Complete")

# specify timeout for python subprocesses
# don't tell time limit
# record timeout despite the output.
# exceptions





# percentages of timeout
# stack the time for each constraint together, and use percentages

