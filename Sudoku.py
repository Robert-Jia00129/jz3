import itertools
import json
import os.path
import warnings

# import src.SMTs.SMTs as z3  # if this fails, run 'python -m pip install z3-solver'
import jz3 as z3
import numpy as np
import random
from copy import deepcopy
import time
from typing import *
from pathlib import Path
from jz3.src.z3_wrapper import Solver


# z3.set_param('parallel.enable',True)

class Sudoku:
    _grid = None  # Creating an empty matrix with None everywhere
    _solver = None  # The solver
    _valid_charset = set(
        [int(x) for x in range(0, 10)])  # Set of valid input chars that is could be placed in a position
    _classic = True
    _distinct = True
    _per_col = True
    _no_num = True
    _prefill = False
    _hard_smt_log_dir = None
    _hard_sudoku_logPath = None
    
    def __init__(self, sudoku_array: List[int], classic: bool, distinct: bool, per_col: bool, no_num: bool,
                 prefill: bool, seed=0, hard_smt_logPath="", hard_sudoku_logPath="", verbose=False,
                 distinct_digits=False,
                 heuristic_search_mode=False, benchmark_mode=True
                 ):
        """
        Only write a logFile when a path is provided
        Type hint for List[int] might not work
        :param sudoku_array:
        :param classic: classic or argyle sudoku
        :param distinct: encoding constraints using z3.Distinct() or z3.PbEq()
        :param per_col: start filling/removing the grid with number in per_col order:
            (start with the first index (0,0) and end at index (8,8))
            or not per_col order:
            (start filling the grid with number order. first filling in all the 1s, 2s, 3s...
            and end with the number 9)
        :param no_num: Encode the numbers with numberic representation (1-9) or
                boolean representation (val1, val2... val9): val2==True indicates the number is 2 at this index
        :param prefill: prefill the grid:
            per_col case: prefill the first row with 1-9 in random order
            not per_col case: prefill all the 1s with random numbers
        :param hard_smt_logPath:
        """
        # a 1-D sudoku_array
        self._solver = Solver()
        self._timeout = 5000
        self._incTimeOut = self._timeout
        self._solver.set("timeout", self._timeout)
        # self._solver.from_file("fileName")
        self._classic = classic
        self._distinct = distinct
        self._no_num = no_num
        self._per_col = per_col
        self._nums = [[0 for _ in range(9)] for _ in range(9)]
        self._hard_smt_log_dir = hard_smt_logPath
        self._hard_sudoku_logPath = hard_sudoku_logPath
        self._prefill = prefill
        self._penalty = 0
        self.condition_tpl = (self._classic, self._distinct, self._per_col, self._no_num, self._prefill)
        self._verbose = verbose
        self._bool_timeout = False
        self._seed = seed
        self._store_global = False
        self._global_solver = z3.Solver()
        
        self._distinctdigits = distinct_digits
        self._condition_var_distinct = z3.Bool('distinct')
        self._condition_var_pbeq = z3.Bool('pbeq')
        self._heuristic_search_mode = heuristic_search_mode
        self._heuristic_solver = Solver(benchmark_mode=benchmark_mode)
        self._heuristic_solver.add_global_constraints(z3.Or(self._condition_var_distinct, self._condition_var_pbeq))
        
        if seed == 0:
            print("WARNING: NO random seed was set for solver class. "
                  "This would cause experiments to be unreliable when compared in across constraints."
                  "If this is intentional, please ignore .")
        random.seed(seed)
        self._solver_operations = []  # Initialize operation logging
        
        # Create variables
        if self._distinctdigits:
            self._digit_sort = z3.DeclareSort("Digit")
            self._constants = [z3.Const(f"C{i}", self._digit_sort) for i in range(1, 10)]
            self._grid = [[z3.Const(f"cell_{r + 1}_{c + 1}", self._digit_sort) for c in range(9)] for r in range(9)]
        
        else:
            self._constants = [i for i in range(1, 10)]
            if not no_num:
                self._grid = [[z3.Int(f"cell_{r + 1}_{c + 1}") for c in range(9)] for r in range(9)]
            else:
                self._grid = [[[z3.Const(f"cell_{r + 1}_{c + 1}_{num + 1}", z3.BoolSort()) for num in range(9)]
                               for c in range(9)] for r in range(9)]
        
        assert (len(sudoku_array) == 81), f"Invalid sudoku string provided! length:{len(sudoku_array)}"
        self.load_numbers(sudoku_array[:81])
    
    def generate_smt2_file(self):
        return self._solver.generate_smtlib()
    
    def load_numbers(self, sudoku_array):
        """
        assign each number in sudoku_array to grid
        :param sudoku_array: np.matrix
        :return: None
        """
        for r in range(9):
            for c in range(9):
                x = sudoku_array[r * 9 + c]
                assert (x in self._valid_charset), "Invalid sudoku string provided! (invalid character \'{}\')".format(
                    x)
                if x != 0:
                    self._nums[r][c] = int(x)
    
    def load_constraints(self):
        digits = [self._grid[r][c] for c in range(9) for r in range(9)]  # digit
        rows = [self._grid[r] for r in range(9)]  # row 1-9
        cols = [[self._grid[r][c] for r in range(9)] for c in range(9)]  # col 1-9
        offset = list(itertools.product(range(0, 3), range(0, 3)))  # box 1st -9th
        boxes = []
        # Load existing numbers
        for r in range(9):
            for c in range(9):
                if self._nums[r][c] != 0:
                    if self._no_num:
                        self._solver.add(self._grid[r][c][self._nums[r][c] - 1])
                    else:
                        self._solver.add(self._grid[r][c] == int(self._nums[r][c]))
        
        for r in range(0, 9, 3):
            for c in range(0, 9, 3):
                boxes.append([self._grid[r + dy][c + dx] for dy, dx in offset])
        
        if self._no_num:
            # pbeq ONLY, no_num 3D grid
            [self._solver.add(z3.PbEq([(self._grid[i][j][k], 1) for k in range(9)], 1))
             for i in range(9) for j in range(9)]  # digit
            [self._solver.add(z3.PbEq([(self._grid[k][i][j], 1) for k in range(9)], 1))
             for i in range(9) for j in range(9)]  # Col distinct
            [self._solver.add(z3.PbEq([(self._grid[j][k][i], 1) for k in range(9)], 1))
             for i in range(9) for j in range(9)]  # Row distinct
            [self._solver.add(z3.PbEq([(box[k][j], 1) for k in range(9)], 1))
             for j in range(9) for box in boxes]  # box
        else:  # numbers  2D grid
            # Restrict digits in between 1-9
            # for digit in digits:
            #     self._solver.add(digit >= 1)
            #     self._solver.add(digit <= 9)
            for digit in digits:
                self._solver.add(z3.Or([digit == i for i in range(1, 10)]))
            if self._distinct:  # distinct, numbers 2D grid
                [self._solver.add(z3.Distinct(row)) for row in rows]  # rows
                [self._solver.add(z3.Distinct(row)) for row in cols]  # cols
                [self._solver.add(z3.Distinct(row)) for row in boxes]  # boxes
            else:  # pbeq, numbers, 2D grid
                [self._solver.add(z3.PbEq([(row[i] == k, 1) for i in range(9)], 1))
                 for k in range(1, 10) for row in rows]
                [self._solver.add(z3.PbEq([(row[i] == k, 1) for i in range(9)], 1))
                 for k in range(1, 10) for row in cols]
                [self._solver.add(z3.PbEq([(row[i] == k, 1) for i in range(9)], 1))
                 for k in range(1, 10) for row in boxes]
        # Argyle-----
        if not self._classic:
            argyle_hints = [[self._grid[r][r + 4] for r in range(4)]  # Major diagonal 1
                , [self._grid[r][r + 1] for r in range(8)]  # ??
                , [self._grid[r + 1][r] for r in range(8)]
                , [self._grid[r + 4][r] for r in range(4)]
                , [self._grid[r][-r - 5] for r in range(4)]
                , [self._grid[r][-r - 2] for r in range(8)]
                , [self._grid[r + 1][-r - 1] for r in range(8)]
                , [self._grid[r + 4][-r - 1] for r in range(4)]
                            ]
            if self._no_num:
                self._solver.add(
                    z3.And([z3.PbLe([(digit[k], 1) for digit in arg], 1) for arg in argyle_hints for k in range(9)]))
                pass
            else:
                if self._distinct:
                    self._solver.add(z3.And([z3.Distinct(arg) for arg in argyle_hints]))
                else:
                    self._solver.add(z3.And(
                        [z3.PbLe([(digit == k + 1, 1) for digit in arg], 1) for arg in argyle_hints for k in range(9)]))
    
    def conditional_check_solvable(self):
        self.load_constraints()
        return self._heuristic_solver.check_conditional_constraints()
    
    def new_solver(self):
        """
        Try checking index[i][j] == Tryval with alternative approach
        :param i:
        :param j:
        :param tryVal:
        :return:
        """
        s_new = Sudoku([c for r in self._nums for c in r], self._classic, False,
                       self._per_col, True, self._prefill, seed=4321)
        s_new._timeout = 0
        s_new._solver.set("timeout", 0)
        s_new.load_constraints()
        self._penalty += 1
        return s_new
    
    def check_condition(self, i, j, tryVal):
        start = time.time()
        res = self._solver.check(
            # self._grid[i][j][tryVal - 1] if self._no_num else self._grid[i][j] == self._constants[tryVal - 1])
            self._grid[i][j][tryVal - 1] if self._no_num else self._grid[i][j] == tryVal)
        end = time.time()
        if self._timeout == 0: return res
        if end - start < (self._timeout - 100) / 1000 and res == z3.unknown:
            raise 'Probably somebody hit ctrl-c, aborting'
        elif self._verbose and end - start > self._timeout / 10000 and res != z3.unknown:
            print('One check took more than 10% of timeout, but completed')
        return res
    
    def removable(self, i, j, test_num) -> (bool, int):
        """
        Testing one index by one index. How to use push and pop
        to test to whole grid without reloading constraints
        Test if test_num is unique and could be removed
        --Replacement: check_puzzle_solvable function

        :param test_num: 1-9
        :return: (removable: bool, penalty: int)
        """
        self._nums[i][j] = 0
        self.load_constraints()
        result = self.check_not_removable(i, j, test_num)  # try _nums[i][j] != test_num
        if result == z3.sat:
            return False, 0
        elif result == z3.unknown:
            print("A hard instance encountered when asserting not equals to the constarint^^")
            # Try solving with faster method
            result = self.new_solver().check_not_removable(i, j, test_num)
            
            if result == z3.unknown:
                raise f"Timeout happened twice when checking if {i} {j} {test_num} is removable"
            else:
                if self._verbose:
                    print(f'unsolvable problem checking removable was {result} for ({i},{j}) is {test_num}')
                self.write_to_smt_and_sudoku_file((i, j), test_num, str(result), False)
                return result != z3.sat, 1
        
        return True, 0
    
    def check_not_removable(self, i, j, tryVal):
        res = self._solver.check(
            (self._grid[i][j][tryVal - 1] == False) if self._no_num else (
                    self._grid[i][j] != self._constants[tryVal - 1]))
        return res
    
    def add_constaint(self, i, j, tryVal):
        self._nums[i][j] = int(tryVal)
        if self._no_num:
            constraint = self._grid[i][j][tryVal - 1]
        else:
            constraint = self._grid[i][j] == tryVal
        self._solver.add(constraint)
        self._solver_operations.append(("assert", str(constraint)))
    
    def add_not_equal_constraint(self, i, j, tryVal):
        self._solver.add(
            self._grid[i][j][tryVal - 1] == False if self._no_num else self._grid[i][j] != self._constants[tryVal - 1])
    
    def gen_full_sudoku(self):
        """
        produce a solved/FULL sudoku
        --Replacement: solving_sudoku function

        :return: 2D list of a solved FULL sudoku
        """
        self.load_constraints()
        if self._per_col:
            # Fill by index
            for i in range(9):
                # print(f"Filling row {i}")
                if i == 0 and self._prefill:
                    testlst = [k for k in range(1, 10)]
                    random.shuffle(testlst)
                for j in range(9):
                    if self._nums[i][j] != 0:
                        continue
                    if i == 0 and self._prefill:
                        tryVal = testlst.pop()
                        check = z3.sat
                    else:
                        x = [k for k in range(1, 10)]
                        random.shuffle(x)
                        tryVal = x.pop()
                        check = self.check_condition(i, j, tryVal)
                    while check != z3.sat:
                        if check is None:
                            raise "ERROR, check is not assigned properly"
                        if check == z3.unknown:
                            s_new = self.new_solver()
                            check = s_new.check_condition(i, j, tryVal)
                            
                            # Record to log path
                            if self._hard_smt_log_dir:
                                self.write_to_smt_and_sudoku_file((i, j), tryVal, str(check), True)
                            else:
                                print("TimeOut and a logPath is not provided")
                            
                            if check == z3.unknown:
                                raise 'Timeout happened twice, don\'t know how to continue!'
                            elif self._verbose:
                                print(f'unsolvable problem was {check} for ({i},{j}) is {tryVal}')
                        else:  # check == z3.unsat
                            assert (check == z3.unsat)
                            if len(x) == 0:
                                print(f'check: {check} {i},{j},{tryVal}')
                                print(f'Current row: {self._nums}')
                                raise 'Tried all values, no luck, check gen_solved_sudoku'
                            tryVal = x.pop()
                            check = self.check_condition(i, j, tryVal)
                    self._nums[i][j] = int(tryVal)
                    if self._no_num:
                        self._solver.add(self._grid[i][j][tryVal - 1])
                    else:
                        self._solver.add(self._grid[i][j] == self._constants[tryVal - 1])
                
                if self._verbose:
                    print(f'Finished with row {i} and filled \n {self._nums[i]}')
        else:  # not per_col
            # Start by filling the number 1,2,3...9
            for num in range(1, 10):
                if self._verbose:
                    print(f'Filling number {num}')
                if num == 9:
                    for r in range(9):
                        for c in range(9):
                            if self._nums[r][c] == 0:
                                self._nums[r][c] = int(num)
                                if self._no_num:
                                    self._solver.add(self._grid[r][c][num - 1])
                                else:
                                    self._solver.add(self._grid[r][c] == int(num))
                else:
                    cols = [i for i in range(9)]
                    for r in range(9):
                        random.shuffle(cols)
                        column_filled = False
                        for c in cols:
                            if self._nums[r][c] == 0:
                                condition = self.check_condition(r, c, num)
                                if condition == z3.sat:
                                    self.add_constaint(r, c, num)
                                    cols.remove(c)
                                    self._nums[r][c] = num
                                    column_filled = True
                                    break
                                else:
                                    if condition == z3.unknown:
                                        s_new = self.new_solver()
                                        check = s_new.check_condition(r, c, num)
                                        
                                        if self._hard_smt_log_dir:
                                            self.write_to_smt_and_sudoku_file((r, c), num, str(check), True)
                                        else:
                                            print("TimeOut and a logPath is not provided")
                                        
                                        if check == z3.unknown:
                                            raise 'Timeout happened twice, don\'t know how to continue!'
                                        elif self._verbose:
                                            print(f'unsolvable problem was {check} for ({r},{c}) is {num}')
                                        if check == z3.sat:
                                            self.add_constaint(r, c, num)
                                            # self._solver.add(condition)
                                            cols.remove(c)
                                            column_filled = True
                                            break
                            
                            elif self._nums[r][c] == num:
                                cols.remove(c)
                                break
                        if not column_filled:
                            print(f"There are no possible columns that number {num} could be filled. Check the grid: ")
                            print(self._nums)
                            raise "Error in generating fully solved sudokues"
                if self._verbose:
                    print(f'Grid after filling in {num} is: ')
                    print(self._nums)
        if self._verbose:
            print("Generated a solved/full sudoku")
            print(self._nums)
        return self._nums, self._penalty
    
    def gen_holes_sudoku(self, solved_sudoku: list[int], store_sudoku_path="", verbose=False):
        """
        Generates a Sudoku puzzle with holes from a solved Sudoku grid.

        :param solved_sudoku: 1D list of an already solved Sudoku grid
        :param store_sudoku_path: Path to store the generated Sudoku puzzle
        :param verbose: If True, prints additional information during the process
        :return: (time, penalty)
        """
        if verbose:
            print(f'Solving puzzle: ')
            print(solved_sudoku)
        
        st = time.time()
        penalty = 0
        sudoku_array = solved_sudoku.copy()
        for i in range(9):
            for j in range(9):
                # Create a new solver instance for each cell using keyword arguments
                solver = Sudoku(
                    sudoku_array=sudoku_array,
                    classic=self._classic,
                    distinct=self._distinct,
                    per_col=self._per_col,
                    no_num=self._no_num,
                    prefill=self._prefill,
                    seed=self._seed,
                    hard_smt_logPath=self._hard_smt_log_dir,
                    hard_sudoku_logPath=self._hard_sudoku_logPath,
                    verbose=False,
                    distinct_digits=self._distinctdigits
                )
                removable, temp_penalty = solver.removable(i, j, solved_sudoku[i * 9 + j])
                if removable:
                    sudoku_array[i * 9 + j] = 0
                penalty += temp_penalty
        
        et = time.time()
        time_rec = et - st
        
        if verbose:
            print('Successfully generated one puzzle')
            print(sudoku_array)
        
        return time_rec, penalty
    
    def gen_full_and_write_smt2_to_file(self, smt_dir):
        """
        return: generated smt2 file_path
        """
        nums, penalty = self.gen_full_sudoku()
        
        if self._verbose:
            if nums is not None:
                print("Sudoku solved successfully!")
                print("Solution:")
                for row in nums:
                    print(row)
            else:
                warnings.warn(
                    f"Unable to generate a full sudoku and the corresponding smt2 file, the current sudoku is: {self._nums}")
        file_name = f"sudoku_smt_{time.strftime('%m_%d_%H_%M_%S')}_{(str(time.time()).split('.')[1])[1:4]}.smt2"
        file_path = os.path.join(smt_dir, file_name)
        with open(file_path, 'w') as f:
            f.write(self._solver.generate_smtlib())
        if self._verbose:
            print(f"SMT2 file generated at : {file_path}")
        return file_path
    
    def write_to_smt_and_sudoku_file(self, pos, value, sat, assert_equals):
        """Write self._solver as a smt file to _log_path

        When reading the constraints:
        t = z3.Solver()
        t.from_file(_log_path)
        print(t, t.check())
        """
        # check directory exist
        if not os.path.exists(self._hard_smt_log_dir):
            os.makedirs(self._hard_smt_log_dir)
        
        par_dir = Path(self._hard_sudoku_logPath).parent
        if not os.path.exists(par_dir):
            os.makedirs(par_dir)
        
        time_str = time.strftime("%m_%d_%H_%M_%S") + (str(time.time()).split('.')[1])[
            1:4]  # making sure no repetition in file name
        
        # record as smt and txt files
        with open(self._hard_smt_log_dir + time_str, 'w') as myfile:
            print(self._solver.generate_smtlib(), file=myfile)
        
        sudoku_lst = ''.join(str(ele) for rows in self._nums for ele in rows)
        log_entry = {
            'grid': sudoku_lst,
            'condition_bool': self.condition_tpl,
            'index': pos,
            'try_Val': value,
            'assert_equals': assert_equals,
            'is_sat': sat
        }
        # record sudoku as string file
        with open(self._hard_sudoku_logPath, 'a+') as log_file:
            log_file.write(json.dumps(log_entry) + '\n')
    
    def generate_smt_with_additional_constraint(self, index: (int, int), try_val: int, is_sat: bool,
                                                assert_equals: bool,
                                                smt_dir: str) -> str:
        """
        Add an additional constraint to the Sudoku problem, generate an SMT file, and return the file path.

        :param index: Tuple (row, column) of the cell for the additional constraint.
        :param try_val: The value to assign or not assign at the given index.
        :param is_sat: If True, the cell at index should be try_val; if False, it should not be try_val.
        :param smt_dir: Directory to store the generated SMT file.
        :return: The path to the generated SMT file.
        """
        self.load_constraints()
        
        # Add the specific condition for the cell at 'index'
        i, j = index
        
        if assert_equals:
            self.add_constaint(i, j, try_val)
        else:
            self.add_not_equal_constraint(i, j, try_val)
        
        # Generate the file path for the SMT file
        file_name = f"sudoku_smt_{time.strftime('%m_%d_%H_%M_%S')}_{(str(time.time()).split('.')[1])[1:4]}.smt2"  # making sure that there is no file name conflicts
        file_path = os.path.join(smt_dir, file_name)
        
        # Write the SMT-LIB representation to the file
        with open(file_path, 'w') as smt_file:
            smt_file.write(self._solver.to_smt2())
        
        return file_path


def generate_puzzle(solved_sudokus, classic: bool, distinct: bool, per_col: bool, no_num: bool, prefill: bool, seed,
                    log_path="", verbose=False):
    """
    Generates puzzle with holes

    :param verbose:
    :param log_path:
    :param solved_sudokus: MUST BE a 3D list
    :param classic:
    :param distinct:
    :return: [[time_rec], [penalty_lst]] list of lists
    """
    time_rec = []
    penalty_lst = []
    for puzzle in solved_sudokus:
        if verbose:
            print(f'Solving puzzle: ')
            print(puzzle)
        st = time.time()
        penalty = 0
        for i in range(9):
            for j in range(9):
                s = Sudoku(puzzle.reshape(-1), classic, distinct, per_col, no_num, prefill, hard_smt_logPath=log_path,
                           seed=seed)
                removable, temp_penalty = s.removable(i, j, puzzle[i][j])
                if removable:
                    puzzle[i][j] = 0
                penalty += temp_penalty
        et = time.time()
        time_rec.append(et - st)
        penalty_lst.append(penalty)
        print('Successfully generated one puzzle')
    assert len(time_rec) == len(penalty_lst), "Bug in generate_puzzle"
    
    return time_rec, penalty_lst


def gen_solve_sudoku(classic: bool, distinct: bool, per_col: bool, no_num: bool, prefill: bool, seed, num_iter=1,
                     log_path="logFile"):
    '''
    First creates a solved sudoku, then generate a sudoku puzzle. returns time for each

    :param prefill:
    :param classic:
    :param distinct:
    :param per_col:
    :param no_num:
    :param num_iter:
    :return: (solve_time, solve_penalty, gen_time, gen_penalty) all are 1D lists
    '''
    ret_solve_time = []
    store_solved_sudoku = []
    solve_penalty = []
    for i in range(num_iter):
        empty_list = [0 for i in range(9) for j in range(9)]
        st = time.time()
        s = Sudoku(empty_list, classic, distinct, per_col, no_num, prefill, hard_smt_logPath=log_path, seed=seed)
        nums, penalty = s.gen_full_sudoku()
        et = time.time()
        store_solved_sudoku.append(nums)
        ret_solve_time.append(et - st)
        solve_penalty.append(penalty)
    # np.save('solved_sudoku', store_solved_sudoku)
    store_holes = deepcopy(store_solved_sudoku)
    store_holes = np.array(store_holes)
    print("Start generating puzzles")
    ret_holes_time, holes_penalty = generate_puzzle(store_holes, classic, distinct, per_col, no_num, prefill, seed=seed)
    assert len(ret_solve_time) == len(solve_penalty), "error in gen_solve_sudoku"
    return ret_solve_time, solve_penalty, ret_holes_time, holes_penalty


def append_list_to_file(file_path, lst: list[int]):
    if not file_path:
        return
    par_dir = Path(file_path).parent
    if not os.path.exists(par_dir):
        os.makedirs(par_dir)
    with open(file_path, 'a+') as f:
        f.write(str(lst) + "\n")


def gen_full_sudoku(*constraints, seed, hard_smt_logPath='smt2_files/', store_sudoku_path="",
                    hard_sudoku_logPath="") -> Tuple[float, int, List[List[int]]]:
    """
    setup empty grid. Call Sudoku.gen_full_sudoku().
    append generated full sudoku to the designated path as a string

    :param hard_smt_log_path:
    :param constraints: classic, distinct, percol, no_num, prefill
    :param store_sudoku_path:
    :return: (time, penalty, sudoku_grid)
    """
    empty_list = [0 for i in range(9) for j in range(9)]
    st = time.time()
    s = Sudoku(empty_list, *constraints, hard_smt_logPath=hard_smt_logPath, hard_sudoku_logPath=hard_sudoku_logPath,
               seed=seed)
    nums, penalty = s.gen_full_sudoku()
    smt2 = s._solver.generate_smt2_transcript()
    with open('./no_wrapper.smt2', 'w') as f:
        f.write(smt2)
    et = time.time()
    # Write to file
    append_list_to_file(store_sudoku_path, sum(nums, []))  # flatten 2D nums into 1D
    return et - st, penalty, nums


def gen_holes_sudoku(solved_sudoku: list[int], *constraints, seed, hard_smt_log_dir='smt2_files/', store_sudoku_path="",
                     hard_sudoku_logPath="", verbose=False):
    # TODO: Code dupication
    """
    Reads sudokus as a string from store_sudoku_path
    :param solved_sudoku: 1D list of an already solved sudoku grid
    :param hard_instances_log_path:
    :param constraints: classic, distinct, percol, no_num, prefill
    :param store_sudoku_path:
    :return: (time, penalty)
    """
    if verbose:
        print(f'Solving puzzle: ')
        print(solved_sudoku)
    st = time.time()
    penalty = 0
    for i in range(9):
        for j in range(9):
            s = Sudoku(solved_sudoku, *constraints, hard_smt_logPath=hard_smt_log_dir,
                       hard_sudoku_logPath=hard_sudoku_logPath, seed=seed)
            removable, temp_penalty = s.removable(i, j, solved_sudoku[i * 9 + j])
            if removable:
                solved_sudoku[i * 9 + j] = 0
            penalty += temp_penalty
    et = time.time()
    time_rec = et - st
    
    if verbose:
        print('Successfully generated one puzzle')
        print(solved_sudoku)
    # np.save('sudoku_puzzle', solved_sudokus)
    append_list_to_file(store_sudoku_path, solved_sudoku)
    return time_rec, penalty


def check_condition_index(sudoku_grid: list[int], condition, index: (int, int), try_val: int, is_sat: str,
                          seed: float) -> (int, int):
    """
    """
    s = Sudoku(sudoku_grid, *condition, seed=seed)
    s.load_constraints()
    start = time.time()
    penalty = 0
    if is_sat:
        if z3.unknown == s.check_condition(index[0], index[1], try_val):
            penalty = 1
    
    else:
        if z3.unknown == s.check_not_removable(index[0], index[1], try_val):
            penalty = 1
    end = time.time()
    return end - start, penalty


def generate_smt_for_particular_instance(grid: str, constraint: list, index: (int, int), try_val: int, is_sat: bool,
                                         assert_equals: bool, smt_dir: str, seed=0) -> str:
    """
    Add an additional constraint to the Sudoku problem, generate an SMT file, and return the file path.
    :param index: Tuple (row, column) of the cell for the additional constraint.
    :param try_val: The value to assign or not assign at the given index.
    :param is_sat: If True, the cell at index should be try_val; if False, it should not be try_val.
    :param smt_dir: Directory to store the generated SMT file.
    :return: The path to the generated SMT file.
    """
    solver = Sudoku(list(map(int, (grid))), *constraint, seed=seed)
    file_path = solver.generate_smt_with_additional_constraint(index, try_val, is_sat, assert_equals, smt_dir)
    
    return file_path


def sudoku_conditional_constraints_test():
    # Create an empty Sudoku grid
    empty_grid = [0] * 81
    
    # Create an instance of the Sudoku class
    sudoku = Sudoku(empty_grid, classic=True, distinct=True, per_col=True, no_num=False, prefill=True, seed=1234,
                    distinct_digits=False, benchmark_mode=True, heuristic_search_mode=True)
    
    # Load the constraints
    sudoku.load_constraints()
    
    # Check if the first index can be equal to 1
    result = sudoku._heuristic_solver.check_conditional_constraints(sudoku._grid[0][0] == z3.Int(1))
    print(f"Can the first index be equal to 1? {result}")
    
    # Access the recorded combinations and performance results
    print("Condition Variable Assignment Models:")
    models = sudoku._heuristic_solver.get_condition_var_assignment_model()
    for i, model in enumerate(models):
        print(f"Model {i + 1}:")
        print(model)


def pure_constraints(classic: bool, distinct: bool, per_col: bool, no_num: bool, prefill: bool, seed, num_iter=1,
                     log_path="logFile"):
    empty_list = [0 for i in range(9) for j in range(9)]
    s = Sudoku(empty_list, classic, distinct, per_col, no_num, prefill, hard_smt_logPath=log_path, seed=seed)
    result = s.generate_smt2_file()
    with open('./output.smt2', 'w') as f:
        f.write(result)


def load_grid_and_check() -> None:
    """
    Add an additional constraint to the Sudoku problem, generate an SMT file, and return the file path.

    :param index: Tuple (row, column) of the cell for the additional constraint.
    :param try_val: The value to assign or not assign at the given index.
    :param is_sat: If True, the cell at index should be try_val; if False, it should not be try_val.
    :param smt_dir: Directory to store the generated SMT file.
    :return: The path to the generated SMT file.
    """
    sudoku_str = "200300100100000200000201000000002001020010000010000020002000010001020000000100002"
    sudoku_array = list(map(int, sudoku_str))
    i = 1
    j = 7
    tryVal = 3
    print(sudoku_array)
    
    # # pbeq case
    s = Sudoku(sudoku_array, classic=False, distinct=False, per_col=False, no_num=False, prefill=False, seed=40)
    
    # # distinct case
    # s = Sudoku(sudoku_array, classic=False, distinct=True, per_col=False, no_num=False, prefill=False, seed=40)
    s.load_constraints()
    
    print(s.check_condition(i, j, tryVal))  # unsat
    m = s._solver.model()
    for i in range(9):
        for j in range(9):
            print(m.eval(s._grid[i][j]), end="")
            if j % 3 == 2:
                print("|", end="")
        print("")
        if i % 3 == 2:
            print("-----------")
    return


if __name__ == "__main__":
    # Test classic case
    # classic, distinct, per_col, no_num
    condition = (True, True, True, False, True)
    kwargs = {
        # 'num_iter': 100,
        # 'log_path': 'tmp/',
        'seed': 42,
    }
    print(gen_full_sudoku(*condition, **kwargs)) # (0.11754703521728516, ...)
    
    # # pure_constraints(classic=True, distinct=False, per_col=True, no_num=False, prefill=True, num_iter=2,seed=4321)
    # print(gen_solve_sudoku(*condition, **kwargs, num_iter=5))
    #
    # # sudoku_conditional_constraints_test()
    # load_grid_and_check()
    
    print("Process finished")
