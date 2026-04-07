import itertools
import json
import os
import random
import time
from copy import deepcopy
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import jz3 as z3
from jz3.src.z3_wrapper import Solver

# G
# DB.
# (bool, distinct)
class Sudoku:
    _valid_charset = set(range(0, 10))

    def __init__(
        self,
        sudoku_array: List[int],
        classic: bool = True,
        distinct: Optional[bool] = True,   # only used when no_num=False; if None, allow both arith variants
        per_col: bool = True,
        no_num: bool = False,
        prefill: bool = False,
        *,
        seed: int = 0,
        timeout_ms: int = 5000,
        max_count: int = 3,
        benchmark_mode: bool = True,
        record_smt: bool = False,
        verbose: bool = False,
        hard_smt_log_dir: str = "",
        hard_sudoku_log_path: str = "",
    ):
        """
        classic: keep for API parity; this refactor supports classic-only constraints for now.
        distinct: arithmetic encoding choice when no_num=False:
            - True  => arith_distinct fixed
            - False => arith_pbeq fixed
            - None  => do not fix; allow jz3 to enumerate both arith variants (benchmarking use)
        per_col/prefill: generation heuristic knobs (not CVs).
        no_num: representation selector (True => bool one-hot; False => arithmetic Int cells).
        max_count: passed to check_conditional_constraints.
        """
        assert classic is True, "This refactor currently supports classic Sudoku only."
        assert len(sudoku_array) == 81, f"Invalid sudoku length: {len(sudoku_array)} (expected 81)"
        assert max_count >= 1

        self._classic = classic
        self._distinct = distinct
        self._per_col = per_col
        self._no_num = no_num
        self._prefill = prefill
        self._seed = seed
        self._timeout_ms = timeout_ms
        self._max_count = max_count
        self._verbose = verbose

        self._hard_smt_log_dir = hard_smt_log_dir
        self._hard_sudoku_log_path = hard_sudoku_log_path

        random.seed(seed)

        # Base puzzle numbers (0 means empty)
        self._nums: List[List[int]] = [[0 for _ in range(9)] for _ in range(9)]
        self.load_numbers(sudoku_array[:81])

        # Conditional solver
        self._solver = Solver(benchmark_mode=benchmark_mode, record_smt=record_smt)
        self._solver.set("timeout", timeout_ms)

        # --- CVs (atomic) ---
        # Building blocks (straightforward names for UI/DB)
        self.cv_bool = z3.Bool("bool")
        self.cv_arith = z3.Bool("arith")
        self.cv_distinct = z3.Bool("distinct")
        self.cv_pbeq = z3.Bool("pbeq")

        # Composed variants (atomic)
        self.cv_arith_distinct = z3.Bool("arith_distinct")
        self.cv_arith_pbeq = z3.Bool("arith_pbeq")
        self.cv_bool_pbeq = z3.Bool("bool_pbeq")

        # Link CVs
        self._add_global_cv_constraints()

        # --- Variables for both representations ---
        # Arithmetic grid: Int
        self.A = [[z3.Int(f"cell_{r+1}_{c+1}") for c in range(9)] for r in range(9)]
        # Boolean one-hot grid
        self.B = [[[z3.Bool(f"cell_{r+1}_{c+1}_{d+1}") for d in range(9)] for c in range(9)] for r in range(9)]

        # Fixed variant for generation/checks
        self._fixed_variant_cv = self._select_fixed_variant_cv()

        # Constraints are loaded once
        self._constraints_loaded = False

        # Generation bookkeeping
        self._penalty = 0

    # -------------------------
    # CV setup
    # -------------------------

    def _add_global_cv_constraints(self) -> None:
        v_ad = self.cv_arith_distinct
        v_ap = self.cv_arith_pbeq
        v_bp = self.cv_bool_pbeq

        arith = self.cv_arith
        boo = self.cv_bool
        distinct = self.cv_distinct
        pbeq = self.cv_pbeq

        # Exactly one encoding variant active
        self._solver.add_global_constraints(
            z3.PbEq([(v_ad, 1), (v_ap, 1), (v_bp, 1)], 1)
        )

        # Variant => blocks
        self._solver.add_global_constraints(
            z3.Implies(v_ad, z3.And(arith, distinct, z3.Not(pbeq), z3.Not(boo))),
            z3.Implies(v_ap, z3.And(arith, pbeq, z3.Not(distinct), z3.Not(boo))),
            z3.Implies(v_bp, z3.And(boo, pbeq, z3.Not(arith), z3.Not(distinct))),
        )

        # Blocks <-> variants
        self._solver.add_global_constraints(
            arith == z3.Or(v_ad, v_ap),
            boo == v_bp,
            distinct == v_ad,
            pbeq == z3.Or(v_ap, v_bp),
        )

    def _select_fixed_variant_cv(self) -> z3.BoolRef:
        """
        Fix the representation for generation:
        - no_num=True  => bool_pbeq
        - no_num=False => arith_distinct or arith_pbeq, unless distinct is None (benchmarking)
        """
        if self._no_num:
            return self.cv_bool_pbeq

        # arithmetic
        if self._distinct is None:
            # Do not fix: let arith_distinct / arith_pbeq be explored (benchmarking),
            # but generation methods should not be used in this mode.
            return self.cv_arith  # weaker condition; you can still call check, but not deterministic for generation

        return self.cv_arith_distinct if self._distinct else self.cv_arith_pbeq

    # -------------------------
    # Load puzzle numbers
    # -------------------------

    def load_numbers(self, sudoku_array: List[int]) -> None:
        for r in range(9):
            for c in range(9):
                x = sudoku_array[r * 9 + c]
                assert x in self._valid_charset, f"Invalid sudoku digit: {x}"
                self._nums[r][c] = int(x)

    # -------------------------
    # Constraints
    # -------------------------

    def load_constraints(self) -> None:
        """
        Add classic Sudoku constraints as conditional constraints guarded by atomic CVs.

        All constraints are added via add_conditional_constraint (as requested).
        """
        if self._constraints_loaded:
            return

        rows_idx = range(9)
        cols_idx = range(9)
        offsets = list(itertools.product(range(0, 3), range(0, 3)))

        # Boxes (arith)
        arith_boxes: List[List[z3.ArithRef]] = []
        for br in range(0, 9, 3):
            for bc in range(0, 9, 3):
                arith_boxes.append([self.A[br + dr][bc + dc] for (dr, dc) in offsets])

        # Boxes (bool) for digit d
        def bool_boxes_for_digit(d: int) -> List[List[z3.BoolRef]]:
            boxes: List[List[z3.BoolRef]] = []
            for br in range(0, 9, 3):
                for bc in range(0, 9, 3):
                    boxes.append([self.B[br + dr][bc + dc][d] for (dr, dc) in offsets])
            return boxes

        # --- Given clues (conditional on representation) ---
        for r in rows_idx:
            for c in cols_idx:
                v = self._nums[r][c]
                if v != 0:
                    self._solver.add_conditional_constraint(self.A[r][c] == v, condition=self.cv_arith)
                    self._solver.add_conditional_constraint(self.B[r][c][v - 1], condition=self.cv_bool)

        # --- Arithmetic scaffold: cell in {1..9} ---
        for r in rows_idx:
            for c in cols_idx:
                self._solver.add_conditional_constraint(
                    z3.Or([self.A[r][c] == k for k in range(1, 10)]),
                    condition=self.cv_arith,
                )

        arith_rows = [self.A[r] for r in rows_idx]
        arith_cols = [[self.A[r][c] for r in rows_idx] for c in cols_idx]

        # --- Arithmetic Distinct ---
        for g in (arith_rows + arith_cols + arith_boxes):
            self._solver.add_conditional_constraint(z3.Distinct(g), condition=self.cv_arith_distinct)

        # --- Arithmetic PbEq ---
        for g in (arith_rows + arith_cols + arith_boxes):
            for k in range(1, 10):
                self._solver.add_conditional_constraint(
                    z3.PbEq([(x == k, 1) for x in g], 1),
                    condition=self.cv_arith_pbeq,
                )

        # --- Boolean one-hot scaffold + PbEq all-different ---
        # Exactly one digit per cell
        for r in rows_idx:
            for c in cols_idx:
                self._solver.add_conditional_constraint(
                    z3.PbEq([(self.B[r][c][d], 1) for d in range(9)], 1),
                    condition=self.cv_bool,
                )

        # For each digit d, each row/col/box has exactly one placement
        for d in range(9):
            # rows
            for r in rows_idx:
                self._solver.add_conditional_constraint(
                    z3.PbEq([(self.B[r][c][d], 1) for c in cols_idx], 1),
                    condition=self.cv_bool,
                )
            # cols
            for c in cols_idx:
                self._solver.add_conditional_constraint(
                    z3.PbEq([(self.B[r][c][d], 1) for r in rows_idx], 1),
                    condition=self.cv_bool,
                )
            # boxes
            for box in bool_boxes_for_digit(d):
                self._solver.add_conditional_constraint(
                    z3.PbEq([(b, 1) for b in box], 1),
                    condition=self.cv_bool,
                )

        self._constraints_loaded = True

    # -------------------------
    # Checking / incremental assertions (generation)
    # -------------------------

    def _active_lit(self, r: int, c: int, val: int) -> z3.BoolRef:
        """
        Returns the representation-specific literal for "cell(r,c) == val"
        used for incremental assertion during generation.
        """
        if self._no_num:
            return self.B[r][c][val - 1]
        return self.A[r][c] == val

    def _active_neg_lit(self, r: int, c: int, val: int) -> z3.BoolRef:
        """
        Returns the representation-specific literal for "cell(r,c) != val".
        """
        if self._no_num:
            return z3.Not(self.B[r][c][val - 1])
        return self.A[r][c] != val

    def check_condition(self, r: int, c: int, val: int) -> z3.CheckSatResult:
        """
        Check satisfiable under the fixed variant CV for this instance.
        """
        self.load_constraints()
        expr = self._active_lit(r, c, val)
        return self._solver.check_conditional_constraints(
            expr,
            condition=self._fixed_variant_cv,
            max_count=self._max_count,
        )

    def check_not_removable(self, r: int, c: int, val: int) -> z3.CheckSatResult:
        """
        Check satisfiable with the negation of a clue (used in hole generation).
        """
        self.load_constraints()
        expr = self._active_neg_lit(r, c, val)
        return self._solver.check_conditional_constraints(
            expr,
            condition=self._fixed_variant_cv,
            max_count=self._max_count,
        )

    def add_constraint(self, r: int, c: int, val: int) -> None:
        """
        Assert a chosen value into the active representation, conditionally guarded
        so it only applies when the right rep is active.
        """
        self._nums[r][c] = int(val)
        lit = self._active_lit(r, c, val)
        cond = self.cv_bool if self._no_num else self.cv_arith
        self._solver.add_conditional_constraint(lit, condition=cond)

    def add_not_equal_constraint(self, r: int, c: int, val: int) -> None:
        lit = self._active_neg_lit(r, c, val)
        cond = self.cv_bool if self._no_num else self.cv_arith
        self._solver.add_conditional_constraint(lit, condition=cond)

    # -------------------------
    # Generation (full grid)
    # -------------------------

    def gen_full_sudoku(self) -> Tuple[List[List[int]], int]:
        """
        Produce a solved/full Sudoku using the same high-level strategy as the original code.

        Note:
        - If distinct is None and no_num=False, generation is not deterministic (two arith variants allowed).
          This method expects distinct to be True/False for arithmetic generation.
        """
        if not self._no_num and self._distinct is None:
            raise ValueError("gen_full_sudoku() requires distinct to be fixed (True/False) when no_num=False.")

        self.load_constraints()

        if self._per_col:
            for i in range(9):
                if i == 0 and self._prefill:
                    candidates = list(range(1, 10))
                    random.shuffle(candidates)

                for j in range(9):
                    if self._nums[i][j] != 0:
                        continue

                    if i == 0 and self._prefill:
                        try_val = candidates.pop()
                        check = z3.sat
                    else:
                        vals = list(range(1, 10))
                        random.shuffle(vals)
                        try_val = vals.pop()
                        check = self.check_condition(i, j, try_val)

                    while check != z3.sat:
                        if check == z3.unknown:
                            # preserve original behavior: treat as hard instance
                            self._penalty += 1
                            # try another value
                        if len(vals) == 0:
                            raise RuntimeError(f"No valid value for cell ({i},{j}) under current encoding.")
                        try_val = vals.pop()
                        check = self.check_condition(i, j, try_val)

                    self.add_constraint(i, j, try_val)

                if self._verbose:
                    print(f"Finished row {i}: {self._nums[i]}")

        else:
            # fill by number 1..9 (original style)
            for num in range(1, 10):
                if self._verbose:
                    print(f"Filling number {num}")

                if num == 9:
                    for r in range(9):
                        for c in range(9):
                            if self._nums[r][c] == 0:
                                self.add_constraint(r, c, num)
                else:
                    cols = [i for i in range(9)]
                    for r in range(9):
                        random.shuffle(cols)
                        placed = False
                        for c in list(cols):
                            if self._nums[r][c] != 0:
                                if self._nums[r][c] == num and c in cols:
                                    cols.remove(c)
                                continue

                            res = self.check_condition(r, c, num)
                            if res == z3.sat:
                                self.add_constraint(r, c, num)
                                cols.remove(c)
                                placed = True
                                break
                        if not placed:
                            raise RuntimeError(f"Failed to place number {num} in row {r}.")

        if self._verbose:
            print("Generated full sudoku:")
            for row in self._nums:
                print(row)

        return self._nums, self._penalty

    # -------------------------
    # Hole generation helpers
    # -------------------------

    def removable(self, i: int, j: int, test_num: int) -> Tuple[bool, int]:
        """
        Remove cell (i,j) temporarily and test if forcing != test_num is SAT.
        If SAT, then puzzle is not uniquely forced by that number -> not removable.
        If UNSAT, removable.
        """
        self._nums[i][j] = 0
        self.load_constraints()

        result = self.check_not_removable(i, j, test_num)
        if result == z3.sat:
            return False, 0
        if result == z3.unknown:
            # Keep original penalty semantics
            return False, 1
        return True, 0

    def gen_holes_sudoku(self, solved_sudoku_1d: List[int], verbose: bool = False) -> Tuple[float, int]:
        """
        Generates a Sudoku puzzle with holes from a solved Sudoku grid (1D list length 81).
        Mirrors original approach (new solver per cell) for simplicity/correctness.
        """
        if verbose:
            print("Generating holes for solved puzzle...")

        st = time.time()
        penalty = 0
        sudoku_array = solved_sudoku_1d.copy()

        for i in range(9):
            for j in range(9):
                solver = Sudoku(
                    sudoku_array=sudoku_array,
                    classic=self._classic,
                    distinct=self._distinct,
                    per_col=self._per_col,
                    no_num=self._no_num,
                    prefill=self._prefill,
                    seed=self._seed,
                    timeout_ms=self._timeout_ms,
                    max_count=self._max_count,
                    verbose=False,
                )
                removable, temp_penalty = solver.removable(i, j, solved_sudoku_1d[i * 9 + j])
                if removable:
                    sudoku_array[i * 9 + j] = 0
                penalty += temp_penalty

        return time.time() - st, penalty

    # -------------------------
    # Logging / SMT2 utilities
    # -------------------------

    def generate_smt2_file(self) -> str:
        return self._solver.generate_smtlib()

    def generate_smt2_transcript(self) -> str:
        return self._solver.generate_smt2_transcript()

    def write_to_smt_and_sudoku_file(
        self,
        pos: Tuple[int, int],
        value: int,
        sat: str,
        assert_equals: bool,
    ) -> None:
        if not self._hard_smt_log_dir or not self._hard_sudoku_log_path:
            return

        os.makedirs(self._hard_smt_log_dir, exist_ok=True)
        os.makedirs(Path(self._hard_sudoku_log_path).parent, exist_ok=True)

        time_str = time.strftime("%m_%d_%H_%M_%S") + (str(time.time()).split(".")[1])[1:4]

        with open(os.path.join(self._hard_smt_log_dir, time_str), "w") as f:
            f.write(self._solver.generate_smtlib())

        sudoku_lst = "".join(str(ele) for row in self._nums for ele in row)
        log_entry = {
            "grid": sudoku_lst,
            "index": pos,
            "try_Val": value,
            "assert_equals": assert_equals,
            "is_sat": sat,
            "no_num": self._no_num,
            "distinct": self._distinct,
            "per_col": self._per_col,
            "prefill": self._prefill,
        }
        with open(self._hard_sudoku_log_path, "a+") as log_file:
            log_file.write(json.dumps(log_entry) + "\n")



def gen_full_sudoku(*constraints, seed=42, max_count=1, **kwargs) -> (float, int, List[List[int]]):
    """
    setup empty grid. Call Sudoku.gen_full_sudoku().
    append generated full sudoku to the designated path as a string

    :param hard_smt_log_path:
    :param constraints: classic, distinct, percol, no_num, prefill
    :param store_sudoku_path:
    :return: (time, penalty)
    """
    empty_list = [0]*81
    st = time.time()
    s = Sudoku(empty_list, *constraints, seed=seed, max_count=max_count, **kwargs)
    nums, penalty = s.gen_full_sudoku()
    smt2 = s.generate_smt2_transcript()
    with open("generated_full_sudoku.smt2", "w") as f:
        f.write(smt2)
    et = time.time()
    return et - st, penalty, nums

# def test_empty_grid_first_idx():
#     empty_list = [0]*81
#
#
#     s = Sudoku(empty_list)
if __name__ == '__main__':
    # constraints = (True, False, True, True, True)
    constraints = (True, True, True, False, True)
    print(gen_full_sudoku(*constraints, seed=42, benchmark_mode=False, record_smt=True)) # (2.1086909770965576, ...)
    # After avoiding smt2 collection and generation -> 1.8983988761901855
    # After removing the meta solver and cached all the CV combinations -> 1.794215202331543
    
    # 282 checks
    # raw smt2 file:  1.36s
    # after remove bool constraints:  0.41s
    # Remove all CV. Include only relavent constraints: 0.02s. ~25x slower