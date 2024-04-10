import unittest
from Sudoku import Sudoku

class TestSudokuGenHoles(unittest.TestCase):
    def test_valid_solved_grid(self):
        solved_grid = [5, 3, 4, 6, 7, 8, 9, 1, 2, 6, 7, 2, 1, 9, 5, 3, 4, 8, 1, 9, 8, 3, 4, 2, 5, 6, 7,
                       8, 5, 9, 7, 6, 1, 4, 2, 3, 4, 2, 6, 8, 5, 3, 7, 9, 1, 7, 1, 3, 9, 2, 4, 8, 5, 6,
                       9, 6, 1, 5, 3, 7, 2, 8, 4, 2, 8, 7, 4, 1, 9, 6, 3, 5, 3, 4, 5, 2, 8, 6, 1, 7, 9]
        sudoku = Sudoku(solved_grid, classic=True, distinct=True, per_col=True, no_num=False, prefill=True)
        time, penalty = sudoku.gen_holes_sudoku(solved_grid)
        self.assertGreater(time, 0)
        self.assertGreaterEqual(penalty, 0)

    def test_empty_grid(self):
        empty_grid = [0] * 81
        sudoku = Sudoku(empty_grid, classic=True, distinct=True, per_col=True, no_num=False, prefill=True)
        time, penalty = sudoku.gen_holes_sudoku(empty_grid)
        self.assertGreaterEqual(time, 0)
        self.assertGreaterEqual(penalty, 0)

    def test_different_constraints(self):
        solved_grid = [5, 3, 4, 6, 7, 8, 9, 1, 2, 6, 7, 2, 1, 9, 5, 3, 4, 8, 1, 9, 8, 3, 4, 2, 5, 6, 7,
                       8, 5, 9, 7, 6, 1, 4, 2, 3, 4, 2, 6, 8, 5, 3, 7, 9, 1, 7, 1, 3, 9, 2, 4, 8, 5, 6,
                       9, 6, 1, 5, 3, 7, 2, 8, 4, 2, 8, 7, 4, 1, 9, 6, 3, 5, 3, 4, 5, 2, 8, 6, 1, 7, 9]
        constraints = [
            (True, True, True, False, True),
            (True, False, False, True, False),
            (False, True, True, True, False)
        ]
        for constraint in constraints:
            sudoku = Sudoku(solved_grid, *constraint)
            _, _ = sudoku.gen_holes_sudoku(solved_grid)
            # Add assertions to verify the generated puzzle respects the constraints

    def test_verbosity(self):
        solved_grid = [5, 3, 4, 6, 7, 8, 9, 1, 2, 6, 7, 2, 1, 9, 5, 3, 4, 8, 1, 9, 8, 3, 4, 2, 5, 6, 7,
                       8, 5, 9, 7, 6, 1, 4, 2, 3, 4, 2, 6, 8, 5, 3, 7, 9, 1, 7, 1, 3, 9, 2, 4, 8, 5, 6,
                       9, 6, 1, 5, 3, 7, 2, 8, 4, 2, 8, 7, 4, 1, 9, 6, 3, 5, 3, 4, 5, 2, 8, 6, 1, 7, 9]
        sudoku = Sudoku(solved_grid, classic=True, distinct=True, per_col=True, no_num=False, prefill=True)
        _, _ = sudoku.gen_holes_sudoku(solved_grid, verbose=True)
        # Add assertions to verify the expected output when verbose=True
        _, _ = sudoku.gen_holes_sudoku(solved_grid, verbose=False)
        # Add assertions to verify the expected output when verbose=False

if __name__ == '__main__':
    unittest.main()