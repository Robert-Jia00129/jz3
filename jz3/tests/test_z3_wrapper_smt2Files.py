import os
from pathlib import Path

import pytest
from jz3.src.z3_wrapper import Solver
import jz3 as z3

GOLDENS_DIR = Path(__file__).parent / "goldens"
UPDATE_GOLDENS = os.getenv("UPDATE_GOLDENS", "").lower() in ("1", "true", "yes", "y")


def _read_text(p: Path) -> str:
    return p.read_text(encoding="utf-8")


def _write_text(p: Path, s: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(s, encoding="utf-8")


def _assert_matches_golden(name: str, actual: str) -> None:
    """
    Golden-file assertion with an update mode.
    Set UPDATE_GOLDENS=1 to overwrite expected goldens.
    """
    golden_path = GOLDENS_DIR / name
    if UPDATE_GOLDENS or not golden_path.exists():
        _write_text(golden_path, actual)
        # If we're updating, we still want the test to pass.
        return
    
    expected = _read_text(golden_path)
    assert actual == expected, f"SMT2 mismatch vs golden: {golden_path}"




def test_generate_smt2_simple_golden():
    """
    First simple golden SMT2 test.
    Workflow:
      1) Run once with UPDATE_GOLDENS=1 to write tests/goldens/simple_recording.smt2
      2) Inspect that file manually and confirm it is what you want.
      3) Commit it; future runs assert exact match.
    """
    solver = Solver()
    
    x = z3.Int("x")
    solver.add(x == 1)
    
    solver.start_recording()
    res = solver.check()
    assert res == z3.sat
    
    smt = solver.generate_smtlib()
    _assert_matches_golden("simple_recording.smt2", smt)


def test_generate_smt2_push_pop_golden():
    """
    Exercises push/pop recording and validates the generated SMT-LIB includes:
      - (push 1)
      - (pop 1)
      - assertions added at each stack depth
      - multiple (check-sat) calls

    Workflow:
      UPDATE_GOLDENS=1 pytest -q
      then inspect tests/goldens/push_pop_recording.smt2
    """
    solver = Solver()
    
    x = z3.Int("x")
    
    solver.start_recording()
    
    # Base level assertion + check
    solver.add(x >= 0)
    r0 = solver.check()
    assert r0 == z3.sat
    
    # Push, add stronger constraint, check becomes UNSAT, then pop and check returns SAT
    solver.push()
    solver.add(x < 0)
    r1 = solver.check()
    assert r1 == z3.unsat
    
    solver.pop()
    r2 = solver.check()
    assert r2 == z3.sat
    
    smt = solver.generate_smtlib()
    
    # Structural sanity checks (helpful even when updating goldens)
    assert "(push 1)" in smt
    assert "(pop 1)" in smt
    
    # Ensure the level-specific assertions appear
    assert "(assert (>= x 0))" in smt
    assert "(assert (< x 0))" in smt
    
    # Ensure check-sat occurs at least 3 times (one before push, one inside, one after pop)
    assert smt.count("(check-sat)") >= 3
    
    # Ensure push happens before the inner (< x 0) assertion and pop happens after it
    push_idx = smt.find("(push 1)")
    inner_assert_idx = smt.find("(assert (< x 0))")
    pop_idx = smt.find("(pop 1)")
    assert 0 <= push_idx < inner_assert_idx < pop_idx
    
    _assert_matches_golden("push_pop_recording.smt2", smt)
