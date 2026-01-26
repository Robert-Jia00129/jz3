import os
from pathlib import Path

import pytest
import z3

from jz3.src.z3_wrapper import Solver


GOLDENS_DIR = Path(__file__).parent / "goldens"
UPDATE_GOLDENS = os.getenv("UPDATE_GOLDENS", "").lower() in ("1", "true", "yes", "y")


def _read_text(p: Path) -> str:
    return p.read_text(encoding="utf-8")


def _write_text(p: Path, s: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(s, encoding="utf-8")


def _assert_matches_golden(name: str, actual: str) -> None:
    """
    Exact golden-file matching.

    - If UPDATE_GOLDENS=1, overwrite the golden.
    - Otherwise, the golden must already exist and must match exactly.
    """
    golden_path = GOLDENS_DIR / name

    if UPDATE_GOLDENS and not os.path.exists(golden_path):
        _write_text(golden_path, actual)
        return

    assert golden_path.exists(), (
        f"Missing golden file: {golden_path}\n"
        f"Run with UPDATE_GOLDENS=1 to create/update goldens."
    )
    expected = _read_text(golden_path)
    assert actual == expected, f"SMT2 mismatch vs golden: {golden_path}"


# -----------------------------------------------------------------------------
# 1) Plain (check-sat) replay SMT2: deterministic SAT
# -----------------------------------------------------------------------------
def test_smt2_check_sat_sat_golden():
    solver = Solver()
    x = z3.Int("x")

    solver.add(x == 1)
    assert solver.check() == z3.sat

    smt = solver.generate_smtlib()
    _assert_matches_golden("check_sat_sat.smt2", smt)


# -----------------------------------------------------------------------------
# 2) Plain (check-sat) replay SMT2: deterministic UNSAT
# -----------------------------------------------------------------------------
def test_smt2_check_sat_unsat_golden():
    solver = Solver()
    x = z3.Int("x")

    solver.add(x == 1)
    solver.add(x == 2)
    assert solver.check() == z3.unsat

    smt = solver.generate_smtlib()
    _assert_matches_golden("check_sat_unsat.smt2", smt)


# -----------------------------------------------------------------------------
# 3) (check-sat-assuming) replay SMT2: deterministic SAT
#    Note: assumptions MUST NOT appear as (assert ...) in the SMT2
# -----------------------------------------------------------------------------
def test_smt2_check_sat_assuming_sat_golden():
    solver = Solver()
    x = z3.Int("x")

    solver.add(x >= 0)

    # SAT because x can be 4
    assert solver.check(x > 3) == z3.sat

    smt = solver.generate_smtlib()
    _assert_matches_golden("check_sat_assuming_sat.smt2", smt)


# -----------------------------------------------------------------------------
# 4) (check-sat-assuming) replay SMT2: deterministic UNSAT
# -----------------------------------------------------------------------------
def test_smt2_check_sat_assuming_unsat_golden():
    solver = Solver()
    x = z3.Int("x")

    solver.add(x >= 0)

    # UNSAT because x >= 0 and (assume x < 0)
    assert solver.check(x < 0) == z3.unsat

    smt = solver.generate_smtlib()
    _assert_matches_golden("check_sat_assuming_unsat.smt2", smt)


# -----------------------------------------------------------------------------
# 5) Mixed check order: check-sat then check-sat-assuming then check-sat
#    Deterministic outcomes and ordering in SMT2 history.
# -----------------------------------------------------------------------------
def test_smt2_mixed_check_and_check_assuming_golden():
    solver = Solver()
    x = z3.Int("x")

    solver.add(x >= 0)
    assert solver.check() == z3.sat          # SAT

    assert solver.check(x < 0) == z3.unsat   # UNSAT (assumption)

    solver.add(x == 0)
    assert solver.check() == z3.sat          # SAT

    smt = solver.generate_smtlib()
    _assert_matches_golden("mixed_check_and_check_assuming.smt2", smt)


# -----------------------------------------------------------------------------
# 6) Push/pop replay SMT2: deterministic SAT -> UNSAT -> SAT
# -----------------------------------------------------------------------------
def test_smt2_push_pop_golden():
    solver = Solver()
    x = z3.Int("x")

    solver.add(x >= 0)
    assert solver.check() == z3.sat

    solver.push()
    solver.add(x < 0)
    assert solver.check() == z3.unsat

    solver.pop()
    assert solver.check() == z3.sat

    smt = solver.generate_smtlib()
    _assert_matches_golden("push_pop_recording.smt2", smt)


# -----------------------------------------------------------------------------
# Helpers to build the demo encodings you provided (bool-only onehot variant)
# -----------------------------------------------------------------------------
def _build_demo_solver_bool_only_onehot(*, benchmark_mode: bool = True):
    solver = Solver(benchmark_mode=benchmark_mode)

    time = z3.Int("time")

    arith_range = z3.Bool("arith_range")
    arith_split = z3.Bool("arith_split")
    bool_onehot = z3.Bool("bool_onehot")

    # Encoding 1: arithmetic range [8, 17] excluding 12
    solver.add_conditional_constraint(
        z3.And(8 <= time, time <= 17, time != 12),
        condition=arith_range,
    )

    # Encoding 2: arithmetic split range excluding 12
    solver.add_conditional_constraint(
        z3.Or(
            z3.And(8 <= time, time < 12),
            z3.And(12 < time, time <= 17),
        ),
        condition=arith_split,
    )

    # Encoding 3: bool-only one-hot for hour_is_8..17, excluding 12
    hours = list(range(8, 18))
    hour_is = {h: z3.Bool(f"hour_is_{h}") for h in hours}

    solver.add_conditional_constraint(
        z3.PbEq([(hour_is[h], 1) for h in hours], 1),
        condition=bool_onehot,
    )
    solver.add_conditional_constraint(z3.Not(hour_is[12]), condition=bool_onehot)

    # Meta constraint: exactly one encoding enabled
    solver.add_global_constraints(
        z3.PbEq([(arith_range, 1), (arith_split, 1), (bool_onehot, 1)], 1)
    )

    return solver, time, hour_is, arith_range, arith_split, bool_onehot


# -----------------------------------------------------------------------------
# 7) Canonical SMT2 from check_conditional_constraints: arithmetic encoding
#    IMPORTANT: inner solver uses check(*args) => (check-sat-assuming ...) in SMT2.
# -----------------------------------------------------------------------------
def test_smt2_canonical_from_check_conditional_constraints_arith_range_sat_golden():
    solver, time, hour_is, arith_range, arith_split, bool_onehot = _build_demo_solver_bool_only_onehot()

    assert solver.check_conditional_constraints(time == 11, condition=arith_range) == z3.sat

    # The SMT2 returned should be the canonical *inner* SMT2 for this call.
    smt = solver.generate_smtlib()
    _assert_matches_golden("canonical_arith_range_time_11_sat.smt2", smt)


# -----------------------------------------------------------------------------
# 8) Canonical SMT2 from check_conditional_constraints: bool-only onehot UNSAT
#    Query hour_is_12 contradicts Not(hour_is_12) under that encoding.
# -----------------------------------------------------------------------------
def test_smt2_canonical_from_check_conditional_constraints_bool_onehot_unsat_golden():
    solver, time, hour_is, arith_range, arith_split, bool_onehot = _build_demo_solver_bool_only_onehot()

    assert solver.check_conditional_constraints(hour_is[12], condition=bool_onehot) == z3.unsat

    smt = solver.generate_smtlib()
    _assert_matches_golden("canonical_bool_onehot_hour_is_12_unsat.smt2", smt)


# -----------------------------------------------------------------------------
# 9) Non-golden semantic test: CV must be True or atomic Bool (no composed expressions)
# -----------------------------------------------------------------------------
def test_add_conditional_constraint_rejects_composed_cv():
    solver = Solver()
    x = z3.Int("x")

    a = z3.Bool("a")
    b = z3.Bool("b")

    with pytest.raises(TypeError):
        solver.add_conditional_constraint(x == 1, condition=z3.And(a, b))
