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


def optimizer_test():
    # Create variables
    x = z3.Int('x')
    y = z3.Int('y')
    z = z3.Int('z')
    
    # Create conditions
    cond1 = z3.Bool('cond1')
    cond2 = z3.Bool('cond2')
    cond3 = z3.Bool('cond3')
    
    # Create constraints
    constraints = [
        z3.Implies(cond1, x > 0),
        z3.Implies(cond2, y > 0),
        z3.Implies(cond3, z > 0)
    ]
    
    # Create optimizer
    opt = z3.Optimize()
    
    # Add constraints to the optimizer
    for constraint in constraints:
        opt.add(constraint)
    
    # Add conditions to the optimizer
    opt.add(z3.Or(cond1, cond2, cond3))
    
    # First combination (maximize)
    opt.push()
    opt.maximize(z3.Sum([z3.If(cond, 1, 0) for cond in [cond1, cond2, cond3]]))
    opt.check()
    combination1 = opt.model()
    opt.pop()
    
    # Second combination (minimize)
    opt.push()
    opt.minimize(z3.Sum([z3.If(cond, 1, 0) for cond in [cond1, cond2, cond3]]))
    combination2 = opt.model()
    opt.pop()
    
    # Print the combinations
    print("Combination 1:")
    print(combination1)
    print("Combination 2:")
    print(combination2)
    
def test_add_conditional_constraint_from_demo():
    """
    Converts solver_demo() into a test focusing on:
      - add_conditional_constraint stores assertions + CVs correctly
      - meta enumeration under global constraints yields 2 assignments
      - result is SAT
    """
    solver = Solver(benchmark_mode=True)
    
    x = z3.Int("x")
    encoding1 = z3.Bool("encoding1")
    encoding2 = z3.Bool("encoding2")
    
    c1 = z3.And(8 <= x, x <= 17, x != 12)
    c2 = z3.Or(z3.And(8 <= x, x < 12), z3.And(12 < x, x <= 17))
    
    solver.add_conditional_constraint(c1, condition=encoding1)
    solver.add_conditional_constraint(c2, condition=encoding2)
    
    # Internal state checks (name-mangled private fields)
    assertions = solver._Solver__assertions  # [(And(x >= 8, x <= 17, x != 12), encoding1), (Or(And(x >= 8, x < 12), And(x > 12, x <= 17)), encoding2)]
    cvs = solver._Solver__CVs  # {encoding1, encoding2}
    
    assert (c1, encoding1) in assertions
    assert (c2, encoding2) in assertions
    assert encoding1 in cvs
    assert encoding2 in cvs
    assert cvs == {encoding1, encoding2}
    
    # Same global constraints as demo: Or + Distinct => exactly one True
    solver.add_global_constraints(z3.Or(encoding1, encoding2))
    solver.add_global_constraints(z3.Distinct(encoding1, encoding2))
    
    solver.start_recording()
    res = solver.check_conditional_constraints()
    
    assert res == z3.sat
    
    assignments = solver.get_condition_var_assignment_model()  # [{'encoding1': True, 'encoding2': False}, {'encoding1': False, 'encoding2': True}]
    # Exactly 2 distinct assignments for two bool CVs with XOR-like constraint
    assert isinstance(assignments, list)
    assert len(assignments) == 2
    
    # Ensure the assignments reflect "exactly one enabled"
    # Stored as dict[str,bool] in your implementation
    for a in assignments:
        assert set(a.keys()) == {"encoding1", "encoding2"}
        assert (a["encoding1"] + a["encoding2"]) == 1  # True==1, False==0


def test_add_conditional_constraint_with_args_forced_cv_sat_and_unsat():
    """
    Verifies the "force this condition to True for this check" behavior:
      meta.add(condition) when condition is not True.
    And verifies SAT/UNSAT outcomes when adding extra guarded args.
    """
    solver = Solver(benchmark_mode=False)
    
    x = z3.Int("x")
    cv = z3.Bool("cv")
    
    # Base conditional constraint guarded by cv
    solver.add_conditional_constraint(x == 1, condition=cv)
    
    # Make the meta-space allow cv=True; simplest is to just allow it with Or(cv, Not(cv)).
    solver.add_global_constraints(z3.Or(cv, z3.Not(cv)))
    
    # UNSAT case: force cv=True, add a conflicting extra constraint
    res_unsat = solver.check_conditional_constraints(x == 2, condition=cv)
    assert res_unsat == z3.unsat
    
    # SAT case: force cv=True, add a consistent extra constraint
    res_sat = solver.check_conditional_constraints(x == 1, condition=cv)
    assert res_sat == z3.sat
    
    # SAT case: simple check without forcing cv
    res_sat = solver.check_conditional_constraints(x == 2)
    assert res_sat == z3.sat


def test_add_conditional_constraint_demo_force_sat_and_unsat():
    """
    Demo-style test that mirrors the intended real use case:

    - We register *three alternative encodings* of the same requirement:
        "time is in [8..17] excluding 12"
      guarded by *encoding condition variables* (CVs).

    - Then we run "queries" under a *forced encoding*:
        * For range/split encodings, the query is `x == k`
        * For one-hot encoding, the query is selecting a boolean indicator `hour_is_k`

    - We verify:
        1) Under each forced encoding, 11 is SAT
        2) Under each forced encoding, 12 is UNSAT
        3) The meta-model indeed sets exactly the forced encoding CV to True
    """
    solver = Solver(benchmark_mode=False)
    
    time = z3.Int("time")
    
    # Encoding selector CVs (meta variables)
    arith_range = z3.Bool("arith_range")  # encoding 1: single range with != 12
    arith_split = z3.Bool("arith_split")  # encoding 2: split range around 12
    bool_onehot = z3.Bool("bool_onehot")  # encoding 3: one-hot discrete hour variables
    
    # Encoding 1: range [8, 17] excluding 12
    range_encoding = z3.And(8 <= time, time <= 17, time != 12)
    solver.add_conditional_constraint(range_encoding, condition=arith_range)
    
    # Encoding 2: split range excluding 12
    split_encoding = z3.Or(
        z3.And(8 <= time, time < 12),
        z3.And(12 < time, time <= 17),
    )
    solver.add_conditional_constraint(split_encoding, condition=arith_split)
    
    # Encoding 3: one-hot discrete hours 8..17, excluding 12
    # - hour_is_i => time == i
    # - exactly one hour_is_i is true
    # - hour_is_12 is forbidden
    hours = list(range(8, 18))
    hour_is = {h: z3.Bool(f"hour_is_{h}") for h in hours}
    
    # Link booleans to the integer time (only enforced when bool_onehot is enabled)
    for h in hours:
        solver.add_conditional_constraint(z3.Implies(hour_is[h], time == h), condition=bool_onehot)
    
    # Exactly one hour selected
    solver.add_conditional_constraint(
        z3.PbEq([(hour_is[h], 1) for h in hours], 1),
        condition=bool_onehot,
    )
    
    # Exclude 12 directly (No longer links to arithmetic `time` variable)
    solver.add_conditional_constraint(z3.Not(hour_is[12]), condition=bool_onehot)
    
    # Meta constraint: exactly one encoding is enabled
    solver.add_global_constraints(
        z3.PbEq([(arith_range, 1), (arith_split, 1), (bool_onehot, 1)], 1)
    )
    
    def assert_forced_encoding_is_selected(forced_cv: z3.BoolRef) -> None:
        """
        check_conditional_constraints() stores a single CV assignment model in non-benchmark mode.
        When we pass condition=<forced_cv>, the meta-solver must set that CV to True.
        """
        models = solver.get_condition_var_assignment_model()
        assert isinstance(models, list) and len(models) == 1
        
        assignment = models[0]  # dict[str,bool]
        assert set(assignment.keys()) == {"arith_range", "arith_split", "bool_onehot"}
        
        assert assignment[str(forced_cv)] is True
        for other_name in {"arith_range", "arith_split", "bool_onehot"} - {str(forced_cv)}:
            assert assignment[other_name] is False
    
    # ---------------------------------------------------------------------
    # SAT queries: ask for "11" under each encoding
    # ---------------------------------------------------------------------
    assert solver.check_conditional_constraints(time == 11, condition=arith_range) == z3.sat
    assert_forced_encoding_is_selected(arith_range)
    
    assert solver.check_conditional_constraints(time == 11, condition=arith_split) == z3.sat
    assert_forced_encoding_is_selected(arith_split)
    
    # One-hot encoding: query is selecting the corresponding boolean indicator
    assert solver.check_conditional_constraints(hour_is[11], condition=bool_onehot) == z3.sat
    assert_forced_encoding_is_selected(bool_onehot)
    
    # ---------------------------------------------------------------------
    # UNSAT queries: ask for "12" under each encoding
    # ---------------------------------------------------------------------
    assert solver.check_conditional_constraints(time == 12, condition=arith_range) == z3.unsat
    assert_forced_encoding_is_selected(arith_range)
    
    assert solver.check_conditional_constraints(time == 12, condition=arith_split) == z3.unsat
    assert_forced_encoding_is_selected(arith_split)
    
    assert solver.check_conditional_constraints(hour_is[12], condition=bool_onehot) == z3.unsat
    assert_forced_encoding_is_selected(bool_onehot)


def test_add_conditional_constraint_demo_bool_only_onehot_force_sat_and_unsat():
    """
    Same as `test_add_conditional_constraint_demo_force_sat_and_unsat` but bool vars no longer implies the arithmetic 'time' var. Bool encoding and arith encoding work completely separately.
    """
    solver = Solver(benchmark_mode=False)
    
    time = z3.Int("time")
    
    # Encoding selector CVs (meta variables) — using your preferred names
    arith_range = z3.Bool("arith_range")  # encoding 1: single range with != 12
    arith_split = z3.Bool("arith_split")  # encoding 2: split range around 12
    bool_onehot = z3.Bool("bool_onehot")  # encoding 3: one-hot discrete hour variables
    
    # ---------------------------------------------------------------------
    # Encoding 1: arithmetic range [8, 17] excluding 12
    # ---------------------------------------------------------------------
    solver.add_conditional_constraint(
        z3.And(8 <= time, time <= 17, time != 12),
        condition=arith_range,
    )
    
    # ---------------------------------------------------------------------
    # Encoding 2: arithmetic split range excluding 12
    # ---------------------------------------------------------------------
    solver.add_conditional_constraint(
        z3.Or(
            z3.And(8 <= time, time < 12),
            z3.And(12 < time, time <= 17),
        ),
        condition=arith_split,
    )
    
    # ---------------------------------------------------------------------
    # Encoding 3: *bool-only* one-hot hours 8..17, excluding 12
    # - exactly one hour_is_h is true
    # - directly assert hour_is_12 is false (no arithmetic 'time' variable involved)
    # ---------------------------------------------------------------------
    hours = list(range(8, 18))
    hour_is = {h: z3.Bool(f"hour_is_{h}") for h in hours}
    
    solver.add_conditional_constraint(
        z3.PbEq([(hour_is[h], 1) for h in hours], 1),
        condition=bool_onehot,
    )
    solver.add_conditional_constraint(z3.Not(hour_is[12]), condition=bool_onehot)
    
    # ---------------------------------------------------------------------
    # Meta constraint: exactly one encoding CV is enabled
    # ---------------------------------------------------------------------
    solver.add_global_constraints(
        z3.PbEq([(arith_range, 1), (arith_split, 1), (bool_onehot, 1)], 1)
    )
    
    def assert_forced_encoding_is_selected(forced_cv: z3.BoolRef) -> None:
        models = solver.get_condition_var_assignment_model()
        assert isinstance(models, list) and len(models) == 1
        
        assignment = models[0]  # dict[str,bool]
        assert set(assignment.keys()) == {"arith_range", "arith_split", "bool_onehot"}
        
        assert assignment[str(forced_cv)] is True
        for other_name in {"arith_range", "arith_split", "bool_onehot"} - {str(forced_cv)}:
            assert assignment[other_name] is False
    
    # ---------------------------------------------------------------------
    # SAT queries
    # ---------------------------------------------------------------------
    
    assert solver.check_conditional_constraints(time == 11, condition=arith_range) == z3.sat
    assert_forced_encoding_is_selected(arith_range)
    
    assert solver.check_conditional_constraints(time == 11, condition=arith_split) == z3.sat
    assert_forced_encoding_is_selected(arith_split)
    
    # Bool-only encoding: query by selecting the boolean for the chosen hour
    assert solver.check_conditional_constraints(hour_is[11], condition=bool_onehot) == z3.sat
    assert_forced_encoding_is_selected(bool_onehot)
    
    # ---------------------------------------------------------------------
    # UNSAT queries
    # ---------------------------------------------------------------------
    
    assert solver.check_conditional_constraints(time == 12, condition=arith_range) == z3.unsat
    assert_forced_encoding_is_selected(arith_range)
    
    assert solver.check_conditional_constraints(time == 12, condition=arith_split) == z3.unsat
    assert_forced_encoding_is_selected(arith_split)
    
    # Bool-only encoding: hour_is_12 contradicts Not(hour_is_12)
    assert solver.check_conditional_constraints(hour_is[12], condition=bool_onehot) == z3.unsat
    assert_forced_encoding_is_selected(bool_onehot)


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
