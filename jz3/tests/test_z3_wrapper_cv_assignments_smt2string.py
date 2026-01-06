import os
from pathlib import Path
import json
from typing import *
import z3
from jz3.src.z3_wrapper import Solver, CVRun

GOLDENS_DIR = Path(__file__).parent / "goldens/multi_cv_smt2"
# UPDATE_GOLDENS = os.getenv("UPDATE_GOLDENS", "").lower() in ("1", "true", "yes", "y")
UPDATE_GOLDENS = True


def _read_text(p: Path) -> str:
    return p.read_text(encoding="utf-8")


def _write_text(p: Path, s: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(s, encoding="utf-8")


def _assert_matches_golden(name: str, actual: Union[str | List[Any]]) -> None:
    # convert actual to string
    if not isinstance(actual, str):
        actual = _runs2str(actual)
        
    golden_path = GOLDENS_DIR / name
    if UPDATE_GOLDENS and not os.path.exists(golden_path):
        _write_text(golden_path, actual)
        return
    assert golden_path.exists(), (
        f"Missing golden file: {golden_path}\n"
        f"Run with UPDATE_GOLDENS=1 to create/update goldens."
    )
    expected = _read_text(golden_path)
    

    assert actual == expected, f"Mismatch vs golden: {golden_path}"

def _runs2str(runs: List[CVRun]) -> str:
    payload = []
    for r in runs:
        assignment = dict(sorted(r.assignment.items()))
        payload.append(
            {
                "assignment": assignment,
                "sat": str(r.sat),
                "smt2": r.smt2,
            }
        )
    payload.sort(key=lambda e: json.dumps(e["assignment"], sort_keys=True))
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"

def _snapshot_runs_sorted(solver: Solver) -> str:
    """
    Snapshot solver.get_runs() into a single stable JSON string.

    We sort by assignment to avoid nondeterminism in Z3's model enumeration order.
    """
    runs = solver.get_runs()
    run_str = _runs2str(runs)
    return run_str


def test_cv_runs_snapshot_simple_two_cvs_one_active_sat():
    """
    Simple starting point:
      - two CVs A, B
      - global constraint: exactly one is True
      - conditional constraints:
          A -> (x == 1)
          B -> (x == 2)
      - query: (x == 1) under forced A
    Expectations:
      - exactly one run recorded (benchmark_mode=False)
      - assignment must be {"A": True, "B": False}
      - per-run SMT2 should reflect only the enabled constraint plus the assumption query
        (i.e., check-sat-assuming ((= x 1))).
    """
    solver = Solver(benchmark_mode=False)
    x = z3.Int("x")
    
    A = z3.Bool("A")
    B = z3.Bool("B")
    
    solver.add_conditional_constraint(x == 1, condition=A)
    solver.add_conditional_constraint(x == 2, condition=B)
    solver.add_global_constraints(z3.PbEq([(A, 1), (B, 1)], 1))
    
    assert solver.check_conditional_constraints(x == 1, condition=A) == z3.sat
    
    actual = solver.get_runs()
    assert len(actual) == 1
    assert actual[0].assignment == {"A": True, "B": False}
    assert actual[0].sat == z3.sat
    _assert_matches_golden("cv_runs_simple_two_cvs_A_forced_sat.json", actual)


def test_cv_assignment_three_cvs_force_family_two_runs_golden():
    solver = Solver(benchmark_mode=True)
    x = z3.Int("x")
    
    # Encodings
    A1 = z3.Bool("A1")
    A2 = z3.Bool("A2")
    OTHER = z3.Bool("OTHER")
    
    # Atomic family selector to force only A-family choices
    use_A = z3.Bool("use_A")
    
    solver.add_conditional_constraint(x == 1, condition=A1)
    solver.add_conditional_constraint(x == 1, condition=A2)  # same semantics, different CV
    solver.add_conditional_constraint(x == 99, condition=OTHER)
    
    # If use_A: exactly one of {A1,A2} is true, and OTHER is false.
    # Else: OTHER is true, and A1/A2 false.
    solver.add_global_constraints(
        z3.Implies(
            use_A,
            z3.And(
                z3.PbEq([(A1, 1), (A2, 1)], 1),
                z3.Not(OTHER),
            ),
        ),
        z3.Implies(
            z3.Not(use_A),
            z3.And(
                OTHER,
                z3.Not(A1),
                z3.Not(A2),
            ),
        ),
    )
    
    # Force the A-family; query is SAT
    assert solver.check_conditional_constraints(x == 1, condition=use_A, max_count=10) == z3.sat
    
    runs = solver.get_runs()
    assert len(runs) == 2
    
    # Exact set of assignments (order-independent)
    assignments = {tuple(sorted(r.assignment.items())) for r in runs}
    assert assignments == {
        (("A1", True), ("A2", False), ("OTHER", False)),
        (("A1", False), ("A2", True), ("OTHER", False)),
    }
    for r in runs:
        assert r.sat == z3.sat
    
    _assert_matches_golden("cv_three_cvs_force_family_two_runs.json", _snapshot_runs_sorted(solver))


# -----------------------------------------------------------------------------
# 3) Push/pop: simple outer replay SMT2 golden
#    This is not a CV run test; it verifies history recording, stack ops, and SAT transitions.
# -----------------------------------------------------------------------------
def test_push_pop_simple_sat_unsat_sat_smt2_golden():
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
    _assert_matches_golden("push_pop_simple_sat_unsat_sat.smt2", smt)


# -----------------------------------------------------------------------------
# Optional extra: push/pop should NOT create CV runs unless check_conditional_constraints is called
# -----------------------------------------------------------------------------
def test_push_pop_does_not_create_cv_runs():
    solver = Solver()
    x = z3.Int("x")
    
    solver.add(x >= 0)
    assert solver.check() == z3.sat
    solver.push()
    solver.add(x < 0)
    assert solver.check() == z3.unsat
    solver.pop()
    assert solver.check() == z3.sat
    
    assert solver.get_runs() == []


def test_cv_runs_snapshot_four_cvs_force_arith_two_assignments_golden():
    """
    Four CVs:
      - arith_distinct, arith_pbeq
      - bool_distinct, bool_pbeq

    We also introduce a higher-level atomic Bool 'arith' used ONLY for forcing:
      check_conditional_constraints(..., condition=arith)

    Global constraints ensure:
      - If arith is True: exactly one of {arith_distinct, arith_pbeq} is True
                         and both bool_* CVs are False.
      - If arith is False: exactly one of {bool_distinct, bool_pbeq} is True
                           and both arith_* CVs are False.

    So when condition=arith is forced True, there are exactly TWO CV assignments,
    even though four CVs exist overall.

    We then query (assumption) x == 3. Both arith encodings allow x==3, so SAT.
    """
    solver = Solver(benchmark_mode=True)  # must be True to enumerate >1 assignment
    x = z3.Int("x")
    
    # Four CVs (atomic Bool variables)
    arith_distinct = z3.Bool("arith_distinct")
    arith_pbeq = z3.Bool("arith_pbeq")
    bool_distinct = z3.Bool("bool_distinct")
    bool_pbeq = z3.Bool("bool_pbeq")
    
    # Higher-level atomic Bool used for forcing the "family"
    arith = z3.Bool("arith")
    
    # -------------------------
    # Arithmetic encoding A: "distinct-style" (simple Or of allowed constants)
    # -------------------------
    solver.add_conditional_constraint(
        z3.Or(x == 1, x == 2, x == 3),
        condition=arith_distinct,
    )
    
    # -------------------------
    # Arithmetic encoding B: "PB-eq style" using one-hot indicators
    # -------------------------
    a1, a2, a3 = z3.Bools("a1 a2 a3")
    solver.add_conditional_constraint(
        z3.PbEq([(a1, 1), (a2, 1), (a3, 1)], 1),
        condition=arith_pbeq,
    )
    solver.add_conditional_constraint(z3.Implies(a1, x == 1), condition=arith_pbeq)
    solver.add_conditional_constraint(z3.Implies(a2, x == 2), condition=arith_pbeq)
    solver.add_conditional_constraint(z3.Implies(a3, x == 3), condition=arith_pbeq)
    
    # -------------------------
    # Bool encodings exist only to create additional CVs; they will be forced OFF when arith=True
    # -------------------------
    b1, b2 = z3.Bools("b1 b2")
    solver.add_conditional_constraint(z3.Distinct(b1, b2), condition=bool_distinct)
    
    c1, c2 = z3.Bools("c1 c2")
    solver.add_conditional_constraint(z3.PbEq([(c1, 1), (c2, 1)], 1), condition=bool_pbeq)
    
    # -------------------------
    # Global constraints: arith selects which pair is active
    # -------------------------
    solver.add_global_constraints(
        z3.Implies(
            arith,
            z3.And(
                z3.PbEq([(arith_distinct, 1), (arith_pbeq, 1)], 1),
                z3.Not(bool_distinct),
                z3.Not(bool_pbeq),
            ),
        ),
        z3.Implies(
            z3.Not(arith),
            z3.And(
                z3.PbEq([(bool_distinct, 1), (bool_pbeq, 1)], 1),
                z3.Not(arith_distinct),
                z3.Not(arith_pbeq),
            ),
        ),
    )
    
    # Force 'arith' family, and query x==3 as an assumption in the inner solver.
    assert solver.check_conditional_constraints(x == 3, condition=arith, max_count=10) == z3.sat
    
    runs = solver.get_runs()
    assert len(runs) == 2  # exactly the two arith assignments
    
    # Optional: enforce the assignment shapes (still compatible with golden snapshot)
    for r in runs:
        assert set(r.assignment.keys()) == {"arith_distinct", "arith_pbeq", "bool_distinct", "bool_pbeq"}
        assert r.assignment["bool_distinct"] is False
        assert r.assignment["bool_pbeq"] is False
        assert (r.assignment["arith_distinct"], r.assignment["arith_pbeq"]) in {(True, False), (False, True)}
        assert str(r.sat) == "sat"
    
    actual = _snapshot_runs_sorted(solver)
    _assert_matches_golden("cv_runs_four_cvs_force_arith_x3_sat.json", actual)


def _build_solver_3cellsfour_encodings_arith_bool_distinct_pbeq(*, benchmark_mode: bool = True):
    solver = Solver(benchmark_mode=benchmark_mode)
    
    cell1, cell2, cell3 = z3.Ints("cell1 cell2 cell3")
    
    arith_distinct = z3.Bool("arith_distinct")
    arith_pbeq = z3.Bool("arith_pbeq")
    bool_distinct = z3.Bool("bool_distinct")
    bool_pbeq = z3.Bool("bool_pbeq")
    
    use_arith = z3.Bool("use_arith")
    use_bool = z3.Bool("use_bool")
    
    vals = [1, 2, 3]
    cells = [cell1, cell2, cell3]
    cell_by_i = {1: cell1, 2: cell2, 3: cell3}
    
    # -------------------------
    # arith_distinct: domain via Or + Distinct
    # -------------------------
    dom = lambda c: z3.Or(c == 1, c == 2, c == 3)
    solver.add_conditional_constraint(dom(cell1), dom(cell2), dom(cell3), condition=arith_distinct)
    solver.add_conditional_constraint(z3.Distinct(cell1, cell2, cell3), condition=arith_distinct)
    
    # -------------------------
    # arith_pbeq: per-cell exactly-one + per-value at-most-one (injective)
    # -------------------------
    for c in cells:
        solver.add_conditional_constraint(
            z3.PbEq([(c == v, 1) for v in vals], 1),
            condition=arith_pbeq,
        )
    for v in vals:
        solver.add_conditional_constraint(
            z3.PbEq([(c == v, 1) for c in cells], 1),
            condition=arith_pbeq,
        )
    
    # -------------------------
    # bool_distinct: onehot + pairwise no-collision per value
    # -------------------------
    b = {(i, v): z3.Bool(f"bd_c{i}_is_{v}") for i in [1, 2, 3] for v in vals}
    
    for i in [1, 2, 3]:
        solver.add_conditional_constraint(
            z3.PbEq([(b[(i, v)], 1) for v in vals], 1),
            condition=bool_distinct,
        )
        for v in vals:
            solver.add_conditional_constraint(
                z3.Implies(b[(i, v)], cell_by_i[i] == v),
                condition=bool_distinct,
            )
    
    for v in vals:
        solver.add_conditional_constraint(z3.Not(z3.And(b[(1, v)], b[(2, v)])), condition=bool_distinct)
        solver.add_conditional_constraint(z3.Not(z3.And(b[(1, v)], b[(3, v)])), condition=bool_distinct)
        solver.add_conditional_constraint(z3.Not(z3.And(b[(2, v)], b[(3, v)])), condition=bool_distinct)
    
    # -------------------------
    # bool_pbeq: onehot + PB at-most-one per value (injective)
    # -------------------------
    p = {(i, v): z3.Bool(f"bp_c{i}_is_{v}") for i in [1, 2, 3] for v in vals}
    
    for i in [1, 2, 3]:
        solver.add_conditional_constraint(
            z3.PbEq([(p[(i, v)], 1) for v in vals], 1),
            condition=bool_pbeq,
        )
        for v in vals:
            solver.add_conditional_constraint(
                z3.Implies(p[(i, v)], cell_by_i[i] == v),
                condition=bool_pbeq,
            )
    
    for v in vals:
        solver.add_conditional_constraint(
            z3.PbEq([(p[(i, v)], 1) for i in [1, 2, 3]], 1),
            condition=bool_pbeq,
        )
    
    # -------------------------
    # Global constraints: select family; within family pick exactly one encoding
    # -------------------------
    solver.add_global_constraints(
        z3.PbEq([(use_arith, 1), (use_bool, 1)], 1),
        
        z3.Implies(
            use_arith,
            z3.And(
                z3.PbEq([(arith_distinct, 1), (arith_pbeq, 1)], 1),
                z3.Not(bool_distinct),
                z3.Not(bool_pbeq),
            ),
        ),
        z3.Implies(
            use_bool,
            z3.And(
                z3.PbEq([(bool_distinct, 1), (bool_pbeq, 1)], 1),
                z3.Not(arith_distinct),
                z3.Not(arith_pbeq),
            ),
        ),
    )
    
    return solver, (cell1, cell2, cell3), (arith_distinct, arith_pbeq, bool_distinct, bool_pbeq), (use_arith, use_bool)


def test_cv_runs_cells3_force_arith_two_runs_golden():
    """
    Forces use_arith, so the meta-solver must pick either:
      - arith_distinct=True, arith_pbeq=False, bool_* = False
      - arith_distinct=False, arith_pbeq=True, bool_* = False

    Query uses assumptions (so SMT2 should contain check-sat-assuming):
      cell1 == 1, cell2 == 2   => implies cell3 == 3
    """
    solver, (cell1, cell2, cell3), cvs, (use_arith,
                                         use_bool) = _build_solver_3cellsfour_encodings_arith_bool_distinct_pbeq()
    
    assert solver.check_conditional_constraints(cell1 == 1, cell2 == 2, condition=use_arith, max_count=10) == z3.sat
    
    runs = solver.get_runs()
    assert len(runs) == 2
    
    for r in runs:
        assert set(r.assignment.keys()) == {"arith_distinct", "arith_pbeq", "bool_distinct", "bool_pbeq"}
        assert r.assignment["bool_distinct"] is False
        assert r.assignment["bool_pbeq"] is False
        assert (r.assignment["arith_distinct"], r.assignment["arith_pbeq"]) in {(True, False), (False, True)}
        assert r.sat == z3.sat
    
    _assert_matches_golden("cv_runs_cells3_force_arith.json", _snapshot_runs_sorted(solver))


def test_cv_runs_cells3_force_bool_two_runs_golden():
    """
    Forces use_bool, so the meta-solver must pick either:
      - bool_distinct=True, bool_pbeq=False, arith_* = False
      - bool_distinct=False, bool_pbeq=True, arith_* = False

    Same assumption query as arith test.
    """
    solver, (cell1, cell2, cell3), cvs, (use_arith,
                                         use_bool) = _build_solver_3cellsfour_encodings_arith_bool_distinct_pbeq()
    
    assert solver.check_conditional_constraints(cell1 == 1, cell2 == 2, condition=use_bool, max_count=10) == z3.sat
    
    runs = solver.get_runs()
    assert len(runs) == 2
    
    for r in runs:
        assert set(r.assignment.keys()) == {"arith_distinct", "arith_pbeq", "bool_distinct", "bool_pbeq"}
        assert r.assignment["arith_distinct"] is False
        assert r.assignment["arith_pbeq"] is False
        assert (r.assignment["bool_distinct"], r.assignment["bool_pbeq"]) in {(True, False), (False, True)}
        assert r.sat == z3.sat
    
    _assert_matches_golden("cv_runs_cells3_force_bool.json", _snapshot_runs_sorted(solver))
