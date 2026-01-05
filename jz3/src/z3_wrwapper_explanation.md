 ## Purpose

`z3_wrapper.py` file defines a **Z3 Solver wrapper** (`class Solver`) that lets you:

1. Register multiple alternative **encodings** of the same logical requirement (e.g., Sudoku “all-different” via `Distinct` vs `PbEq`), and guard each alternative behind a **Condition Variable (CV)**.

2. Add **global constraints over CVs** (a “meta-configuration space”), so Z3 can pick a consistent CV assignment.

3. Run a **two-layer solving workflow**:

* **Meta-solver layer:** picks a satisfying CV assignment under the global CV constraints.
* **Inner solver layer:** materializes only the constraints whose CVs are enabled, and calls `check()` on the actual problem.

4. Optionally **benchmark** multiple CV assignments, generating per-assignment SMT2 and running other SMT solvers via `run_solvers`.

5. Record solver actions so you can emit a mostly-replayable **SMT-LIB script**.

---

## Key components

### `InequivalentConditionalConstraints`

A custom warning category used when different CV assignments lead to different SAT/UNSAT outcomes (a strong indicator your “alternative encodings” are not equivalent). 

---

## `class Solver(z3.Solver)`

### Internal state (high level)

* `__assertions`: list of `(constraint, cv)` pairs. These are “conditional constraints” guarded by CVs. 
* `__CVs`: set of valid CVs (atomic Bool variables only; `True` is not stored). 
* `__global_constraints`: conjunction of constraints that restrict legal CV assignments (meta rules). 
* Recording: `__start_recording`, `__history`, `generate_smtlib()` implement the SMT2 logging/replay functionality. 
* Benchmark outputs: `__condition_var_assignment_model`, `__solvers_results_for_different_conditional_variables`. 

### Safety guard: `__getattribute__`

Warns if callers use methods outside an allowlist, because those operations might not be captured in SMT2 history and could introduce “recording mismatch” bugs. 

---

## Configuration APIs

### `add_global_constraints(*constraints)`

Accumulates constraints that define the valid “space” of CV assignments. Think: “exactly one encoding enabled”, “these two flags cannot both be true”, etc. 

### `add_conditional_constraint(*constraints, condition=...)`

Registers one or more constraints guarded by a CV.

Important invariants enforced:

* `condition` must be either `True` or an **atomic Bool variable** (not `And(...)`, not `Or(...)`). 
* Non-`True` CVs are added to `__CVs` for enumeration/blocking.
* It sanity-checks that the global CV constraint system is satisfiable. 

---

## Shared helper utilities

### `_eval_bool(model, b)`

Evaluates a BoolRef in a model using model completion. Used to interpret CV truth values robustly. 

### `_block_model(model, cvs)`

Constructs a blocking clause that prevents the meta-solver from returning the exact same CV assignment again. This enables “enumerate distinct CV assignments.” 

---

## Solving APIs

### `check_conditional_constraints(*args, condition=True, max_count=5)`

This is the “stable / non-hamming” meta-solver method.

What it does:

1. Temporarily registers any extra constraints in `args` guarded by the provided `condition`. 
2. Builds a **meta Z3 solver** that contains:

   * `__global_constraints`
   * plus `condition == True` for this call (so if user asks “check under distinct_cond”, it forces that CV on). 
3. Enumerates distinct CV assignments (no duplicates) by repeatedly:

   * reading a meta-model
   * building a fresh “inner” `Solver()`
   * adding every conditional constraint whose CV is `True` under the meta-model
   * `inner.check()` 
4. In benchmark mode:

   * stores the CV assignment dictionary
   * extracts per-assignment SMT2 (`inner.to_smt2()`)
   * runs external solvers via `run_solvers.run_solvers(...)` and records results 
5. If different CV assignments yield different SAT results, emits `InequivalentConditionalConstraints`. 
6. If recording is enabled, it records the “canonical” (first) chosen constraints into `__history` and later can emit a standalone SMT-LIB program via `generate_smtlib()`. 

### `check_conditional_constraints_hamming(...)`

A second benchmark method that tries to pick CV assignments that are “as different as possible” using an `Optimize()` maximin/min-distance objective (Hamming-distance based). This is kept separate because it is more error-prone. 

---

## Recording and SMT2 emission

### `start_recording()`, `add()`, `push()/pop()`, `check()`

These methods augment normal solver operations by logging a replayable history of:

* asserted formulas
* stack operations
* check-sat calls and results 

### `generate_smtlib()`

Replays `__history` into a concrete SMT-LIB string, currently hardcoding `(set-logic QF_LIA)` and appending assertions / push/pop / check-sat / results as comments. 

---

## Output getters

* `get_condition_var_assignment_model()` returns the recorded CV assignments/models. 
* `get_var_assignments_and_solvers_performance()` returns the per-assignment external solver results in benchmark mode. 

---

## Demo / testing code

### `solver_demo()`

Shows the intended usage pattern with two alternative encodings guarded by `encoding1` and `encoding2`, plus global constraints enforcing exactly one is enabled (`Or(...)` + `Distinct(...)`). Then it calls `check_conditional_constraints()` and prints CV assignments and solver performance. 

### `optimizer_test()`

A standalone example of using `Optimize()` with different objectives (maximize vs minimize number of conditions). It is separate from the main wrapper logic. 
