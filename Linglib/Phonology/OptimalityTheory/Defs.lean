import Linglib.Core.Optimization.Evaluation

/-!
# Tableaux

The OT-specific evaluation vocabulary: a `Tableau` is the lexicographic
minimisation problem `[prince-smolensky-1993]` solves — a finite candidate set
ranked by a `ViolationProfile`-valued objective. These are OT-tradition names
for the `LexMinProblem` engine in `Core.Optimization.Evaluation`; downstream OT
code uses `Tableau`/`Tableau.optimal` rather than the generic spellings.

The violation-profile vocabulary these range over is framework-neutral and
lives in `Constraints.Profile`; the tableau *constructors* and optimality
theorems live in `OptimalityTheory.Basic`.

## Main definitions

* `Tableau C n` — a finite OT tableau over candidates `C` with `n` constraints.
* `Tableau.IsOptimal` — the predicate "candidate is a lexicographic winner".
* `Tableau.optimal` — the `Finset` of winning candidates.

## Main results

* `Tableau.exists_optimal` / `Tableau.optimal_nonempty` — a winner exists.
* `Tableau.mem_optimal_iff` / `Tableau.optimal_subset` — membership facts.
-/

namespace OptimalityTheory

open Core.Optimization.Evaluation

/-- OT-named alias for `LexMinProblem` — a finite candidate set ranked by a
fixed-length violation profile. -/
abbrev Tableau (C : Type*) [DecidableEq C] (n : Nat) := LexMinProblem C n

/-- OT-named alias for `LexMinProblem.IsLexMin` — `c` is a lexicographic
winner of `t`. -/
abbrev Tableau.IsOptimal {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (c : C) : Prop :=
  LexMinProblem.IsLexMin t c

/-- OT-named alias for `LexMinProblem.lexMins` — the winning candidates. -/
abbrev Tableau.optimal {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) : Finset C :=
  LexMinProblem.lexMins t

/-- OT-named alias for `LexMinProblem.exists_lexMin`. -/
theorem Tableau.exists_optimal {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) : ∃ c, t.IsOptimal c :=
  LexMinProblem.exists_lexMin t

/-- OT-named alias for `LexMinProblem.mem_lexMins_iff`. -/
theorem Tableau.mem_optimal_iff {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (c : C) :
    c ∈ t.optimal ↔ t.IsOptimal c :=
  LexMinProblem.mem_lexMins_iff t c

/-- OT-named alias for `LexMinProblem.lexMins_nonempty`. -/
theorem Tableau.optimal_nonempty {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) : t.optimal.Nonempty :=
  LexMinProblem.lexMins_nonempty t

/-- OT-named alias for `LexMinProblem.lexMins_subset`. -/
theorem Tableau.optimal_subset {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (c : C) :
    c ∈ t.optimal → c ∈ t.candidates :=
  LexMinProblem.lexMins_subset t c

end OptimalityTheory
