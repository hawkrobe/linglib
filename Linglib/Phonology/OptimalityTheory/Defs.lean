import Linglib.Core.Optimization.Evaluation
import Mathlib.GroupTheory.Perm.Basic

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
* `Ranking n` — a constraint ranking ([prince-2002]'s domination order).

## Main results

* `Tableau.exists_optimal` / `Tableau.optimal_nonempty` — a winner exists.
* `Tableau.mem_optimal_iff` / `Tableau.optimal_subset` — membership facts.
* `Tableau.optimal_eq_singleton_iff` — sole winner ⟺ strict domination.
-/

namespace OptimalityTheory

open Core.Optimization.Evaluation

/-- OT-named alias for `LexMinProblem` — a finite candidate set ranked by a
fixed-length violation profile. -/
abbrev Tableau (C : Type*) [DecidableEq C] (n : Nat) := LexMinProblem C n

variable {C : Type*} [DecidableEq C] {n : Nat}

/-- OT-named alias for `LexMinProblem.IsLexMin` — `c` is a lexicographic
winner of `t`. -/
abbrev Tableau.IsOptimal (t : Tableau C n) (c : C) : Prop :=
  LexMinProblem.IsLexMin t c

/-- OT-named alias for `LexMinProblem.lexMins` — the winning candidates. -/
abbrev Tableau.optimal (t : Tableau C n) : Finset C :=
  LexMinProblem.lexMins t

/-- OT-named alias for `LexMinProblem.exists_lexMin`. -/
theorem Tableau.exists_optimal (t : Tableau C n) : ∃ c, t.IsOptimal c :=
  LexMinProblem.exists_lexMin t

/-- OT-named alias for `LexMinProblem.mem_lexMins_iff`. -/
theorem Tableau.mem_optimal_iff (t : Tableau C n) (c : C) :
    c ∈ t.optimal ↔ t.IsOptimal c :=
  LexMinProblem.mem_lexMins_iff t c

/-- OT-named alias for `LexMinProblem.lexMins_nonempty`. -/
theorem Tableau.optimal_nonempty (t : Tableau C n) : t.optimal.Nonempty :=
  LexMinProblem.lexMins_nonempty t

/-- OT-named alias for `LexMinProblem.lexMins_subset`. -/
theorem Tableau.optimal_subset (t : Tableau C n) (c : C) :
    c ∈ t.optimal → c ∈ t.candidates :=
  LexMinProblem.lexMins_subset t c

/-- A tableau has sole winner `m` iff `m` strictly lex-dominates every other
candidate. -/
theorem Tableau.optimal_eq_singleton_iff (t : Tableau C n) {m : C}
    (hm : m ∈ t.candidates) :
    t.optimal = {m} ↔ ∀ c ∈ t.candidates, c ≠ m → t.profile m < t.profile c := by
  constructor
  · intro h c hc hcm
    have hmin : ∀ d ∈ t.candidates, t.profile m ≤ t.profile d :=
      ((t.mem_optimal_iff m).mp (h ▸ Finset.mem_singleton_self m)).2
    rcases lt_or_eq_of_le (hmin c hc) with hlt | heq
    · exact hlt
    · exact absurd (Finset.mem_singleton.mp (h ▸ (t.mem_optimal_iff c).mpr
        ⟨hc, fun d hd => heq ▸ hmin d hd⟩)) hcm
  · intro h
    refine Finset.eq_singleton_iff_unique_mem.mpr
      ⟨(t.mem_optimal_iff m).mpr ⟨hm, fun d hd => ?_⟩, fun c hc => ?_⟩
    · rcases eq_or_ne d m with rfl | hdm
      · exact le_refl _
      · exact (h d hd hdm).le
    · by_contra hcm
      exact absurd ((h c ((t.mem_optimal_iff c).mp hc).1 hcm).trans_le
        (((t.mem_optimal_iff c).mp hc).2 m hm)) (lt_irrefl _)

/-- A constraint ranking: a permutation of `Fin n` ([prince-2002]'s total
domination order `≫`). `r i` is the constraint at rank position `i` (position
`0` is most dominant); `r.symm k` is the rank position of `k`. -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Fin n)

end OptimalityTheory
