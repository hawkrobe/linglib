import Linglib.Core.Optimization.Evaluation
import Linglib.Core.Optimization.System
import Linglib.Core.Optimization.Profile
import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Tableaux as Constraint Systems

The OT-specific `predict` view: a `Tableau` is an `argminDecoder` over a
`ViolationProfile`-valued score, i.e. a `Core.Optimization.ConstraintSystem`.
This is the OT counterpart of the Harmonic-Grammar `ConstraintSystem` (a
`softmaxDecoder` over `harmonyScore con w`, built inline in HG study files),
kept on the OT layer so the neutral `Core.Optimization` machinery stays
independent of the `Tableau` API.

A study file can keep its `Tableau`/`optimal` formulation and additionally
expose the unified `ConstraintSystem.predict` distribution via `tableauSystem`.

## Main definitions

* `tableauSystem` — an OT tableau viewed as a generic `ConstraintSystem`.

## Main results

* `tableauSystem_predict_eq` — `predict` is uniform over `Tableau.optimal`.
* `tableauSystem_predict_unique_winner` / `tableauSystem_predict_loser` —
  the deterministic (single-winner) specialisations used in study files.
-/

namespace OptimalityTheory

open Core.Optimization
open Core.Optimization.Evaluation

variable {C : Type*} [DecidableEq C] {n : Nat}

/-- An OT tableau viewed as a generic `ConstraintSystem`. The score type
    `LexProfile Nat n` is definitionally `ViolationProfile n`, so the
    `argminDecoder`'s `LinearOrder` requirement is satisfied by the
    standard `Pi.Lex` instance. -/
noncomputable def tableauSystem
    (t : Tableau C n) : ConstraintSystem C (LexProfile Nat n) where
  candidates := t.candidates
  score := t.profile
  decoder := argminDecoder

/-- The unifying identity: `tableauSystem`'s prediction is uniform over
    `Tableau.optimal`. Since `Tableau.optimal` IS the argmin filter set
    by definition, the `argminDecoder` reduces to the standard "uniform
    over winners" formula. All other bridge results follow. -/
theorem tableauSystem_predict_eq
    (t : Tableau C n) (c : C) :
    (tableauSystem t).predict c =
      (if c ∈ t.optimal then ((t.optimal.card : ℝ))⁻¹ else 0) := by
  have hfilter : t.optimal = (t.candidates.filter
      (fun c' => ∀ c'' ∈ t.candidates, t.profile c' ≤ t.profile c'')) := by
    ext x
    simp only [Finset.mem_filter, LexMinProblem.lexMins, argMinSet]
  show argminDecoder.decode t.candidates t.profile c = _
  unfold argminDecoder
  simp only
  rw [hfilter]
  congr

/-- A candidate is in the support of the `tableauSystem` distribution
    iff it is in the tableau's optimal set. -/
theorem tableauSystem_predict_pos_iff_optimal
    (t : Tableau C n) (c : C) :
    0 < (tableauSystem t).predict c ↔ c ∈ t.optimal := by
  rw [tableauSystem_predict_eq]
  by_cases hc : c ∈ t.optimal
  · have hcard : 0 < (t.optimal.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨c, hc⟩)
    simp [hc, inv_pos.mpr hcard]
  · simp [hc]

/-- When `Tableau.optimal = {winner}` (the typical deterministic-OT pattern
    used in study files via `by decide`), the unified `predict` view assigns
    probability 1 to the winner. -/
theorem tableauSystem_predict_unique_winner
    (t : Tableau C n) (winner : C) (h : t.optimal = {winner}) :
    (tableauSystem t).predict winner = 1 := by
  rw [tableauSystem_predict_eq, h]; simp

/-- And losers in a unique-winner tableau receive probability 0. -/
theorem tableauSystem_predict_loser
    (t : Tableau C n) (winner loser : C) (hne : loser ≠ winner)
    (h : t.optimal = {winner}) :
    (tableauSystem t).predict loser = 0 := by
  rw [tableauSystem_predict_eq, h]; simp [hne]

end OptimalityTheory
