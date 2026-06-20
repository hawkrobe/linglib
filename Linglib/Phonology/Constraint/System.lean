import Linglib.Core.Optimization.System
import Linglib.Phonology.Constraint.Weighted
import Linglib.Core.Optimization.Profile
import Linglib.Phonology.Constraint.Defs
import Linglib.Phonology.OptimalityTheory.Optimality

/-!
# Constraint Systems — OT/HG/MaxEnt instantiations of `Core.Optimization.ConstraintSystem`

The framework-neutral `ConstraintSystem` record + `predict` machinery
lives in `Core/Optimization/System.lean`. This file packages the
linguistic constraint-based grammar instantiations as smart constructors:

  - `otSystem`     — OT: `Score = LexProfile Nat n`, decoder = `argminDecoder`
  - `hgSystem`     — HG: `Score = ℝ`, decoder = `argmaxDecoder`
  - `maxEntSystem` — MaxEnt: `Score = ℝ`, decoder = `softmaxDecoder α`

Stochastic frameworks that put noise on weights or candidates (NHG,
Normal MaxEnt, Stochastic OT) are RUM specializations: the noise kernel
composes with the deterministic decoder. See `NoiseKernel.lean`.

A `tableauSystem` bridge view shows that the established `Tableau` API
is `argminDecoder` over a `LexProfile Nat n` score in disguise.
-/

namespace Constraint

open Core.Optimization

-- ============================================================================
-- § 1: Smart Constructors
-- ============================================================================

/-- Build an Optimality Theory system: lexicographic minimum on a violation
    profile. The candidate set must be finite; `profile c` gives the
    `n`-tuple of constraint violations for candidate `c` ranked in
    order of dominance.

    Equivalent to choosing the OT winner(s) by `argmin` on the lex order. -/
noncomputable def otSystem {Cand : Type*} {n : Nat}
    (candidates : Finset Cand) (profile : Cand → LexProfile Nat n) :
    ConstraintSystem Cand (LexProfile Nat n) where
  candidates := candidates
  score := profile
  decoder := argminDecoder

/-- Build a (deterministic) Harmonic Grammar system: real-valued harmony
    score, choose the candidate(s) that maximise it.

    The harmony score is `harmonyScoreR constraints c = -Σⱼ wⱼ · Cⱼ(c)`.
    Higher harmony = lower (weighted) violation = more grammatical. -/
noncomputable def hgSystem {Cand : Type*}
    (candidates : Finset Cand) (constraints : List (WeightedConstraint Cand)) :
    ConstraintSystem Cand ℝ where
  candidates := candidates
  score := harmonyScoreR constraints
  decoder := argmaxDecoder

/-- Build a MaxEnt Harmonic Grammar system: same harmony score as `hgSystem`,
    but soft-decode with temperature `α`. As `α → ∞`, this converges to
    `hgSystem` (see `softmax_argmax_limit` in `Core.Agent.RationalAction`).

    The default `α = 1` matches [goldwater-johnson-2003]'s
    standard MaxEnt formulation. -/
noncomputable def maxEntSystem {Cand : Type*}
    (candidates : Finset Cand) (constraints : List (WeightedConstraint Cand))
    (α : ℝ := 1) :
    ConstraintSystem Cand ℝ where
  candidates := candidates
  score := harmonyScoreR constraints
  decoder := softmaxDecoder α

-- ============================================================================
-- § 2: Tableau Bridge
-- ============================================================================

/-! `Constraint.Tableau` is the established study-file API for
OT (used by `mkTableau ... .optimal = {winner}` patterns). The bridge below
shows that `Tableau` is a special case of `ConstraintSystem`: the OT score
`profile : C → ViolationProfile n` is exactly a `LexProfile Nat n`-valued
score (definitionally), and `Tableau.optimal` is exactly the support of the
`argminDecoder` distribution. So existing OT studies can keep their
`Tableau`/`optimal` formulation and additionally expose the unified
`ConstraintSystem.predict` view via `tableauSystem`. -/

open Core.Optimization.Evaluation
open Constraint OptimalityTheory

/-- An OT tableau viewed as a generic `ConstraintSystem`. The score type
    `LexProfile Nat n` is definitionally `ViolationProfile n`, so the
    `argminDecoder`'s `LinearOrder` requirement is satisfied by the
    standard `Pi.Lex` instance. -/
noncomputable def tableauSystem {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) : ConstraintSystem C (LexProfile Nat n) where
  candidates := t.candidates
  score := t.profile
  decoder := argminDecoder

/-- The unifying identity: `tableauSystem`'s prediction is uniform over
    `Tableau.optimal`. Since `Tableau.optimal` IS the argmin filter set
    by definition, the `argminDecoder` reduces to the standard "uniform
    over winners" formula. All other bridge results follow. -/
theorem tableauSystem_predict_eq {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (c : C) :
    (tableauSystem t).predict c =
      (if c ∈ t.optimal then ((t.optimal.card : ℝ))⁻¹ else 0) := by
  have hfilter : t.optimal = (t.candidates.filter
      (fun c' => ∀ c'' ∈ t.candidates, t.profile c' ≤ t.profile c'')) := by
    ext x
    simp only [Finset.mem_filter, LexMinProblem.lexMins]
  show argminDecoder.decode t.candidates t.profile c = _
  unfold argminDecoder
  simp only
  rw [hfilter]
  congr

/-- A candidate is in the support of the `tableauSystem` distribution
    iff it is in the tableau's optimal set. -/
theorem tableauSystem_predict_pos_iff_optimal {C : Type*} [DecidableEq C] {n : Nat}
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
theorem tableauSystem_predict_unique_winner {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (winner : C) (h : t.optimal = {winner}) :
    (tableauSystem t).predict winner = 1 := by
  rw [tableauSystem_predict_eq, h]; simp

/-- And losers in a unique-winner tableau receive probability 0. -/
theorem tableauSystem_predict_loser {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (winner loser : C) (hne : loser ≠ winner)
    (h : t.optimal = {winner}) :
    (tableauSystem t).predict loser = 0 := by
  rw [tableauSystem_predict_eq, h]; simp [hne]

end Constraint
