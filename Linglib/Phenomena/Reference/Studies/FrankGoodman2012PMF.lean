import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Phenomena.Reference.Studies.FrankGoodman2012
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{frank-goodman-2012} on the unbundled `RSA.Op` API (Phase 2 pilot)
@cite{frank-goodman-2012}

Phase 2 of the RSA → mathlib-PMF migration. This file re-builds the
@cite{frank-goodman-2012} reference game on the `RSA/Operators.lean` API
(`L0OfMeaning`, `S1Belief`, `L1`) — alongside the existing `RSAConfig`
formulation in `FrankGoodman2012.lean`, not as a replacement.

The point is twofold:

1. **The API is usable.** Constructing L0/S1/L1 via the unbundled operators
   on a real linguistic model works without contortions.
2. **Free mathlib theorems.** Properties like the support characterisation
   `mem_support_L1_iff` and the grounding identity `L1 = PMF.posterior`
   transfer to the model as one-liners (no separate proofs needed —
   the theorems lift directly from `Core/Probability/PMFPosterior.lean`).

Phase 4 (extending `rsa_predict` to ENNReal/PMF) is what enables migrating
the comparative L1 inequalities (`L1 .square .blue_square > L1 .square .green_square`)
that this file does *not* attempt to re-prove. Those continue to use the
bundled `RSAConfig.L1` in the sibling `FrankGoodman2012.lean`.

## Reused from `FrankGoodman2012.lean`

* `Object` — the three reference-game objects
* `Feature` — the four feature words
* `Feature.appliesTo` — the Boolean denotation matrix

## New here

* `meaning : Feature → Object → ℝ≥0∞` — ENNReal-valued meaning function
* `L0`, `S1`, `L1` — built from `RSA.L0OfMeaning` / `S1Belief` / `L1`
* `worldPrior := PMF.uniformOfFintype Object` — uniform prior
* `L1_eq_posterior` — grounding theorem (proof: `rfl`)
* `mem_support_L1_iff_apply` — support characterisation (proof: delegates)
-/

set_option autoImplicit false

namespace FrankGoodman2012.PMF

open scoped ENNReal
open RSA FrankGoodman2012

/-! ## ENNReal-valued meaning -/

/-- `meaning u w = 1` if `u` applies to `w`, else `0`. ENNReal-valued so it
plugs into `RSA.L0OfMeaning` directly. -/
noncomputable def meaning (u : Feature) (w : Object) : ℝ≥0∞ :=
  if u.appliesTo w then 1 else 0

theorem meaning_ne_top (u : Feature) (w : Object) : meaning u w ≠ ∞ := by
  unfold meaning; cases u.appliesTo w <;> simp

theorem meaning_pos_of_appliesTo {u : Feature} {w : Object}
    (h : u.appliesTo w = true) : meaning u w ≠ 0 := by
  unfold meaning; rw [h]; simp

/-! ## Positivity / finiteness on `meaning` -/

/-- Each feature applies to at least one object — so `L0OfMeaning` is well-defined. -/
theorem meaning_sum_ne_zero (u : Feature) : ∑' w, meaning u w ≠ 0 := by
  intro h
  rw [ENNReal.tsum_eq_zero] at h
  cases u
  · exact meaning_pos_of_appliesTo (u := .blue) (w := .blue_square) rfl (h .blue_square)
  · exact meaning_pos_of_appliesTo (u := .green) (w := .green_square) rfl (h .green_square)
  · exact meaning_pos_of_appliesTo (u := .square) (w := .blue_square) rfl (h .blue_square)
  · exact meaning_pos_of_appliesTo (u := .circle) (w := .blue_circle) rfl (h .blue_circle)

theorem meaning_sum_ne_top (u : Feature) : ∑' w, meaning u w ≠ ∞ := by
  rw [tsum_eq_sum (s := Finset.univ)
    (fun w (h : w ∉ Finset.univ) => absurd (Finset.mem_univ w) h)]
  exact ENNReal.sum_ne_top.mpr fun w _ => meaning_ne_top u w

/-! ## L0 — literal listener -/

/-- L0 from the meaning function. Each utterance picks out a PMF over objects
proportional to where it's true. -/
noncomputable def L0 (u : Feature) : PMF Object :=
  L0OfMeaning meaning u (meaning_sum_ne_zero u) (meaning_sum_ne_top u)

/-! ## Positivity / finiteness on the speaker numerator -/

/-- For each world, some utterance has positive L0 there — so `S1Belief` is
well-defined. (For α = 1 and unit cost, the speaker numerator is just `L0`.) -/
theorem S1_sum_ne_zero (w : Object) :
    ∑' u, (L0 u w : ℝ≥0∞) ^ (1 : ℝ) * 1 ≠ 0 := by
  intro h
  rw [ENNReal.tsum_eq_zero] at h
  -- For each world, exhibit a true utterance and derive contradiction.
  have hL0_pos : ∀ u : Feature, u.appliesTo w = true → (L0 u w : ℝ≥0∞) ≠ 0 := by
    intro u happ
    rw [L0, L0OfMeaning_apply]
    refine mul_ne_zero (meaning_pos_of_appliesTo happ) ?_
    rw [ne_eq, ENNReal.inv_eq_zero]
    exact meaning_sum_ne_top u
  cases w with
  | blue_square =>
    have hu := h .blue
    rw [ENNReal.rpow_one, mul_one] at hu
    exact hL0_pos .blue rfl hu
  | blue_circle =>
    have hu := h .blue
    rw [ENNReal.rpow_one, mul_one] at hu
    exact hL0_pos .blue rfl hu
  | green_square =>
    have hu := h .green
    rw [ENNReal.rpow_one, mul_one] at hu
    exact hL0_pos .green rfl hu

theorem S1_sum_ne_top (w : Object) :
    ∑' u, (L0 u w : ℝ≥0∞) ^ (1 : ℝ) * 1 ≠ ∞ := by
  rw [tsum_eq_sum (s := Finset.univ)
    (fun u (h : u ∉ Finset.univ) => absurd (Finset.mem_univ u) h)]
  refine ENNReal.sum_ne_top.mpr fun u _ => ?_
  rw [ENNReal.rpow_one, mul_one]
  exact (lt_of_le_of_lt (PMF.coe_le_one _ _) ENNReal.one_lt_top).ne

/-! ## S1 — pragmatic speaker -/

/-- S1 with α = 1 and unit cost. -/
noncomputable def S1 (w : Object) : PMF Feature :=
  S1Belief L0 (fun _ => 1) 1 w (S1_sum_ne_zero w) (S1_sum_ne_top w)

/-! ## Uniform world prior -/

/-- Uniform prior over the three objects. -/
noncomputable def worldPrior : PMF Object := PMF.uniformOfFintype Object

/-! ## L1 — pragmatic listener -/

/-- The marginal of an utterance under (`S1`, uniform prior) is non-zero —
so `L1` is well-defined. -/
theorem marginal_ne_zero (u : Feature) :
    PMF.marginal S1 worldPrior u ≠ 0 := by
  intro h
  rw [PMF.marginal, ENNReal.tsum_eq_zero] at h
  -- Uniform prior is positive everywhere.
  have hwp : ∀ w, worldPrior w ≠ 0 := by
    intro w
    rw [worldPrior, PMF.uniformOfFintype_apply]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  -- For each utterance there's a true world; S1 there is positive.
  have hS1_pos_at_truth : ∀ (u : Feature) (w : Object),
      u.appliesTo w = true → S1 w u ≠ 0 := by
    intro u w happ hzero
    rw [S1, S1Belief_apply] at hzero
    -- Either the numerator is zero or the inverse-marginal is zero.
    rcases mul_eq_zero.mp hzero with hnum | hinv
    · rw [ENNReal.rpow_one, mul_one] at hnum
      rw [L0, L0OfMeaning_apply] at hnum
      rcases mul_eq_zero.mp hnum with hm | hms
      · exact meaning_pos_of_appliesTo happ hm
      · rw [ENNReal.inv_eq_zero] at hms; exact meaning_sum_ne_top u hms
    · rw [ENNReal.inv_eq_zero] at hinv; exact S1_sum_ne_top w hinv
  cases u with
  | blue =>
    have hw := h .blue_square
    rcases mul_eq_zero.mp hw with hp | hs
    · exact hwp _ hp
    · exact hS1_pos_at_truth .blue .blue_square rfl hs
  | green =>
    have hw := h .green_square
    rcases mul_eq_zero.mp hw with hp | hs
    · exact hwp _ hp
    · exact hS1_pos_at_truth .green .green_square rfl hs
  | square =>
    have hw := h .blue_square
    rcases mul_eq_zero.mp hw with hp | hs
    · exact hwp _ hp
    · exact hS1_pos_at_truth .square .blue_square rfl hs
  | circle =>
    have hw := h .blue_circle
    rcases mul_eq_zero.mp hw with hp | hs
    · exact hwp _ hp
    · exact hS1_pos_at_truth .circle .blue_circle rfl hs

/-- Pragmatic listener — *defined* as `PMF.posterior` of the speaker kernel
against the world prior. -/
noncomputable def L1 (u : Feature) : PMF Object :=
  RSA.L1 S1 worldPrior u (marginal_ne_zero u)

/-! ## The grounding payoff: free mathlib theorems -/

/-- L1 IS Bayesian inversion of S1 against the world prior. True by
construction — the unbundled API doesn't redefine Bayes' rule, it forwards
to `PMF.posterior`. Compare to a bundled approach which would require a
bridge proof reconciling `cfg.L1` with `PMF.posterior`. -/
theorem L1_eq_posterior (u : Feature) :
    L1 u = PMF.posterior S1 worldPrior u (marginal_ne_zero u) := rfl

/-- Support of L1 at `u` = worlds with positive prior and positive speaker
mass for `u`. One-line lift of `RSA.mem_support_L1_iff`. -/
theorem mem_support_L1_iff_apply (u : Feature) (w : Object) :
    w ∈ (L1 u).support ↔ worldPrior w ≠ 0 ∧ S1 w u ≠ 0 :=
  mem_support_L1_iff S1 worldPrior u (marginal_ne_zero u) w

/-- Bayes identity in product form: `marginal · L1 = prior · speaker`.
One-line lift of `RSA.marginal_mul_L1_apply`. -/
theorem marginal_mul_L1_apply (u : Feature) (w : Object) :
    PMF.marginal S1 worldPrior u * L1 u w = worldPrior w * S1 w u :=
  RSA.marginal_mul_L1_apply S1 worldPrior u (marginal_ne_zero u) w

end FrankGoodman2012.PMF
