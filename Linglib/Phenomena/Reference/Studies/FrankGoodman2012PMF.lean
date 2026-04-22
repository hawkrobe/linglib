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
open FrankGoodman2012

/-! ## ENNReal-valued meaning -/

/-- `meaning u w = 1` if `u` applies to `w`, else `0`. ENNReal-valued so it
plugs into `RSA.L0OfMeaning` directly. -/
noncomputable def meaning (u : Feature) (w : Object) : ℝ≥0∞ :=
  if u.appliesTo w then 1 else 0

private theorem meaning_ne_top (u : Feature) (w : Object) : meaning u w ≠ ∞ := by
  unfold meaning
  split_ifs
  · exact ENNReal.one_ne_top
  · exact ENNReal.zero_ne_top

private theorem meaning_ne_zero_of_appliesTo {u : Feature} {w : Object}
    (h : u.appliesTo w = true) : meaning u w ≠ 0 := by
  unfold meaning
  rw [if_pos h]
  exact one_ne_zero

/-! ## Witnesses for positivity

`truthWitness` and `utteranceWitness` are scaffolding that lets the three
positivity lemmas (`meaning_sum_ne_zero`, `S1_sum_ne_zero`, `marginal_ne_zero`)
share the case-by-case "for each X exhibit a Y satisfying P" boilerplate. -/

/-- For each utterance, a world it truthfully applies to. -/
private def truthWitness : Feature → Object
  | .blue => .blue_square
  | .green => .green_square
  | .square => .blue_square
  | .circle => .blue_circle

private theorem appliesTo_truthWitness (u : Feature) :
    u.appliesTo (truthWitness u) = true := by cases u <;> rfl

/-- For each world, an utterance that truthfully applies to it. -/
private def utteranceWitness : Object → Feature
  | .blue_square => .blue
  | .blue_circle => .blue
  | .green_square => .green

private theorem appliesTo_utteranceWitness (w : Object) :
    (utteranceWitness w).appliesTo w = true := by cases w <;> rfl

/-! ## Positivity / finiteness on `meaning` -/

/-- Each feature applies to at least one object — so `L0OfMeaning` is well-defined. -/
private theorem meaning_sum_ne_zero (u : Feature) : ∑' w, meaning u w ≠ 0 := by
  intro h
  rw [ENNReal.tsum_eq_zero] at h
  exact meaning_ne_zero_of_appliesTo (appliesTo_truthWitness u) (h (truthWitness u))

private theorem meaning_sum_ne_top (u : Feature) : ∑' w, meaning u w ≠ ∞ := by
  rw [tsum_eq_sum (s := Finset.univ)
    (fun w (h : w ∉ Finset.univ) => absurd (Finset.mem_univ w) h)]
  exact ENNReal.sum_ne_top.mpr fun w _ => meaning_ne_top u w

/-! ## L0 — literal listener -/

/-- L0 from the meaning function. Each utterance picks out a PMF over objects
proportional to where it's true. -/
noncomputable def L0 (u : Feature) : PMF Object :=
  RSA.L0OfMeaning meaning u (meaning_sum_ne_zero u) (meaning_sum_ne_top u)

/-! ## Positivity / finiteness on the speaker numerator -/

/-- For each world, some utterance has positive L0 there — so `S1Belief` is
well-defined. (For α = 1 and unit cost, the speaker numerator is just `L0`.) -/
private theorem S1_sum_ne_zero (w : Object) :
    ∑' u, (L0 u w : ℝ≥0∞) ^ (1 : ℝ) * 1 ≠ 0 := by
  intro h
  rw [ENNReal.tsum_eq_zero] at h
  have hu := h (utteranceWitness w)
  simp only [ENNReal.rpow_one, mul_one] at hu
  rw [L0, RSA.L0OfMeaning_apply] at hu
  rcases mul_eq_zero.mp hu with hm | hms
  · exact meaning_ne_zero_of_appliesTo (appliesTo_utteranceWitness w) hm
  · rw [ENNReal.inv_eq_zero] at hms
    exact meaning_sum_ne_top (utteranceWitness w) hms

private theorem S1_sum_ne_top (w : Object) :
    ∑' u, (L0 u w : ℝ≥0∞) ^ (1 : ℝ) * 1 ≠ ∞ := by
  rw [tsum_eq_sum (s := Finset.univ)
    (fun u (h : u ∉ Finset.univ) => absurd (Finset.mem_univ u) h)]
  refine ENNReal.sum_ne_top.mpr fun u _ => ?_
  simp only [ENNReal.rpow_one, mul_one]
  exact PMF.apply_ne_top _ _

/-! ## S1 — pragmatic speaker -/

/-- S1 with α = 1 and unit cost. -/
noncomputable def S1 (w : Object) : PMF Feature :=
  RSA.S1Belief L0 (fun _ => 1) 1 w (S1_sum_ne_zero w) (S1_sum_ne_top w)

private theorem S1_ne_zero_of_appliesTo (u : Feature) (w : Object)
    (happ : u.appliesTo w = true) : S1 w u ≠ 0 := by
  intro hzero
  rw [S1, RSA.S1Belief_apply] at hzero
  rcases mul_eq_zero.mp hzero with hnum | hinv
  · simp only [ENNReal.rpow_one, mul_one] at hnum
    rw [L0, RSA.L0OfMeaning_apply] at hnum
    rcases mul_eq_zero.mp hnum with hm | hms
    · exact meaning_ne_zero_of_appliesTo happ hm
    · rw [ENNReal.inv_eq_zero] at hms; exact meaning_sum_ne_top u hms
  · rw [ENNReal.inv_eq_zero] at hinv; exact S1_sum_ne_top w hinv

/-! ## Uniform world prior -/

/-- Uniform prior over the three objects. -/
noncomputable def worldPrior : PMF Object := PMF.uniformOfFintype Object

/-! ## L1 — pragmatic listener -/

/-- The marginal of an utterance under (`S1`, uniform prior) is non-zero —
so `L1` is well-defined. -/
private theorem marginal_ne_zero (u : Feature) :
    PMF.marginal S1 worldPrior u ≠ 0 := by
  intro h
  rw [PMF.marginal, ENNReal.tsum_eq_zero] at h
  have hwp : worldPrior (truthWitness u) ≠ 0 := by
    rw [worldPrior, PMF.uniformOfFintype_apply]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  rcases mul_eq_zero.mp (h (truthWitness u)) with hp | hs
  · exact hwp hp
  · exact S1_ne_zero_of_appliesTo u (truthWitness u) (appliesTo_truthWitness u) hs

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
  RSA.mem_support_L1_iff S1 worldPrior u (marginal_ne_zero u) w

/-- Bayes identity in product form: `marginal · L1 = prior · speaker`.
One-line lift of `RSA.marginal_mul_L1_apply`. -/
theorem marginal_mul_L1_apply (u : Feature) (w : Object) :
    PMF.marginal S1 worldPrior u * L1 u w = worldPrior w * S1 w u :=
  RSA.marginal_mul_L1_apply S1 worldPrior u (marginal_ne_zero u) w

end FrankGoodman2012.PMF
