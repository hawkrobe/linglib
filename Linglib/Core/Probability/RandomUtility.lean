import Linglib.Core.Probability.Gaussian

/-!
# Binary Gaussian random utility model (probit choice)

The closed-form binary choice probability of a Gaussian random utility model:
when two alternatives' utilities differ by `Δ` and the *difference* of their
i.i.d. Gaussian perturbations has standard deviation `σ`, the probability of
choosing the first is `Φ(Δ / σ)`, where `Φ` is the standard normal CDF
(`Core.normalCDF`). Equivalently it is `P(X > 0)` for `X ~ N(Δ, σ²)`.

This is the **probit** choice rule — the Gaussian sibling of the **logit**
(softmax) choice rule that arises from Gumbel noise (`mcfaddenIntegral_binary`).
It is the shared, domain-neutral core that [thurstone-1927]'s Case V model of
discriminal processes (`Core.ThurstoneCaseV`, psychophysics) and Noisy Harmonic
Grammar ([boersma-pater-2016], phonology) both *instantiate*: neither depends on
the other; each applies this one fact about the normal CDF.

`[UPSTREAM]`: Mathlib has the Gaussian *measure* (`gaussianReal`) and a *generic*
CDF (`ProbabilityTheory.cdf`), but no standard-normal CDF `Φ` (supplied by
`Core.normalCDF`), no error function, and no random-utility / choice layer (this
file). The grounding chain `gaussianChoiceProb → normalCDF → cdf (gaussianReal 0 1)`
bottoms out in Mathlib's measure-theoretic Gaussian.

## Main results

* `gaussianChoiceProb` — the probit choice probability `Φ(Δ / σ)`.
* `gaussianChoiceProb_complement` — `P(Δ) + P(-Δ) = 1`.
* `gaussianChoiceProb_strictMono` — strictly increasing in the utility gap (for `σ > 0`).
-/

namespace Core

open Real

variable {Δ σ : ℝ}

/-- Binary choice probability of a Gaussian random utility model: `Φ(Δ / σ)`,
where `Δ` is the utility gap between the two alternatives and `σ` is the standard
deviation of the Gaussian noise on their difference. Equivalently `P(X > 0)` for
`X ~ N(Δ, σ²)` — the probit choice rule. -/
noncomputable def gaussianChoiceProb (Δ σ : ℝ) : ℝ :=
  normalCDF (Δ / σ)

@[simp]
theorem gaussianChoiceProb_zero (σ : ℝ) : gaussianChoiceProb 0 σ = 1 / 2 := by
  simp only [gaussianChoiceProb, zero_div, normalCDF_zero]

/-- The probit choice probability is strictly positive. -/
theorem gaussianChoiceProb_pos (Δ σ : ℝ) : 0 < gaussianChoiceProb Δ σ :=
  normalCDF_pos _

/-- The probit choice probability is strictly less than one. -/
theorem gaussianChoiceProb_lt_one (Δ σ : ℝ) : gaussianChoiceProb Δ σ < 1 :=
  normalCDF_lt_one _

/-- Complementarity: choosing the first alternative or the second is certain. -/
theorem gaussianChoiceProb_complement (Δ σ : ℝ) :
    gaussianChoiceProb Δ σ + gaussianChoiceProb (-Δ) σ = 1 := by
  simp only [gaussianChoiceProb, neg_div, normalCDF_neg]; ring

/-- A positive utility gap is chosen more often than chance (for `σ > 0`). -/
theorem half_lt_gaussianChoiceProb (hΔ : 0 < Δ) (hσ : 0 < σ) :
    1 / 2 < gaussianChoiceProb Δ σ :=
  normalCDF_pos_gt_half (div_pos hΔ hσ)

/-- A negative utility gap is chosen less often than chance (for `σ > 0`). -/
theorem gaussianChoiceProb_lt_half (hΔ : Δ < 0) (hσ : 0 < σ) :
    gaussianChoiceProb Δ σ < 1 / 2 :=
  normalCDF_neg_lt_half (div_neg_of_neg_of_pos hΔ hσ)

/-- The choice probability is strictly increasing in the utility gap (for `σ > 0`). -/
theorem gaussianChoiceProb_strictMono (hσ : 0 < σ) :
    StrictMono (fun Δ => gaussianChoiceProb Δ σ) := by
  intro a b h
  simp only [gaussianChoiceProb]
  exact normalCDF_strictMono (div_lt_div_of_pos_right h hσ)

end Core
