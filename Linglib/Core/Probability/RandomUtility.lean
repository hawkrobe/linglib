module

public import Linglib.Core.Probability.Distributions.Gaussian

/-!
# Binary Gaussian random utility model (probit choice)

The closed-form binary choice probability of a Gaussian random utility model:
when two alternatives' utilities differ by `Δ` and the *difference* of their
i.i.d. Gaussian perturbations has standard deviation `σ`, the probability of
choosing the first is `Φ(Δ / σ)`, where `Φ` is the standard normal CDF
(`ProbabilityTheory.normalCDF`). Equivalently it is `P(X > 0)` for `X ~ N(Δ, σ²)`
(`gaussianReal_real_Ioi_zero`).

This is the **probit** choice rule — the Gaussian sibling of the **logit**
(softmax) choice rule that arises from Gumbel noise (`rumMaxProb_gumbel_eq_softmax`
in `Core/Probability/Choice/GumbelLuce.lean`). `rumMaxProb` below is the shared
n-ary carrier both noise families instantiate.
It is the shared, domain-neutral core that [thurstone-1927]'s Case V model of
discriminal processes (`Core.ThurstoneCaseV`, psychophysics) and Noisy Harmonic
Grammar ([boersma-pater-2016], phonology) both *instantiate*: neither depends on
the other; each applies this one fact about the normal CDF.

`[UPSTREAM]`: Mathlib has the Gaussian *measure* (`gaussianReal`) and a *generic*
CDF (`ProbabilityTheory.cdf`), but no standard-normal CDF `Φ` (supplied by
`ProbabilityTheory.normalCDF`), no error function, and no random-utility / choice layer (this
file). The grounding chain `gaussianChoiceProb → normalCDF → cdf (gaussianReal 0 1)`
bottoms out in Mathlib's measure-theoretic Gaussian.

## Main results

* `gaussianChoiceProb` — the probit choice probability `Φ(Δ / σ)`.
* `gaussianChoiceProb_complement` — `P(Δ) + P(-Δ) = 1`.
* `gaussianChoiceProb_strictMono` — strictly increasing in the utility gap (for `σ > 0`).
-/

@[expose] public section

namespace Core

open Real MeasureTheory ProbabilityTheory

variable {Δ σ : ℝ}

/-- Binary choice probability of a Gaussian random utility model: `Φ(Δ / σ)`,
where `Δ` is the utility gap between the two alternatives and `σ` is the standard
deviation of the Gaussian noise on their difference. Equivalently `P(X > 0)` for
`X ~ N(Δ, σ²)` — the probit choice rule. -/
noncomputable def gaussianChoiceProb (Δ σ : ℝ) : ℝ :=
  normalCDF (Δ / σ)

/-- The probit choice probability is the mass a Gaussian with mean `Δ` and standard deviation
`σ` gives to the positive half-line. -/
theorem gaussianReal_real_Ioi_zero (Δ : ℝ) (hσ : 0 < σ) :
    (gaussianReal Δ (.mk (σ ^ 2) (sq_nonneg σ))).real (Set.Ioi 0) = gaussianChoiceProb Δ σ := by
  have hv : NNReal.mk (σ ^ 2) (sq_nonneg σ) ≠ 0 := by simp [← NNReal.coe_eq_zero, hσ.ne']
  simp only [gaussianReal_real_Ioi Δ hv, NNReal.coe_mk, sqrt_sq hσ.le, sub_zero,
    gaussianChoiceProb]

@[simp]
theorem gaussianChoiceProb_zero (σ : ℝ) : gaussianChoiceProb 0 σ = 2⁻¹ := by
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
theorem inv_two_lt_gaussianChoiceProb (hΔ : 0 < Δ) (hσ : 0 < σ) :
    2⁻¹ < gaussianChoiceProb Δ σ :=
  inv_two_lt_normalCDF_iff.2 (div_pos hΔ hσ)

/-- A negative utility gap is chosen less often than chance (for `σ > 0`). -/
theorem gaussianChoiceProb_lt_inv_two (hΔ : Δ < 0) (hσ : 0 < σ) :
    gaussianChoiceProb Δ σ < 2⁻¹ :=
  normalCDF_lt_inv_two_iff.2 (div_neg_of_neg_of_pos hΔ hσ)

/-- The choice probability is strictly increasing in the utility gap (for `σ > 0`). -/
theorem gaussianChoiceProb_strictMono (hσ : 0 < σ) :
    StrictMono (fun Δ ↦ gaussianChoiceProb Δ σ) :=
  fun _ _ h ↦ normalCDF_strictMono (div_lt_div_of_pos_right h hσ)

/-! ### The n-ary max-probability integral -/

open MeasureTheory in
/-- The max-probability integral of a random utility model with i.i.d. noise:
the density formula `∫ pdf(x - uᵢ) · ∏_{j≠i} cdf(x - uⱼ) dx` for the event that
alternative `i` attains the maximum utility `uᵢ + εᵢ`. The Gumbel instance
evaluates to softmax (`rumMaxProb_gumbel_eq_softmax`); the Gaussian instance is
the n-ary Thurstone model. -/
noncomputable def rumMaxProb {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pdf cdf : ℝ → ℝ) (u : ι → ℝ) (i : ι) : ℝ :=
  ∫ x : ℝ, pdf (x - u i) * ∏ j ∈ Finset.univ.erase i, cdf (x - u j)

end Core
