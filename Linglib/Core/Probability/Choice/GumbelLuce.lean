import Linglib.Core.Probability.Gumbel
import Linglib.Core.Probability.Choice.RandomUtility
import Linglib.Core.Probability.Choice.RationalAction

/-!
# Gumbel–Luce equivalence [mcfadden-1974]

A random utility model assigns each alternative `i` the utility `uᵢ + εᵢ` and
chooses the maximizer; with i.i.d. Gumbel noise the choice probabilities are
exactly softmax, `P(i) = exp(uᵢ/β) / ∑ⱼ exp(uⱼ/β)`. The Gumbel→softmax
direction is due to [marschak-1960] and, in the constructive form given here,
to Holman and Marley (via [luce-suppes-1965]); [mcfadden-1974] proves it as
his Lemma 1 and credits them. McFadden's own contribution is the converse, Lemma 2:
among translation-complete i.i.d. noise distributions only the Gumbel family
yields the Luce rule [luce-1959]. Uniqueness genuinely needs choice sets of
size ≥ 3: for binary choice the logistic form does not pin down Gumbel noise
(Yellott [yellott-1977]; compare the binary probit in
`Core/Probability/Choice/RandomUtility.lean`).

The distribution layer (density, measure, CDF, max-stability, and the
max-probability integral) lives in `Core/Probability/Gumbel.lean`; this file
gives it the random-utility reading.

## Main definitions

* `RationalAction.fromGumbelRUM`: the Luce agent of a Gumbel RUM, defined as
  `fromSoftmax` at inverse temperature `β⁻¹`.

## Main results

* `rumChoiceProb_gumbelMeasure`: Lemma 1 of [mcfadden-1974] — under independent
  Gumbel utilities the choice probabilities are softmax.
* `rumChoiceProb_gumbelMeasure_fin_two`: the binary case is the logistic function.
* `gumbel_from_functional_eq`, `eq_cdf_gumbelMeasure_of_functional_eq`: the
  terminal step of Lemma 2 — a noise CDF satisfying `G(x-c) = G(x)^{exp c}`
  is Gumbel. McFadden derives that equation only for positive-integer `exp c`
  (duplicated alternatives) and extends by monotonicity; the derivation of the
  equation from the softmax form and translation completeness is not
  formalized here.
-/

namespace Core

open Real MeasureTheory Set Filter ProbabilityTheory

section GumbelRUM

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {β : ℝ}

instance (μ β : ℝ) : NullSingletonClass (gumbelMeasure μ β) := by
  unfold gumbelMeasure; infer_instance

/-- **Gumbel RUM ⟹ softmax** (Lemma 1 of [mcfadden-1974], due to Holman and
    Marley via Luce and Suppes): when the utilities are independent with
    `Gumbel(uⱼ, β)` laws, alternative `i` has the highest utility with
    probability `softmax ((1/β) • u) i`.

    [mcfadden-1974] states the unit-scale case; the `β`-generalization is
    standard (the scale of the noise is not separately identified from the
    scale of `u`). -/
theorem rumChoiceProb_gumbelMeasure (u : ι → ℝ) (hβ : 0 < β) (i : ι) :
    rumChoiceProb (fun j ↦ gumbelMeasure (u j) β) i =
      ENNReal.ofReal (softmax ((1 / β) • u) i) := by
  have : ∀ j, IsProbabilityMeasure (gumbelMeasure (u j) β) :=
    fun j ↦ isProbabilityMeasure_gumbelMeasure hβ (u j)
  have hcdf : Measurable fun x ↦ ∏ j ∈ Finset.univ.erase i, cdf (gumbelMeasure (u j) β) x :=
    Finset.measurable_fun_prod _ fun j _ ↦ (monotone_cdf _).measurable
  have hnonneg : ∀ x, 0 ≤ ∏ j ∈ Finset.univ.erase i, cdf (gumbelMeasure (u j) β) x :=
    fun x ↦ Finset.prod_nonneg fun j _ ↦ cdf_nonneg _ x
  have hint : Integrable fun x ↦ gumbelPDFReal (u i) β x *
      ∏ j ∈ Finset.univ.erase i, cdf (gumbelMeasure (u j) β) x :=
    (integrable_gumbelPDFReal hβ (u i)).mul_bdd (c := 1) hcdf.aestronglyMeasurable
      (.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (hnonneg x)]
        exact Finset.prod_le_one₀ (fun j _ ↦ cdf_nonneg _ x) fun j _ ↦ cdf_le_one _ x)
  have hpdf : Measurable (gumbelPDF (u i) β) := (measurable_gumbelPDFReal _ _).ennreal_ofReal
  rw [rumChoiceProb_eq_lintegral_cdf, gumbelMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hpdf hcdf.ennreal_ofReal]
  simp_rw [Pi.mul_apply, gumbelPDF, ← ENNReal.ofReal_mul (gumbelPDFReal_nonneg hβ.le _ _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (.of_forall fun x ↦ mul_nonneg (gumbelPDFReal_nonneg hβ.le _ _) (hnonneg x)),
    integral_gumbelPDFReal_mul_prod_cdf u hβ i]
  simp only [softmax, Pi.smul_apply, smul_eq_mul, one_div_mul_eq_div]

end GumbelRUM

/-! ### Binary case: the logistic function -/

/-- **Binary Gumbel RUM = logistic**: for two alternatives the choice
    probability is `sigmoid ((u 0 - u 1) / β)`. Compare the binary probit
    `rumChoiceProb_gaussianReal`, `Φ((u 0 - u 1)/√(2v))` for Gaussian noise. By
    [yellott-1977] the two are indistinguishable on binary data alone. -/
theorem rumChoiceProb_gumbelMeasure_fin_two (u : Fin 2 → ℝ) {β : ℝ} (hβ : 0 < β) :
    rumChoiceProb (fun j ↦ gumbelMeasure (u j) β) 0 =
      ENNReal.ofReal (Real.sigmoid ((u 0 - u 1) / β)) := by
  rw [rumChoiceProb_gumbelMeasure u hβ 0, softmax_fin_two]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 2; ring

/-! ### The Gumbel RUM as a `RationalAction` -/

section RationalAgent

variable {ι : Type*} [Fintype ι]

/-- The Luce agent of a Gumbel RUM: score `exp(uᵢ/β)`. This is `fromSoftmax`
    at inverse temperature `β⁻¹` — exact under i.i.d. Gumbel(0, β) noise by
    Lemma 1 of [mcfadden-1974], not an approximation. -/
noncomputable def RationalAction.fromGumbelRUM (u : ι → ℝ) (β : ℝ) :
    RationalAction Unit ι :=
  RationalAction.fromSoftmax (fun _ => u) β⁻¹

/-- The Gumbel RUM policy is softmax at inverse temperature `β⁻¹`. -/
theorem RationalAction.fromGumbelRUM_policy [Nonempty ι] (u : ι → ℝ) {β : ℝ} (i : ι) :
    (RationalAction.fromGumbelRUM u β).policy () i = softmax (β⁻¹ • u) i := by
  rw [RationalAction.fromGumbelRUM, RationalAction.fromSoftmax_policy_eq]

end RationalAgent

/-! ### Uniqueness: the terminal step of McFadden's Lemma 2

Lemma 2 of [mcfadden-1974] assumes softmax selection probabilities on every
finite subset of a universe, representative utilities ranging over all of ℝ,
and i.i.d. noise with a *translation complete* CDF `G`; it concludes `G` is
Gumbel. Playing duplicated alternatives off against each other yields
`G(x - log K) = G(x)^K` for positive integers `K`, which extends to the real
functional equation by monotonicity. The theorems below formalize the terminal
step only: solving the (real-strength) functional equation. -/

/-- A noise CDF satisfying `G(x - c) = G(x) ^ exp c` with `0 < G 0` has the
    Gumbel form `G(t) = exp (log (G 0) · exp (-t))`. -/
theorem gumbel_from_functional_eq (G : ℝ → ℝ) (hG0_pos : 0 < G 0)
    (hfe : ∀ x c : ℝ, G (x - c) = (G x) ^ (exp c)) (t : ℝ) :
    G t = exp (log (G 0) * exp (-t)) := by
  have h := hfe 0 (-t)
  simp only [zero_sub, neg_neg] at h
  rw [h, rpow_def_of_pos hG0_pos]

/-- With the nondegeneracy bound `G 0 < 1`, the functional equation pins `G`
    to an honest Gumbel CDF: `G = cdf (gumbelMeasure (log (-log (G 0))) 1)`. -/
theorem eq_cdf_gumbelMeasure_of_functional_eq (G : ℝ → ℝ) (hG0_pos : 0 < G 0)
    (hG0_lt : G 0 < 1) (hfe : ∀ x c : ℝ, G (x - c) = (G x) ^ (exp c)) (t : ℝ) :
    G t = cdf (gumbelMeasure (log (-log (G 0))) 1) t := by
  have hα : 0 < -log (G 0) := neg_pos.mpr (log_neg hG0_pos hG0_lt)
  rw [gumbel_from_functional_eq G hG0_pos hfe t, cdf_gumbelMeasure_eq one_pos]
  congr 1
  rw [div_one, show -(t - log (-log (G 0))) = log (-log (G 0)) + -t from by ring,
    exp_add, exp_log hα]
  ring

end Core
