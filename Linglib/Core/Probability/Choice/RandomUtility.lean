/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Constructions.Pi
public import Linglib.Core.Probability.Distributions.Gaussian
public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Random utility models

In a random utility model the alternatives `j : ι` have independent real-valued utilities with laws
`ν j`, and the alternative with the highest utility is chosen. The choice probability of `i` is the
mass that the product measure `Measure.pi ν` gives to the event that coordinate `i` is the strict
maximum. The additive model, with utility `u j + ε j` for a systematic part `u j` and noise `ε j`,
is the case where `ν` is a location family.

The theory here is independent of the noise family. Disintegrating the product measure along
coordinate `i` writes the choice probability as the integral against `ν i` of the product of the
other coordinates' distribution functions. For atomless noise ties are null, so the choice
probabilities of the alternatives sum to one. Gumbel noise gives the logit rule
(`Linglib/Core/Probability/Choice/GumbelLuce.lean`), and Gaussian noise gives the probit rule, whose
binary case is computed here from the convolution of two Gaussians.

## Main definitions

* `ProbabilityTheory.rumChoiceProb`: the probability that alternative `i` has the highest utility.
* `ProbabilityTheory.gaussianChoiceProb`: the binary probit choice probability `Φ (Δ / σ)`.

## Main results

* `ProbabilityTheory.rumChoiceProb_eq_lintegral`: the choice probability as an integral against
  `ν i`.
* `ProbabilityTheory.sum_rumChoiceProb`: for atomless noise the choice probabilities sum to one.
* `ProbabilityTheory.rumChoiceProb_gaussianReal`: two alternatives with independent Gaussian
  utilities of common variance `v` have choice probability `Φ ((u 0 - u 1) / √(2 * v))`.

## TODO

`gaussianChoiceProb` is the closed form `Φ (Δ / σ)` for every real `σ`, so at `σ ≤ 0` it is a junk
value and not the mass of a Gaussian tail. Defining it as `(gaussianReal Δ (σ ^ 2)).real (Ioi 0)`
would give deterministic choice at `σ = 0`, at the cost of positivity hypotheses in the consumers.

## References

* [L. L. Thurstone, *A law of comparative judgment* (1927)][thurstone-1927]
* [D. McFadden, *Conditional logit analysis of qualitative choice behavior* (1974)][mcfadden-1974]
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-! ### Choice probabilities -/

section ChoiceProb

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The choice probability of alternative `i` in the random utility model whose utilities are
independent with laws `ν j`: the probability that coordinate `i` is the strict maximum. -/
noncomputable def rumChoiceProb (ν : ι → Measure ℝ) (i : ι) : ℝ≥0∞ :=
  Measure.pi ν {x | ∀ j, j ≠ i → x j < x i}

/-- The choice probability of `i` is the integral, against the law of the `i`-th utility, of the
probability that every other utility falls below it. -/
theorem rumChoiceProb_eq_lintegral (ν : ι → Measure ℝ) [∀ j, SigmaFinite (ν j)] (i : ι) :
    rumChoiceProb ν i = ∫⁻ x, ∏ j ∈ univ.erase i, ν j (Iio x) ∂ν i :=
  Measure.pi_setOf_forall_ne_mem ν i (s := fun _ x ↦ Iio x)
    fun _ ↦ measurableSet_lt measurable_snd measurable_fst

/-- For atomless noise the choice probability integrates the product of the other alternatives'
distribution functions. -/
theorem rumChoiceProb_eq_lintegral_cdf (ν : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    [∀ j, NullSingletonClass (ν j)] (i : ι) :
    rumChoiceProb ν i = ∫⁻ x, ENNReal.ofReal (∏ j ∈ univ.erase i, cdf (ν j) x) ∂ν i := by
  rw [rumChoiceProb_eq_lintegral]
  refine lintegral_congr fun x ↦ ?_
  rw [ENNReal.ofReal_prod_of_nonneg fun j _ ↦ cdf_nonneg _ _]
  exact prod_congr rfl fun j _ ↦ by rw [ofReal_cdf, measure_congr Iio_ae_eq_Iic]

variable (ν : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] [∀ j, NullSingletonClass (ν j)]

/-- Ties between two distinct coordinates are null under atomless independent noise. -/
theorem pi_setOf_apply_eq_apply {j k : ι} (hjk : j ≠ k) : Measure.pi ν {x | x j = x k} = 0 := by
  have hs : ∀ l, MeasurableSet {p : ℝ × ℝ | p.2 ∈ (if l = j then {p.1} else univ : Set ℝ)} := by
    intro l
    by_cases hl : l = j
    · simpa [hl] using measurableSet_eq_fun measurable_snd measurable_fst
    · simp [hl]
  have h := Measure.pi_setOf_forall_ne_mem ν k
    (s := fun l a ↦ if l = j then {a} else univ) hs
  have hset : {x : ι → ℝ | ∀ l, l ≠ k → x l ∈ (if l = j then {x k} else univ : Set ℝ)} =
      {x | x j = x k} := by
    ext x
    simp only [mem_ofPred_eq]
    refine ⟨fun h ↦ by simpa using h j hjk, fun h l _ ↦ ?_⟩
    by_cases hl : l = j
    · simp [hl, h]
    · simp [hl]
  rw [hset] at h
  rw [h]
  refine lintegral_eq_zero_of_ae_eq_zero (.of_forall fun a ↦ ?_)
  exact prod_eq_zero (mem_erase.2 ⟨hjk, mem_univ j⟩) (by simp)

/-- For atomless noise the choice probabilities of the alternatives sum to one. -/
theorem sum_rumChoiceProb [Nonempty ι] : ∑ i, rumChoiceProb ν i = 1 := by
  have hmeas : ∀ i, MeasurableSet {x : ι → ℝ | ∀ j, j ≠ i → x j < x i} := fun i ↦ by
    simp only [ofPred_forall]
    exact .iInter fun j ↦ .iInter fun _ ↦
      measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)
  have hdisj : Pairwise (Function.onFun Disjoint fun i ↦ {x : ι → ℝ | ∀ j, j ≠ i → x j < x i}) :=
    fun i k hik ↦ Set.disjoint_left.2 fun x hi hk ↦ lt_asymm (hi k hik.symm) (hk i hik)
  simp only [rumChoiceProb]
  rw [← measure_biUnion_finset (fun i _ k _ hik ↦ hdisj hik) fun i _ ↦ hmeas i,
    ← measure_univ (μ := Measure.pi ν)]
  refine measure_congr (ae_eq_univ.2 (measure_mono_null (t := ⋃ j, ⋃ k, ⋃ (_ : j ≠ k),
    {x : ι → ℝ | x j = x k}) (fun x hx ↦ ?_) ?_))
  · by_contra hinj
    simp only [mem_iUnion, not_exists] at hinj
    obtain ⟨i, hi⟩ := Finite.exists_max x
    exact hx (mem_iUnion₂.2 ⟨i, mem_univ i, fun j hj ↦ (hi j).lt_of_ne fun h ↦ hinj j i hj h⟩)
  · exact measure_iUnion_null fun j ↦ measure_iUnion_null fun k ↦ measure_iUnion_null fun hjk ↦
      pi_setOf_apply_eq_apply ν hjk

end ChoiceProb

/-! ### Gaussian noise: the probit rule -/

/-- The binary probit rule: two alternatives with independent Gaussian utilities of means `u 0`,
`u 1` and common variance `v`. The difference of the utilities is Gaussian with variance `2 * v`. -/
theorem rumChoiceProb_gaussianReal (u : Fin 2 → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    rumChoiceProb (fun j ↦ gaussianReal (u j) v) 0 =
      ENNReal.ofReal (normalCDF ((u 0 - u 1) / √(2 * v))) := by
  have hS : {x : Fin 2 → ℝ | ∀ j, j ≠ 0 → x j < x 0} =
      MeasurableEquiv.piFinTwo (fun _ ↦ ℝ) ⁻¹' ((fun p : ℝ × ℝ ↦ p.1 + -p.2) ⁻¹' Ioi 0) := by
    ext x; simp [Fin.forall_fin_two]
  have hmap : ((gaussianReal (u 0) v).prod (gaussianReal (u 1) v)).map (fun p ↦ p.1 + -p.2) =
      gaussianReal (u 0 - u 1) (v + v) := by
    have h : (gaussianReal (u 0) v).prod ((gaussianReal (u 1) v).map fun x ↦ -x) =
        ((gaussianReal (u 0) v).prod (gaussianReal (u 1) v)).map (Prod.map id fun x ↦ -x) := by
      simpa using Measure.map_prod_map (gaussianReal (u 0) v) (gaussianReal (u 1) v)
        measurable_id measurable_neg
    rw [sub_eq_add_neg, ← gaussianReal_conv_gaussianReal, ← gaussianReal_map_neg, Measure.conv, h,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hv2 : v + v ≠ 0 := by simpa using hv
  rw [rumChoiceProb, hS,
    (measurePreserving_piFinTwo fun j ↦ gaussianReal (u j) v).measure_preimage_equiv,
    ← Measure.map_apply (by fun_prop) measurableSet_Ioi, hmap, ← ofReal_measureReal,
    gaussianReal_real_Ioi _ hv2, sub_zero, NNReal.coe_add, two_mul]

variable {Δ σ : ℝ}

open Real

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

/-- Two alternatives with independent Gaussian utilities of common standard deviation `σ` follow the
probit rule with standard deviation `σ * √2`, that of the difference of the two utilities. -/
theorem rumChoiceProb_gaussianReal_sq (u : Fin 2 → ℝ) (hσ : 0 < σ) :
    rumChoiceProb (fun j ↦ gaussianReal (u j) (.mk (σ ^ 2) (sq_nonneg σ))) 0 =
      ENNReal.ofReal (gaussianChoiceProb (u 0 - u 1) (σ * √2)) := by
  have hv : NNReal.mk (σ ^ 2) (sq_nonneg σ) ≠ 0 := by simp [← NNReal.coe_eq_zero, hσ.ne']
  rw [rumChoiceProb_gaussianReal u hv, gaussianChoiceProb, NNReal.coe_mk, mul_comm (2 : ℝ),
    sqrt_mul (sq_nonneg σ), sqrt_sq hσ.le]

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

end ProbabilityTheory
