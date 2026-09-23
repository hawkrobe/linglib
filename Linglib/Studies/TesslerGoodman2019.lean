module

public import Linglib.Pragmatics.RSA.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Tessler and Goodman (2019): The Language of Generalization

This file formalizes [tessler-goodman-2019]'s model of generic, habitual and causal language.
A generalization has the threshold semantics of a gradable adjective on the scale of
prevalence, the probability that an instance of the category has the property (2),
`genericMeaning`, with the threshold underspecified and drawn from a prior. The interpretation
model (1) conditions a prior over prevalence on the utterance with the threshold integrated
out, so the marginalized meaning of the generalization at a prevalence is the threshold prior's
mass below it, and silence is true everywhere, `meaning`, `listener`, the substrate's
`RSA.literalListener`. The endorsement model (3) is the speaker who chooses between the
generalization and silence by how well each conveys the referent prevalence, `endorser`, the
substrate's `RSA.speaker`. Since silence returns the prior, `listener_silent_apply`, the
speaker endorses the generalization exactly when the marginalized meaning at the referent
prevalence exceeds its expectation under the prevalence prior, `endorse_iff`; with the uniform
threshold prior on the unit interval the marginalized meaning is the prevalence itself,
`meaning_uniformThreshold`, so a generalization is endorsed exactly when the referent prevalence
exceeds the prior mean prevalence, `endorse_iff_expectation_lt`, the cue validity of Appendix A,
whose normalizer is that mean, `expectedPrevalence_map`.

The worked examples of Table 1 are consequences of the prior mean. Endorsement is monotone in
prevalence at a fixed prior (Figure 1), `endorse_mono`; at one referent prevalence a property
whose prior mean lies below it is endorsed while one whose prior mean lies at or above it is
not, `endorse_of_expectation_lt`, `not_endorse_of_le_expectation`, which is why *dogs bark* at
a high prevalence and *mosquitos carry malaria* at a low one are endorsed while *kangaroos
have spots* is not. A prior symmetric about one half has mean one half,
`expectedPrevalence_eq_half_of_symm`, so *robins are female* at a prevalence of one half is
exactly at the boundary, the generalization no more informative than silence,
`boundary_of_symm`; mixing such a prior with a component at zero prevalence, the categories
without the mechanism, lowers the mean below one half, `expectedPrevalence_mixture`, so *robins
lay eggs* at the same prevalence is endorsed, `endorse_of_mixture`. Habituals use the same
model on the scale of frequency, and causal generalizations on the rate at which the cause
produces the effect, with the priors elicited in the experiments; the model's fits to the
endorsement data of the three case studies are the paper's empirical content and are described,
not formalized.

## Implementation notes

The prevalence scale is a finite type carrying a real prevalence, and the prevalence prior a
probability measure on it; the threshold prior is any finite measure on the reals, the paper's
uniform prior on the support of the prevalence prior being the case treated on the real face.
The rationality of the endorser is a parameter, so the theorems hold at every positive
rationality; the paper's fitted values are not pinned.

## References

* [tessler-goodman-2019]
* [frank-goodman-2012]
* [lassiter-goodman-2017]
* [leslie-2008]
-/

@[expose] public section

namespace TesslerGoodman2019

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNReal

/-- The utterances of the endorsement model: the generalization, or silence. -/
inductive Utterance
  | generic
  | silent
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤

instance : DiscreteMeasurableSpace Utterance := ⟨λ _ => trivial⟩

/-- The threshold semantics of a generalization (2): the prevalence exceeds the threshold. -/
def genericMeaning (θ p : ℝ) : Prop := θ < p

section Model

variable {W : Type*} [Fintype W] [MeasurableSpace W]

/-- The meaning of (1) with the threshold integrated out against its prior `ν`: for the
generalization the prior mass of thresholds below the prevalence, for silence one. -/
noncomputable def meaning (ν : Measure ℝ) (prev : W → ℝ) : Utterance → W → ℝ≥0∞
  | .generic, w => ν {θ | genericMeaning θ (prev w)}
  | .silent, _ => 1

/-- The expectation under the prevalence prior of the marginalized meaning of the
generalization. -/
noncomputable def expectedMeaning (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ) : ℝ≥0∞ :=
  ∑ w, meaning ν prev .generic w * μ {w}

theorem expectedMeaning_ne_top (μ : Measure W) [IsFiniteMeasure μ] (ν : Measure ℝ)
    [IsFiniteMeasure ν] (prev : W → ℝ) : expectedMeaning μ ν prev ≠ ⊤ :=
  ENNReal.sum_ne_top.2 λ _ _ => ENNReal.mul_ne_top (measure_ne_top ν _) (measure_ne_top μ _)

/-- The interpretation model (1): the prevalence prior conditioned on the marginalized
meaning. -/
noncomputable def listener (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ) :
    Kernel Utterance W :=
  literalListener μ (meaning ν prev)

variable [DiscreteMeasurableSpace W]

/-- The endorsement model (3): the speaker at rationality `lam`, choosing between the
generalization and silence at no cost. -/
noncomputable def endorser (lam : ℝ) (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ) :
    Kernel W Utterance :=
  speaker lam 1 (listener μ ν prev)

/-- The generalization is endorsed at a state when the speaker produces it more readily than
silence. -/
def Endorsed (lam : ℝ) (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ) (w : W) : Prop :=
  (endorser lam μ ν prev w).real {.silent} < (endorser lam μ ν prev w).real {.generic}

variable (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ)

theorem listener_generic_apply (w : W) :
    listener μ ν prev .generic {w} =
      meaning ν prev .generic w * μ {w} / expectedMeaning μ ν prev := by
  rw [listener, literalListener_apply_singleton]; rfl

variable [IsProbabilityMeasure μ] {lam : ℝ} {w : W}

/-- Silence returns the prior. -/
theorem listener_silent_apply (w : W) : listener μ ν prev .silent {w} = μ {w} := by
  rw [listener, literalListener_apply_singleton]
  simp only [meaning, one_mul]
  rw [sum_measure_singleton, Finset.coe_univ, measure_univ, div_one]

variable [IsFiniteMeasure ν]

/-- The generalization is endorsed exactly when its marginalized meaning at the referent state
exceeds the prior expectation of that meaning: the comparison of Figure 1C, the listener's
posterior on hearing the generalization against the prior. -/
theorem endorse_iff (hlam : 0 < lam) (hw : μ {w} ≠ 0) (hZ : expectedMeaning μ ν prev ≠ 0) :
    Endorsed lam μ ν prev w ↔ expectedMeaning μ ν prev < meaning ν prev .generic w := by
  rw [Endorsed, endorser, speaker_real_singleton_lt_iff (cost := 1) (L := listener μ ν prev)
    (w := w) hlam.le (λ _ => ENNReal.one_ne_top) (λ u => literalListener_apply_le_one μ _ u _)
    ⟨.silent, by
      rw [listener_silent_apply, Pi.one_apply, mul_one]
      exact weight_rpow_ne_zero hlam.le hw⟩]
  simp only [Pi.one_apply, mul_one]
  rw [ENNReal.rpow_lt_rpow_iff hlam, listener_silent_apply, listener_generic_apply,
    ENNReal.lt_div_iff_mul_lt (Or.inl hZ) (Or.inl (expectedMeaning_ne_top μ ν prev)), mul_comm,
    ENNReal.mul_lt_mul_iff_left hw (measure_ne_top μ _)]

/-- Endorsement is monotone in prevalence at a fixed prior (Figure 1C). -/
theorem endorse_mono (hlam : 0 < lam) (hZ : expectedMeaning μ ν prev ≠ 0) {w w' : W}
    (hw : μ {w} ≠ 0) (hw' : μ {w'} ≠ 0) (hle : prev w ≤ prev w') (h : Endorsed lam μ ν prev w) :
    Endorsed lam μ ν prev w' := by
  rw [endorse_iff μ ν prev hlam hw hZ] at h
  rw [endorse_iff μ ν prev hlam hw' hZ]
  exact h.trans_le (measure_mono λ θ hθ => lt_of_lt_of_le hθ hle)

end Model

/-! ### The uniform threshold prior -/

section Uniform

/-- The uniform threshold prior on the unit interval, the support of a prevalence prior. -/
noncomputable def uniformThreshold : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsFiniteMeasure uniformThreshold :=
  ⟨by rw [uniformThreshold, Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩

/-- The uniform threshold prior's mass below a prevalence in the unit interval is the
prevalence. -/
theorem uniformThreshold_Iio {p : ℝ} (h1 : p ≤ 1) :
    uniformThreshold (Set.Iio p) = ENNReal.ofReal p := by
  rw [uniformThreshold, Measure.restrict_apply measurableSet_Iio,
    show Set.Iio p ∩ Set.Icc 0 1 = Set.Ico 0 p by
      ext θ; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨h, h0', _⟩; exact ⟨h0', h⟩
      · rintro ⟨h0', h⟩; exact ⟨h, h0', by linarith⟩,
    Real.volume_Ico, sub_zero]

variable {W : Type*}

/-- Under the uniform threshold prior the marginalized meaning of the generalization is the
prevalence. -/
theorem meaning_uniformThreshold (prev : W → ℝ) (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1) (w : W) :
    meaning uniformThreshold prev .generic w = ENNReal.ofReal (prev w) :=
  uniformThreshold_Iio (hp w).2

variable [MeasurableSpace W]

/-- The mean prevalence under the prior. -/
noncomputable def expectedPrevalence (μ : Measure W) (prev : W → ℝ) : ℝ := ∫ w, prev w ∂μ

variable (prev : W → ℝ)

/-- Appendix A: the prevalence prior is the pushforward of a prior over categories along their
prevalences, and the normalizer of cue validity, the mean prevalence over categories, is the
mean of the prevalence prior. -/
theorem expectedPrevalence_map {K : Type*} [MeasurableSpace K] [DiscreteMeasurableSpace K]
    [Countable K] (P : Measure K) (prevK : K → W) (hprev : Measurable prevK)
    (hf : Measurable prev) :
    expectedPrevalence (P.map prevK) prev = ∫ k, prev (prevK k) ∂P := by
  rw [expectedPrevalence, integral_map hprev.aemeasurable hf.aestronglyMeasurable]

variable [Fintype W] [DiscreteMeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ]

theorem expectedPrevalence_eq_sum :
    expectedPrevalence μ prev = ∑ w, μ.real {w} * prev w := by
  rw [expectedPrevalence, integral_fintype .of_finite]
  rfl

theorem expectedMeaning_uniformThreshold (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1) :
    expectedMeaning μ uniformThreshold prev = ENNReal.ofReal (expectedPrevalence μ prev) := by
  rw [expectedPrevalence_eq_sum, expectedMeaning,
    ENNReal.ofReal_sum_of_nonneg λ w _ => mul_nonneg measureReal_nonneg (hp w).1]
  refine Finset.sum_congr rfl λ w _ => ?_
  rw [meaning_uniformThreshold prev hp, ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top μ _), mul_comm]

variable {lam : ℝ} {w : W}

/-- Cue validity (Appendix A): the generalization is endorsed exactly when the referent
prevalence exceeds the mean prevalence under the prior. -/
theorem endorse_iff_expectation_lt (hlam : 0 < lam) (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1)
    (hw : μ {w} ≠ 0) (hZ : 0 < expectedPrevalence μ prev) :
    Endorsed lam μ uniformThreshold prev w ↔ expectedPrevalence μ prev < prev w := by
  rw [endorse_iff μ uniformThreshold prev hlam hw
    (by rw [expectedMeaning_uniformThreshold prev μ hp]; exact (ENNReal.ofReal_pos.2 hZ).ne'),
    expectedMeaning_uniformThreshold prev μ hp, meaning_uniformThreshold prev hp,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hZ.le]

/-- A property whose prior mean lies below the referent prevalence is endorsed. -/
theorem endorse_of_expectation_lt (hlam : 0 < lam) (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1)
    (hw : μ {w} ≠ 0) (hZ : 0 < expectedPrevalence μ prev)
    (h : expectedPrevalence μ prev < prev w) : Endorsed lam μ uniformThreshold prev w :=
  (endorse_iff_expectation_lt prev μ hlam hp hw hZ).2 h

/-- A property whose prior mean lies at or above the referent prevalence is not endorsed. -/
theorem not_endorse_of_le_expectation (hlam : 0 < lam) (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1)
    (hw : μ {w} ≠ 0) (hZ : 0 < expectedPrevalence μ prev)
    (h : prev w ≤ expectedPrevalence μ prev) : ¬ Endorsed lam μ uniformThreshold prev w :=
  λ he => absurd ((endorse_iff_expectation_lt prev μ hlam hp hw hZ).1 he) (not_lt.2 h)

end Uniform

/-! ### Table 1: symmetric and bimodal priors -/

/-- A mixture of a probability measure with mass `φ` and another with mass `1 - φ` is a
probability measure. -/
theorem isProbabilityMeasure_mixture {W : Type*} [MeasurableSpace W] (ν₁ ν₀ : Measure W)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₀] {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ 1) :
    IsProbabilityMeasure (φ.toNNReal • ν₁ + (1 - φ).toNNReal • ν₀) :=
  ⟨by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
      ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.coe_add, ← Real.toNNReal_add h0 (by linarith), add_sub_cancel,
      Real.toNNReal_one, ENNReal.coe_one]⟩

section Examples

variable {W : Type*} [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
  (prev : W → ℝ)

/-- A prior invariant under a reflection of the scale about one half has mean one half. -/
theorem expectedPrevalence_eq_half_of_symm (μ : Measure W) [IsProbabilityMeasure μ] (σ : W ≃ W)
    (hσ : ∀ w, prev (σ w) = 1 - prev w) (hμ : ∀ w, μ {σ w} = μ {w}) :
    expectedPrevalence μ prev = 1 / 2 := by
  have h1 : ∑ w, μ.real {w} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have key : expectedPrevalence μ prev = ∑ w, μ.real {w} * (1 - prev w) := by
    rw [expectedPrevalence_eq_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl λ w _ => ?_
    rw [hσ, measureReal_def, hμ, ← measureReal_def]
  have : ∑ w, μ.real {w} * (1 - prev w) = (∑ w, μ.real {w}) - ∑ w, μ.real {w} * prev w := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl λ w _ => by ring
  rw [this, h1, ← expectedPrevalence_eq_sum] at key
  linarith

/-- The mean prevalence of a mixture is the mixture of the means. -/
theorem expectedPrevalence_mixture (ν₁ ν₀ : Measure W) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₀]
    (c d : ℝ≥0) :
    expectedPrevalence (c • ν₁ + d • ν₀) prev =
      c * expectedPrevalence ν₁ prev + d * expectedPrevalence ν₀ prev := by
  simp only [expectedPrevalence]
  rw [integral_add_measure (.of_finite) (.of_finite), integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul]

/-- *Robins are female*: a prior symmetric about one half puts a referent prevalence of one
half exactly at the boundary, where the generalization and silence are produced alike. -/
theorem boundary_of_symm (μ : Measure W) [IsProbabilityMeasure μ] (σ : W ≃ W)
    (hσ : ∀ w, prev (σ w) = 1 - prev w) (hμ : ∀ w, μ {σ w} = μ {w}) {lam : ℝ} (hlam : 0 < lam)
    (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1) {w : W} (hw : μ {w} ≠ 0) (hhalf : prev w = 1 / 2) :
    (endorser lam μ uniformThreshold prev w).real {.generic} =
      (endorser lam μ uniformThreshold prev w).real {.silent} := by
  have hE := expectedPrevalence_eq_half_of_symm prev μ σ hσ hμ
  have hZ : 0 < expectedPrevalence μ prev := by rw [hE]; norm_num
  have h1 := not_endorse_of_le_expectation prev μ hlam hp hw hZ (by rw [hE, hhalf])
  have h2 : ¬ (endorser lam μ uniformThreshold prev w).real {.generic} <
      (endorser lam μ uniformThreshold prev w).real {.silent} := by
    rw [endorser, speaker_real_singleton_lt_iff (cost := 1) (L := listener μ uniformThreshold prev)
      (w := w) hlam.le (λ _ => ENNReal.one_ne_top) (λ u => literalListener_apply_le_one μ _ u _)
      ⟨.silent, by
        rw [listener_silent_apply, Pi.one_apply, mul_one]
        exact weight_rpow_ne_zero hlam.le hw⟩]
    simp only [Pi.one_apply, mul_one]
    rw [ENNReal.rpow_lt_rpow_iff hlam, listener_silent_apply, listener_generic_apply,
      expectedMeaning_uniformThreshold prev μ hp, meaning_uniformThreshold prev hp, hE, hhalf,
      ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact lt_irrefl _
  exact le_antisymm (not_lt.1 h1) (not_lt.1 h2)

/-- *Robins lay eggs*: mixing a prior symmetric about one half with a component at zero
prevalence, the categories without the mechanism, at weight `1 - φ`, gives mean `φ / 2`. -/
theorem expectedPrevalence_bimodal (ν₁ : Measure W) [IsProbabilityMeasure ν₁] (σ : W ≃ W)
    (hσ : ∀ w, prev (σ w) = 1 - prev w) (hν : ∀ w, ν₁ {σ w} = ν₁ {w}) (w₀ : W)
    (hw₀ : prev w₀ = 0) {φ : ℝ} (h0 : 0 ≤ φ) :
    expectedPrevalence (φ.toNNReal • ν₁ + (1 - φ).toNNReal • Measure.dirac w₀) prev = φ / 2 := by
  rw [expectedPrevalence_mixture, expectedPrevalence_eq_half_of_symm prev ν₁ σ hσ hν,
    expectedPrevalence, integral_dirac, hw₀, Real.coe_toNNReal _ h0]
  ring

/-- At a referent prevalence of one half the bimodal prior endorses the generalization
whenever some categories lack the mechanism, `φ < 1`, while the symmetric prior alone,
`φ = 1`, sits at the boundary. -/
theorem endorse_of_mixture (ν₁ : Measure W) [IsProbabilityMeasure ν₁] (σ : W ≃ W)
    (hσ : ∀ w, prev (σ w) = 1 - prev w) (hν : ∀ w, ν₁ {σ w} = ν₁ {w}) (w₀ : W)
    (hw₀ : prev w₀ = 0) {φ : ℝ} (h0 : 0 < φ) (h1 : φ < 1) {lam : ℝ} (hlam : 0 < lam)
    (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1) {w : W} (hw : ν₁ {w} ≠ 0) (hhalf : prev w = 1 / 2) :
    haveI := isProbabilityMeasure_mixture ν₁ (Measure.dirac w₀) h0.le h1.le
    Endorsed lam (φ.toNNReal • ν₁ + (1 - φ).toNNReal • Measure.dirac w₀) uniformThreshold prev
      w := by
  have := isProbabilityMeasure_mixture ν₁ (Measure.dirac w₀) h0.le h1.le
  have hE := expectedPrevalence_bimodal prev ν₁ σ hσ hν w₀ hw₀ h0.le
  refine endorse_of_expectation_lt prev _ hlam hp ?_ (by rw [hE]; positivity)
    (by rw [hE, hhalf]; linarith)
  rw [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  refine ne_of_gt (lt_of_lt_of_le (ENNReal.mul_pos ?_ hw) le_self_add)
  exact_mod_cast (Real.toNNReal_pos.2 h0).ne'

end Examples

end TesslerGoodman2019
