/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Conditional probability

Lemmas on mathlib's conditional measure `μ[|s]` that mathlib does not state: zero-one
consequences of conditioning, real-valued forms, pushforwards, invariance under scaling with the
composition of two Bayesian updates, and conditioning on nested events up to null sets.
`[UPSTREAM]` candidates for `Mathlib/Probability/ConditionalProbability.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

/-! ### Evaluation lemmas for conditionals -/

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {s : Set Ω}

/-- An event of conditional probability zero meets the conditioning event in a null set. -/
theorem measure_inter_eq_zero_of_cond_eq_zero [IsFiniteMeasure μ] {e : Set Ω}
    (hs : MeasurableSet s) (h : μ[e | s] = 0) : μ (s ∩ e) = 0 :=
  by_contra fun hne ↦ (cond_pos_of_inter_ne_zero hs hne).ne' h

/-- If `e` has probability zero given `s` and probability one given `u`, then `u` has
probability zero given `s`. -/
theorem cond_eq_zero_of_cond_eq_one [IsFiniteMeasure μ] {e u : Set Ω} (hs : MeasurableSet s)
    (he : MeasurableSet e) (hu : MeasurableSet u) (h₁ : μ[e | s] = 0) (h₂ : μ[e | u] = 1) :
    μ[u | s] = 0 := by
  have hu₀ : μ u ≠ 0 := fun h ↦ by simp [cond_eq_zero_of_meas_eq_zero h] at h₂
  have := cond_isProbabilityMeasure (μ := μ) hu₀
  have hc := measure_inter_eq_zero_of_cond_eq_zero μ hu ((prob_compl_eq_zero_iff he).2 h₂)
  have : μ (s ∩ u) = 0 := measure_mono_null
    (fun x ⟨hx, hxu⟩ ↦ (em (x ∈ e)).imp (fun hxe ↦ ⟨hx, hxe⟩) fun hxe ↦ ⟨hxu, hxe⟩)
    (measure_union_null (measure_inter_eq_zero_of_cond_eq_zero μ hs h₁) hc)
  rw [cond_apply hs, this, mul_zero]

/-- Conditioning on a subset that sheds only worlds outside `e` can only raise the conditional
probability of `e`. -/
theorem cond_le_cond_of_subset {u₁ u₂ e : Set Ω} (hu₁ : MeasurableSet u₁)
    (hu₂ : MeasurableSet u₂) (hsub : u₂ ⊆ u₁) (hent : e ∩ u₁ ⊆ u₂) : μ[|u₁] e ≤ μ[|u₂] e := by
  have h : e ∩ u₁ = e ∩ u₂ :=
    Set.Subset.antisymm (fun w hw ↦ ⟨hw.1, hent hw⟩) (Set.inter_subset_inter_right _ hsub)
  rw [cond_apply hu₁, cond_apply hu₂, Set.inter_comm u₁, Set.inter_comm u₂, h]
  exact mul_le_mul_left (ENNReal.inv_le_inv.mpr (measure_mono hsub)) _

/-- The conditional as a ratio of real-valued masses. -/
theorem cond_real_apply (hs : MeasurableSet s) (e : Set Ω) :
    μ[|s].real e = μ.real (s ∩ e) / μ.real s := by
  simp only [measureReal_def, cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv, inv_mul_eq_div]

end ProbabilityTheory

/-! ### Pushforwards -/

namespace ProbabilityTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}

/-- Conditioning a pushforward on a set is pushing forward the conditional on its preimage. -/
theorem cond_map {f : Ω → Ω'} (hf : AEMeasurable f μ) {s : Set Ω'} (hs : MeasurableSet s) :
    (μ.map f)[|s] = (μ[|f ⁻¹' s]).map f := by
  rw [cond, cond, Measure.map_smul _ hf.restrict, Measure.restrict_map_of_aemeasurable hf hs,
    Measure.map_apply_of_aemeasurable hf hs]

end ProbabilityTheory

/-! ### Sequential conditioning

Conditioning is scale-invariant, so two Bayesian updates compose: reweighting by `f`,
normalizing, reweighting by `g` and normalizing again is one reweighting by `f * g`. -/

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Conditioning is invariant under scaling the measure by a positive finite constant. -/
theorem cond_smul {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (μ : Measure Ω) (s : Set Ω) :
    (c • μ)[|s] = μ[|s] := by
  simp only [cond, Measure.smul_apply, smul_eq_mul, Measure.restrict_smul, smul_smul]
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hc), mul_right_comm, ENNReal.inv_mul_cancel hc0 hc,
    one_mul]

/-- Normalizing after reweighting by `f` and again after reweighting by `g` is normalizing once
after reweighting by `f * g`, so two Bayesian updates compose. -/
theorem cond_univ_withDensity_mul (μ : Measure Ω) {f g : Ω → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hfin : μ.withDensity f Set.univ ≠ ∞) :
    (((μ.withDensity f)[|Set.univ]).withDensity g)[|Set.univ] =
      (μ.withDensity (f * g))[|Set.univ] := by
  rw [withDensity_mul μ hf hg]
  rcases eq_or_ne (μ.withDensity f Set.univ) 0 with h0 | h0
  · have hz : (0 : Measure Ω).withDensity g = 0 :=
      Measure.ext fun s hs ↦ by rw [withDensity_apply _ hs]; simp
    rw [Measure.measure_univ_eq_zero.1 h0,
      cond_eq_zero_of_meas_eq_zero (μ := (0 : Measure Ω)) (s := Set.univ) (by simp), hz]
  · have hc : (μ.withDensity f)[|Set.univ] = (μ.withDensity f Set.univ)⁻¹ • μ.withDensity f := by
      rw [cond, Measure.restrict_univ]
    rw [hc, withDensity_smul_measure,
      cond_smul (ENNReal.inv_ne_zero.2 hfin) (ENNReal.inv_ne_top.2 h0)]

end ProbabilityTheory

/-! ### Nested events

Conditioning sees an event only up to a null set, so conditioning on an event almost contained in
another is conditioning the conditional, and the two conditionals are then comparable. -/

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s t : Set Ω}

theorem cond_congr_set (h : s =ᵐ[μ] t) : μ[|s] = μ[|t] := by
  rw [cond, cond, measure_congr h, Measure.restrict_congr_set h]

variable [IsFiniteMeasure μ]

/-- Conditioning on an event almost contained in another is conditioning the conditional. -/
theorem cond_cond_of_ae_le (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ≤ᵐ[μ] t) :
    μ[|t][|s] = μ[|s] := by
  rw [cond_cond_eq_cond_inter ht hs, Set.inter_comm]
  exact cond_congr_set (Filter.inter_eventuallyEqSet_left.2 hst)

/-- One conditional is absolutely continuous with respect to another exactly when the first
event is almost contained in the second. -/
theorem cond_absolutelyContinuous_cond_iff (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ[|s] ≪ μ[|t] ↔ s ≤ᵐ[μ] t := by
  refine ⟨fun h ↦ ?_, fun h ↦ cond_cond_of_ae_le hs ht h ▸ cond_absolutelyContinuous⟩
  have h0 : μ[|s] tᶜ = 0 := h (by rw [cond_apply ht, Set.inter_compl_self, measure_empty, mul_zero])
  rw [cond_apply hs, mul_eq_zero, ENNReal.inv_eq_zero] at h0
  exact ae_le_set.2 (h0.resolve_left (measure_ne_top _ _))

end ProbabilityTheory
