/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Conditional measures are densities

`cond_eq_withDensity`: conditioning on an event is reweighting by the density
`(μ s)⁻¹` on `s` and `0` off it — an exact measure equality with no
side conditions beyond measurability. The Radon-Nikodym facts
(`rnDeriv_cond`, `rnDeriv_cond_ae_const`) are its corollaries.
`[UPSTREAM]` candidates. Mathlib has no `withDensity` or `rnDeriv`
characterization of `cond` in either direction; its
`Probability/ConditionalProbability.lean` imports only measure typeclasses, so
the realistic upstream shape is a new leaf holding this file's three lemmas
(importing `ConditionalProbability` + `WithDensity` + `Decomposition.Lebesgue`,
the pattern of `WithDensityFinite.lean`), unless review pulls
`cond_eq_withDensity` alone into `ConditionalProbability.lean` at the cost of
one import.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s : Set Ω}

/-- The conditional measure `μ[|s]` is `μ` with density `(μ s)⁻¹` on `s` and `0` off it. -/
theorem cond_eq_withDensity (hs : MeasurableSet s) :
    μ[|s] = μ.withDensity (s.indicator fun _ => (μ s)⁻¹) :=
  ((withDensity_indicator hs _).trans (withDensity_const _)).symm

variable [SigmaFinite μ]

/-- The Radon-Nikodym derivative of the conditional measure `μ[|s]` with
respect to `μ` is `(μ s)⁻¹` on `s` and `0` off it. -/
theorem rnDeriv_cond (hs : MeasurableSet s) :
    (μ[|s]).rnDeriv μ =ᵐ[μ] s.indicator fun _ => (μ s)⁻¹ :=
  cond_eq_withDensity hs ▸ Measure.rnDeriv_withDensity μ (measurable_const.indicator hs)

/-- On its own event, the conditional measure's density is the constant `(μ s)⁻¹`. -/
theorem rnDeriv_cond_ae_const (hs : MeasurableSet s) :
    (μ[|s]).rnDeriv μ =ᵐ[μ[|s]] fun _ => (μ s)⁻¹ :=
  (cond_absolutelyContinuous.ae_eq (rnDeriv_cond hs)).trans <|
    (ae_cond_mem hs).mono fun _ hx => Set.indicator_of_mem hx _

end ProbabilityTheory

/-! ### Evaluation lemmas for conditionals

Bounds and real-valued forms of `cond` at an event. `[UPSTREAM]` candidates
alongside the density characterization above. -/

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {s : Set Ω}

/-- Values of a conditional of a finite measure never exceed 1. -/
theorem cond_apply_le_one [IsFiniteMeasure μ] (hs : MeasurableSet s) (e : Set Ω) :
    μ[|s] e ≤ 1 := by
  rw [cond_apply hs]
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · simp [measure_mono_null Set.inter_subset_left h0]
  · calc (μ s)⁻¹ * μ (s ∩ e) ≤ (μ s)⁻¹ * μ s :=
        mul_le_mul' le_rfl (measure_mono Set.inter_subset_left)
    _ = 1 := ENNReal.inv_mul_cancel h0 (measure_ne_top μ s)

/-- Conditional values are finite for finite measures. -/
theorem cond_apply_ne_top [IsFiniteMeasure μ] (hs : MeasurableSet s) (e : Set Ω) :
    μ[|s] e ≠ ∞ :=
  (lt_of_le_of_lt (cond_apply_le_one μ hs e) ENNReal.one_lt_top).ne

/-- Conditioning gives probability 1 to any superset of the conditioning
event. -/
theorem cond_eq_one_of_subset [IsFiniteMeasure μ] {e : Set Ω}
    (hs : MeasurableSet s) (hsub : s ⊆ e) (hne : μ s ≠ 0) : μ[|s] e = 1 := by
  rw [cond_apply hs, Set.inter_eq_left.mpr hsub,
    ENNReal.inv_mul_cancel hne (measure_ne_top μ s)]

/-- The conditional as a ratio of real-valued masses. -/
theorem cond_real_apply (hs : MeasurableSet s) (e : Set Ω) :
    (μ[|s] e).toReal = (μ (s ∩ e)).toReal / (μ s).toReal := by
  rw [cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv, inv_mul_eq_div]

/-- Total probability in real-valued form: a measurable conditioning event
splits any event's mass. -/
theorem real_total [IsFiniteMeasure μ] {h : Set Ω} (hm : MeasurableSet h) (e : Set Ω) :
    (μ (h ∩ e)).toReal + (μ (hᶜ ∩ e)).toReal = (μ e).toReal := by
  have h1 := measure_inter_add_sdiff (μ := μ) e hm
  rw [Set.sdiff_eq] at h1
  have h2 := congrArg ENNReal.toReal h1
  rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    Set.inter_comm e h, Set.inter_comm e hᶜ] at h2

/-- In a finite discrete space, an event's mass is the sum of its atoms'
masses (the register of `Mathlib.Probability.Decision.Risk.Countable`). -/
theorem measure_apply_fintype [Fintype Ω] [MeasurableSingletonClass Ω]
    (e : Set Ω) [DecidablePred (· ∈ e)] :
    μ e = ∑ w ∈ Finset.univ.filter (· ∈ e), μ {w} := by
  rw [MeasureTheory.sum_measure_singleton]
  congr 1
  ext w
  simp

/-- The counting measure of an event in a finite discrete space is the
number of its atoms. Loop-safe as a `simp` rewrite (the right-hand side
contains no measure application). -/
theorem count_apply_fintype [Fintype Ω] [MeasurableSingletonClass Ω]
    (e : Set Ω) [DecidablePred (· ∈ e)] :
    (Measure.count : Measure Ω) e = (Finset.univ.filter (· ∈ e)).card := by
  rw [measure_apply_fintype]
  simp [Measure.count_singleton]

end ProbabilityTheory
