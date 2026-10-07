/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Finite sums of Dirac measures

On a finite type with measurable singletons, `∑ b, w b • dirac b` gives a set the total weight
of its points; `Measure.ofWeights w` names it. With nonnegative real weights its real values are
sums of those weights, and it is a probability measure when they sum to one. `[UPSTREAM]`
candidate for `Mathlib/MeasureTheory/Measure/Dirac.lean`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {β : Type*} [MeasurableSpace β] [Fintype β] [MeasurableSingletonClass β]

/-- A finite sum of scaled Dirac measures gives a set the total weight of its points. -/
theorem sum_smul_dirac_apply (w : β → ℝ≥0∞) (s : Set β) :
    (∑ b, w b • dirac b) s = ∑ b, s.indicator w b := by
  rw [finsetSum_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  by_cases hb : b ∈ s <;> simp [hb]

/-- A finite sum of scaled Dirac measures evaluates at a singleton to its weight. -/
theorem sum_smul_dirac_apply_singleton (w : β → ℝ≥0∞) (b : β) :
    (∑ b', w b' • dirac b') {b} = w b := by
  classical
  simp [sum_smul_dirac_apply, Set.indicator_apply]

/-- With nonnegative real weights, a finite sum of Dirac measures gives a set, on reals, the
total weight of its points. -/
theorem sum_ofReal_smul_dirac_real_apply {w : β → ℝ} (hw : ∀ b, 0 ≤ w b) (s : Set β) :
    (∑ b, ENNReal.ofReal (w b) • dirac b).real s = ∑ b, s.indicator w b := by
  rw [measureReal_def, sum_smul_dirac_apply, ENNReal.toReal_sum fun b _ ↦ by
    by_cases hb : b ∈ s <;> simp [hb]]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  by_cases hb : b ∈ s <;> simp [hb, hw b]

/-- Nonnegative real weights summing to one give a probability measure. -/
theorem isProbabilityMeasure_sum_ofReal_smul_dirac {w : β → ℝ} (hw : ∀ b, 0 ≤ w b)
    (h : ∑ b, w b = 1) : IsProbabilityMeasure (∑ b, ENNReal.ofReal (w b) • dirac b) :=
  ⟨by rw [sum_smul_dirac_apply, Set.indicator_univ,
    ← ENNReal.ofReal_sum_of_nonneg fun b _ ↦ hw b, h, ENNReal.ofReal_one]⟩

omit [MeasurableSingletonClass β] in
/-- The measure on a finite type giving each point its weight. -/
noncomputable def ofWeights (w : β → ℝ≥0∞) : Measure β := ∑ b, w b • dirac b

@[simp] theorem ofWeights_apply_singleton (w : β → ℝ≥0∞) (b : β) : ofWeights w {b} = w b :=
  sum_smul_dirac_apply_singleton w b

theorem ofWeights_apply_singleton_ne_zero {w : β → ℝ≥0∞} {b : β} (h : w b ≠ 0) :
    ofWeights w {b} ≠ 0 := by
  rwa [ofWeights_apply_singleton]

/-- The weight measure of a finite set is the sum of its points' weights. -/
theorem ofWeights_apply_finset (w : β → ℝ≥0∞) (s : Finset β) :
    ofWeights w ↑s = ∑ b ∈ s, w b := by
  rw [← sum_measure_singleton]
  simp only [ofWeights_apply_singleton]

/-- Finite weights give a finite measure. -/
theorem isFiniteMeasure_ofWeights {w : β → ℝ≥0∞} (hw : ∀ b, w b ≠ ∞) :
    IsFiniteMeasure (ofWeights w) :=
  ⟨by rw [← Finset.coe_univ, ofWeights_apply_finset]; exact ENNReal.sum_lt_top.2 fun b _ ↦
    (hw b).lt_top⟩

instance (w : β → ℕ) : IsFiniteMeasure (ofWeights fun b ↦ (w b : ℝ≥0∞)) :=
  isFiniteMeasure_ofWeights fun _ ↦ ENNReal.natCast_ne_top _

end MeasureTheory.Measure
