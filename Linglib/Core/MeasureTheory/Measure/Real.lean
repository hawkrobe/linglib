/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Atoms of a probability measure on a finite type

On a finite type with measurable singletons, the real masses of the atoms of a probability
measure sum to one, so the geometric mean they weight of a function constant on the atoms is that
constant. `[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Measure/Real.lean`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]

theorem sum_measureReal_singleton_eq_one (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑ a, μ.real {a} = 1 := by
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

/-- The geometric mean, weighted by a probability measure, of a function constant on the atoms of
positive mass is that constant. -/
theorem prod_rpow_measureReal_of_forall_eq (μ : Measure α) [IsProbabilityMeasure μ] {r : ℝ}
    (hr : 0 ≤ r) {f : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a, μ {a} ≠ 0 → f a = c) :
    ∏ a, f a ^ (r * μ.real {a}) = c ^ r := by
  rw [ENNReal.prod_rpow_of_forall_eq (fun a _ ↦ mul_nonneg hr measureReal_nonneg) fun a _ ha ↦
      h a fun h0 ↦ ha (by rw [measureReal_def, h0, ENNReal.toReal_zero, mul_zero]),
    ← Finset.mul_sum, sum_measureReal_singleton_eq_one, mul_one]

end MeasureTheory
