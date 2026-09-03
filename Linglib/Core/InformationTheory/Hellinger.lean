/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Hellinger distance on a finite type

The Bhattacharyya coefficient `∑ a, √(μ {a} · ν {a})` of two measures on a finite type, the
squared Hellinger distance `1 - BC`, and the Hellinger distance `√(1 - BC)`. For probability
measures the coefficient lies in `[0, 1]`, so the Hellinger distance is bounded by `1` where the
Kullback–Leibler divergence may be infinite. Mathlib has no Hellinger distance; `[UPSTREAM]`
candidate for `Mathlib/InformationTheory/`.
-/

open MeasureTheory Real

namespace InformationTheory

variable {α : Type*} [MeasurableSpace α] [Fintype α] (μ ν : Measure α)

/-- The Bhattacharyya coefficient `∑ a, √(μ {a} · ν {a})`. -/
noncomputable def bhattacharyyaCoeff : ℝ := ∑ a, √(μ.real {a} * ν.real {a})

/-- The squared Hellinger distance `1 - BC(μ, ν)`. -/
noncomputable def hellingerDistSq : ℝ := 1 - bhattacharyyaCoeff μ ν

/-- The Hellinger distance `√(1 - BC(μ, ν))`. -/
noncomputable def hellingerDist : ℝ := √(hellingerDistSq μ ν)

theorem bhattacharyyaCoeff_nonneg : 0 ≤ bhattacharyyaCoeff μ ν :=
  Finset.sum_nonneg fun _ _ => sqrt_nonneg _

theorem hellingerDistSq_le_one : hellingerDistSq μ ν ≤ 1 :=
  sub_le_self _ (bhattacharyyaCoeff_nonneg μ ν)

theorem hellingerDist_le_one : hellingerDist μ ν ≤ 1 :=
  sqrt_one ▸ sqrt_le_sqrt (hellingerDistSq_le_one μ ν)

variable [MeasurableSingletonClass α] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- For probability measures the Bhattacharyya coefficient is at most `1`, by the
arithmetic–geometric mean inequality on each atom. -/
theorem bhattacharyyaCoeff_le_one : bhattacharyyaCoeff μ ν ≤ 1 := by
  calc bhattacharyyaCoeff μ ν ≤ ∑ a, (μ.real {a} + ν.real {a}) / 2 :=
        Finset.sum_le_sum fun a _ => sqrt_le_iff.mpr
          ⟨by positivity, by nlinarith [sq_nonneg (μ.real {a} - ν.real {a})]⟩
    _ = 1 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, sum_measureReal_singleton,
          sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
        norm_num

theorem hellingerDistSq_nonneg : 0 ≤ hellingerDistSq μ ν :=
  sub_nonneg.mpr (bhattacharyyaCoeff_le_one μ ν)

end InformationTheory
