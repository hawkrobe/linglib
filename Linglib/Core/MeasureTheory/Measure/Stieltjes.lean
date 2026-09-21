/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Continuity points of a Stieltjes function

A Stieltjes function is continuous exactly where its measure has no atom. `[UPSTREAM]` candidate
for `Mathlib/MeasureTheory/Measure/Stieltjes.lean`.
-/

public section

open Set

namespace StieltjesFunction

/-- A Stieltjes function is continuous at `x` iff its measure has no atom at `x`. -/
theorem continuousAt_iff_measure_singleton (f : StieltjesFunction ℝ) {x : ℝ} :
    ContinuousAt f x ↔ f.measure {x} = 0 := by
  rw [measure_singleton, ENNReal.ofReal_eq_zero, sub_nonpos,
    continuousAt_iff_continuous_left'_right', f.mono.continuousWithinAt_Iio_iff_leftLim_eq]
  exact ⟨fun h ↦ h.1.ge, fun h ↦
    ⟨(f.mono.leftLim_le le_rfl).antisymm h, (f.right_continuous x).mono Ioi_subset_Ici_self⟩⟩

end StieltjesFunction
