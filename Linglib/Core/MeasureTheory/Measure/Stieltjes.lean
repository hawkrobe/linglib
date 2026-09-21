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

namespace StieltjesFunction

variable {R : Type*} [LinearOrder R] [TopologicalSpace R] [OrderTopology R] [CompactIccSpace R]
  [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] [DenselyOrdered R]

/-- A Stieltjes function is continuous at `x` iff its measure has no atom at `x`. -/
theorem continuousAt_iff_measure_singleton (f : StieltjesFunction R) {x : R} :
    ContinuousAt f x ↔ f.measure {x} = 0 := by
  rw [measure_singleton, ENNReal.ofReal_eq_zero, sub_nonpos,
    f.mono.continuousAt_iff_leftLim_eq_rightLim, f.rightLim_eq,
    (f.mono.leftLim_le le_rfl).ge_iff_eq]

end StieltjesFunction
