/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.Real

/-!
# Surprisal

The surprisal, or information content, of a point under a measure is the negative logarithm of
the mass of the point. The summand of Shannon entropy at a point is the mass of the point times
its surprisal.

## References

* [cover-thomas-2006], chapter 2.
-/

open MeasureTheory Real

namespace InformationTheory

variable {S : Type*} [MeasurableSpace S]

/-- The surprisal of the point `s` under the measure `μ`. -/
noncomputable def surprisal (μ : Measure S) (s : S) : ℝ := -log (μ.real {s})

theorem negMulLog_measureReal_singleton (μ : Measure S) (s : S) :
    negMulLog (μ.real {s}) = μ.real {s} * surprisal μ s := by
  rw [negMulLog, surprisal]
  ring

end InformationTheory
