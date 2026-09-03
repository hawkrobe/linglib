/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# The Radon–Nikodym derivative on a countable type

On a countable type with measurable singletons, a measure absolutely continuous with respect
to a finite measure `ν` has density `a ↦ μ {a} / ν {a}`, so its Radon–Nikodym derivative is
the ratio of atom masses `ν`-almost everywhere. `[UPSTREAM]` candidate for
`Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`.
-/

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  {μ ν : Measure α} [IsFiniteMeasure ν]

theorem withDensity_div_singleton (hμν : μ ≪ ν) :
    ν.withDensity (fun a => μ {a} / ν {a}) = μ := by
  refine ext_of_singleton fun a => ?_
  rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton]
  exact ENNReal.div_mul_cancel' (fun h => hμν h) fun h => absurd h (measure_ne_top ν _)

theorem rnDeriv_eq_div_singleton (hμν : μ ≪ ν) :
    μ.rnDeriv ν =ᵐ[ν] fun a => μ {a} / ν {a} := by
  conv_lhs => rw [← withDensity_div_singleton hμν]
  exact rnDeriv_withDensity ν (measurable_of_countable _)

end MeasureTheory.Measure
