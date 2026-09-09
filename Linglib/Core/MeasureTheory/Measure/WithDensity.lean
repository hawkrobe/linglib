/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Densities and pushforwards

A density that factors through a map commutes with the pushforward along it.
`[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Measure/WithDensity.lean`.
-/

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}

theorem map_withDensity_comp {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f :=
  ext λ s hs => by
    rw [map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
      setLIntegral_map hs hf hg]
    rfl

end MeasureTheory.Measure
