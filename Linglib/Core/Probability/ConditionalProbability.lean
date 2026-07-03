/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Conditional measures: the Radon-Nikodym derivative

The density of `μ[|s]` with respect to `μ` is `(μ s)⁻¹` on `s` and `0` off it.
`[UPSTREAM]` candidates; the upstream home is either
`MeasureTheory/Measure/Decomposition/Lebesgue.lean` (following
`rnDeriv_restrict_self`) or a `Probability/` leaf importing the decomposition.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {s : Set Ω}

/-- The density of the conditional measure: `(μ s)⁻¹` on `s`, `0` off it. -/
theorem rnDeriv_cond [SigmaFinite μ] (hs : MeasurableSet s) (hs0 : μ s ≠ 0) :
    (μ[|s]).rnDeriv μ =ᵐ[μ] s.indicator fun _ => (μ s)⁻¹ := by
  have h1 : ((μ s)⁻¹ • μ.restrict s).rnDeriv μ
      =ᵐ[μ] (μ s)⁻¹ • (μ.restrict s).rnDeriv μ :=
    Measure.rnDeriv_smul_left_of_ne_top' _ _ (ENNReal.inv_ne_top.mpr hs0)
  refine h1.trans ((Measure.rnDeriv_restrict_self μ hs).mono fun x hx => ?_)
  rw [Pi.smul_apply, hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- On its own event, the conditional measure's density is the constant
    `(μ s)⁻¹`. -/
theorem rnDeriv_cond_ae_const [SigmaFinite μ] (hs : MeasurableSet s)
    (hs0 : μ s ≠ 0) : (μ[|s]).rnDeriv μ =ᵐ[μ[|s]] fun _ => (μ s)⁻¹ := by
  filter_upwards [cond_absolutelyContinuous.ae_eq (rnDeriv_cond hs hs0),
    ae_cond_mem hs] with x hx hxs
  rw [hx, Set.indicator_of_mem hxs]

end ProbabilityTheory
