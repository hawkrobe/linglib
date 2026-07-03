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

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {s : Set Ω}

/-- The conditional measure `μ[|s]` is `μ` with density `(μ s)⁻¹` on `s`
and `0` off it. -/
theorem cond_eq_withDensity (hs : MeasurableSet s) :
    μ[|s] = μ.withDensity (s.indicator fun _ => (μ s)⁻¹) :=
  ((withDensity_indicator hs _).trans (withDensity_const _)).symm

/-- The Radon-Nikodym derivative of the conditional measure `μ[|s]` with
respect to `μ` is `(μ s)⁻¹` on `s` and `0` off it. -/
theorem rnDeriv_cond [SigmaFinite μ] (hs : MeasurableSet s) :
    (μ[|s]).rnDeriv μ =ᵐ[μ] s.indicator fun _ => (μ s)⁻¹ :=
  cond_eq_withDensity hs ▸ Measure.rnDeriv_withDensity μ (measurable_const.indicator hs)

/-- On its own event, the conditional measure's density is the constant `(μ s)⁻¹`. -/
theorem rnDeriv_cond_ae_const [SigmaFinite μ] (hs : MeasurableSet s) :
    (μ[|s]).rnDeriv μ =ᵐ[μ[|s]] fun _ => (μ s)⁻¹ :=
  (cond_absolutelyContinuous.ae_eq (rnDeriv_cond hs)).trans <|
    (ae_cond_mem hs).mono fun _ hx => Set.indicator_of_mem hx _

end ProbabilityTheory
