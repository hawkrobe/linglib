/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Graded truth from a prior on a parameter

For a predicate `φ : Θ → E → Prop` depending on a parameter `θ : Θ` and a prior `μ : Measure Θ`,
`gradedTruth μ φ x` is the mass `μ.real {θ | φ θ x}` of the parameters at which `φ x` holds. The
threshold of a gradable adjective or the reading of a clause-embedding predicate are such
parameters: each `φ θ` is Boolean, and the graded value comes from the prior.

## Main definitions

* `Probabilistic.gradedTruth μ φ x`: the graded truth value `μ.real {θ | φ θ x}`.

## Main results

* `Probabilistic.gradedTruth_dirac`: under the Dirac prior at `θ₀`, the graded truth value is `1`
  if `φ θ₀ x` holds and `0` otherwise.
* `Probabilistic.gradedTruth_mono`, `Probabilistic.gradedTruth_compl`: monotonicity in the
  predicate, and the value of the negated predicate.

## References

* [D. Lassiter and N. D. Goodman, *Adjectival vagueness in a Bayesian model of
  interpretation*][lassiter-goodman-2017]
* [J. Grove and A. S. White, *Factivity, presupposition projection, and the role of discrete
  knowledge in gradient inference judgments*][grove-white-2025]
-/

open MeasureTheory

namespace Probabilistic

variable {Θ E : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (φ ψ : Θ → E → Prop) (x : E)

/-- The graded truth of the parametric predicate `φ` at `x` under the prior `μ`: the prior's
mass on the parameters that make `φ x` true. -/
noncomputable def gradedTruth : ℝ := μ.real {θ | φ θ x}

theorem gradedTruth_nonneg : 0 ≤ gradedTruth μ φ x := measureReal_nonneg

theorem gradedTruth_le_one [IsProbabilityMeasure μ] : gradedTruth μ φ x ≤ 1 :=
  measureReal_le_one

/-- Graded truth respects entailment between parametric predicates. -/
theorem gradedTruth_mono [IsFiniteMeasure μ] (h : ∀ θ, φ θ x → ψ θ x) :
    gradedTruth μ φ x ≤ gradedTruth μ ψ x :=
  measureReal_mono (fun _ hθ => h _ hθ) (measure_ne_top _ _)

/-- The graded truth of a negated predicate is the complementary mass. -/
theorem gradedTruth_compl [IsProbabilityMeasure μ] (hφ : MeasurableSet {θ | φ θ x}) :
    gradedTruth μ (fun θ x => ¬ φ θ x) x = 1 - gradedTruth μ φ x := by
  rw [gradedTruth, gradedTruth, show {θ | ¬ φ θ x} = {θ | φ θ x}ᶜ from rfl,
    measureReal_compl hφ, probReal_univ]

/-- With no uncertainty about the parameter, graded truth is Boolean truth. -/
theorem gradedTruth_dirac [MeasurableSingletonClass Θ] (θ₀ : Θ) [Decidable (φ θ₀ x)] :
    gradedTruth (Measure.dirac θ₀) φ x = if φ θ₀ x then 1 else 0 := by
  rw [gradedTruth, measureReal_def, Measure.dirac_apply]
  split_ifs with h
  · rw [Set.indicator_of_mem (show θ₀ ∈ {θ | φ θ x} from h), Pi.one_apply, ENNReal.toReal_one]
  · rw [Set.indicator_of_notMem (show θ₀ ∉ {θ | φ θ x} from h), ENNReal.toReal_zero]

end Probabilistic
