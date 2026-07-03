/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.InformationTheory.KullbackLeibler.Basic
import Linglib.Core.Probability.ConditionalProbability

/-!
# Kullback-Leibler divergence of a conditional measure

The conditioning identity: for a probability measure `μ` and an event `s` of
nonzero mass, `klDiv (μ[|s]) μ = −log μ(s)` — Bayesian update by pure
restriction costs exactly the information content of the event.

`[UPSTREAM]` candidate for `Mathlib/InformationTheory/KullbackLeibler/`
(placement and namespace mirror `ChainRule.lean`, the directory's other
file combining `klDiv` with probability constructions).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace InformationTheory

/-- **Conditioning identity** (measure level): for a probability measure `μ`,
    the KL divergence of the conditional measure `μ[|s]` from `μ` is the
    information content of the event: `−log μ(s)`. The general core of
    [levy-2008]'s equivalence of relative-entropy difficulty and surprisal. -/
theorem klDiv_cond_self {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    {s : Set Ω} (hs : MeasurableSet s) (hs0 : μ s ≠ 0) :
    klDiv (μ[|s]) μ = ENNReal.ofReal (-Real.log (μ s).toReal) := by
  have := cond_isProbabilityMeasure (μ := μ) hs0
  rw [klDiv_of_rnDeriv_ae_const cond_absolutelyContinuous
    (rnDeriv_cond_ae_const hs hs0), ENNReal.toReal_inv, Real.log_inv]

end InformationTheory
