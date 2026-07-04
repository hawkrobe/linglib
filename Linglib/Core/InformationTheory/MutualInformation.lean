/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Mutual information of a joint measure

Mutual information is the Kullback-Leibler divergence of a joint measure from
the product of its marginals. It is reference-free — unlike entropy, it needs
no background measure — so it is stated at the level of measures; the discrete
`PMF.mutualInformation` is its `toMeasure` shadow
(`PMF.mutualInformation_eq_toReal_mutualInfo`). `[UPSTREAM]` candidate for
`Mathlib/InformationTheory/`, which has `klDiv` and `Measure.fst`/`Measure.snd`
but no mutual information.
-/

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Mutual information of a joint measure: its Kullback-Leibler divergence
    from the product of its marginals. -/
noncomputable def mutualInfo (ρ : Measure (α × β)) : ℝ≥0∞ :=
  klDiv ρ (ρ.fst.prod ρ.snd)

end InformationTheory
