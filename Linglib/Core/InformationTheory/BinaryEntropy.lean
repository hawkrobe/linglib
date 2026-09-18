/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.InformationTheory.Entropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Entropy of a Bernoulli measure

The entropy of the Bernoulli measure `Ber(x, y, p)` on two distinct points is the binary
entropy function `binEntropy p` of `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean`, so
the monotonicity and concavity of `binEntropy` transfer to the entropy of a two-point law.
`[UPSTREAM]` candidate for that file.
-/

open MeasureTheory ProbabilityTheory Real unitInterval

namespace InformationTheory

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The entropy of a Bernoulli measure on two distinct points is the binary entropy of its
parameter. -/
theorem measureEntropy_bernoulliMeasure {x y : S} (h : x ≠ y) (p : I) :
    Hm[Ber(x, y, p)] = binEntropy p := by
  classical
  have hx : Ber(x, y, p).real {x} = p :=
    bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton x) rfl
      (by simpa using h.symm)
  have hy : Ber(x, y, p).real {y} = 1 - p :=
    bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton y) (by simpa using h)
      rfl
  rw [measureEntropy_of_isProbabilityMeasure, binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    tsum_eq_sum (s := {x, y}), Finset.sum_pair h, hx, hy]
  intro s hs
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
  rw [bernoulliMeasure_real_apply_of_notMem_of_notMem p (measurableSet_singleton s)
    (by simpa using Ne.symm hs.1) (by simpa using Ne.symm hs.2), negMulLog_zero]

end InformationTheory
