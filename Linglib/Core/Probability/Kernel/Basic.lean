/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Kernels between countable spaces

Every measure on a countable type is s-finite, and every kernel out of a countable type with
measurable singletons is a countable sum of the kernels concentrated at one point, so every
kernel between two countable types is s-finite. `[UPSTREAM]` candidate for
`Mathlib/Probability/Kernel/Basic.lean`.
-/

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

open scoped Classical in
/-- A kernel out of a countable type is the sum over points `a` of the kernel that is `κ a` at
`a` and `0` elsewhere. -/
theorem sum_piecewise_singleton_const [Countable α] [MeasurableSingletonClass α]
    (κ : Kernel α β) :
    (Kernel.sum fun a => piecewise (measurableSet_singleton a) (const α (κ a)) 0) = κ := by
  ext a s hs
  rw [sum_apply' _ _ hs, tsum_eq_single a fun n hn => by simp [piecewise_apply, Ne.symm hn]]
  simp [piecewise_apply]

instance [Countable α] [MeasurableSingletonClass α] [Countable β] (κ : Kernel α β) :
    IsSFiniteKernel κ := by
  rw [← sum_piecewise_singleton_const κ]
  infer_instance

end ProbabilityTheory.Kernel
