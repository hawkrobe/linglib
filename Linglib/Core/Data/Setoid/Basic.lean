/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Setoid.Basic

/-!
# Kernel monotonicity for setoids

Mirror of `Mathlib/Data/Setoid/Basic.lean`: the composition-monotonicity
of `Setoid.ker`, which mathlib currently lacks. [UPSTREAM]
-/

/-- If `g` factors through `f`, then the kernel of `f` refines the kernel
of `g`. [UPSTREAM] -/
theorem Setoid.ker_le_ker_comp {α β γ : Type*} (f : α → β) (h : β → γ) :
    Setoid.ker f ≤ Setoid.ker (h ∘ f) :=
  Setoid.le_def.mpr fun hxy => congrArg h hxy
