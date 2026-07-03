/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Setoid.Basic

/-!
# Kernel monotonicity for setoids

Mirror of `Mathlib/Data/Setoid/Basic.lean`: the composition-monotonicity
of `Setoid.ker`. Mathlib has this fact for every *algebraic* kernel —
`LinearMap.ker_le_ker_comp` (whose name this mirrors), `MonoidHom.comap_ker`,
`RingHom.comap_ker`, `CategoryTheory.Limits.kernelSubobject_comp_le` — but
not for the plain `Setoid.ker` they all specialize. [UPSTREAM]
-/

/-- If `g` factors through `f`, then the kernel of `f` refines the kernel
of `g` — the `Setoid` primitive of `LinearMap.ker_le_ker_comp`. [UPSTREAM] -/
theorem Setoid.ker_le_ker_comp {α β γ : Type*} (f : α → β) (h : β → γ) :
    Setoid.ker f ≤ Setoid.ker (h ∘ f) :=
  Setoid.le_def.mpr fun hxy => congrArg h hxy
