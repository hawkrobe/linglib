/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Setoid.Basic

/-!
# Kernel monotonicity and decidable equality for setoids

Mirror of `Mathlib/Data/Setoid/Basic.lean`: the composition-monotonicity
of `Setoid.ker`, and decidable equality of two setoids on a finite type whose
relations are decidable. Mathlib has the monotonicity fact for every
*algebraic* kernel — `LinearMap.ker_le_ker_comp` (whose name this mirrors),
`MonoidHom.comap_ker`, `RingHom.comap_ker`,
`CategoryTheory.Limits.kernelSubobject_comp_le` — but not for the plain
`Setoid.ker` they all specialize. [UPSTREAM]
-/

/-- If `g` factors through `f`, then the kernel of `f` refines the kernel
of `g` — the `Setoid` primitive of `LinearMap.ker_le_ker_comp`. [UPSTREAM] -/
theorem Setoid.ker_le_ker_comp {α β γ : Type*} (f : α → β) (h : β → γ) :
    Setoid.ker f ≤ Setoid.ker (h ∘ f) :=
  Setoid.le_def.mpr fun hxy => congrArg h hxy

/-- The kernel of a map into a type with decidable equality is decidable. [UPSTREAM] -/
instance Setoid.ker.decidableRel {α β : Type*} (f : α → β) [DecidableEq β] :
    DecidableRel (⇑(Setoid.ker f)) :=
  λ a b => inferInstanceAs (Decidable (f a = f b))

/-- Equality of setoids on a finite type is decided pairwise. [UPSTREAM] -/
instance Setoid.decidableEqOfDecidableRel {α : Type*} [Fintype α] (s t : Setoid α)
    [DecidableRel (⇑s)] [DecidableRel (⇑t)] : Decidable (s = t) :=
  decidable_of_iff (∀ a b, s a b ↔ t a b) Setoid.ext_iff.symm
