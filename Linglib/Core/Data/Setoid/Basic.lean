/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Setoid.Basic

/-!
# Kernel monotonicity, meets, and decidable equality for setoids

This file adds to `Mathlib/Data/Setoid/Basic.lean` the monotonicity of `Setoid.ker` under
composition, the relation of an indexed meet of setoids, and decidable equality of setoids on a
finite type. Mathlib has the monotonicity for algebraic kernels (`LinearMap.ker_le_ker_comp`,
`MonoidHom.comap_ker`) but not for the plain `Setoid.ker` they specialize. [UPSTREAM]
-/

@[expose] public section

/-- If `g` factors through `f`, then the kernel of `f` refines the kernel
of `g` — the `Setoid` primitive of `LinearMap.ker_le_ker_comp`. [UPSTREAM] -/
theorem Setoid.ker_le_ker_comp {α β γ : Type*} (f : α → β) (h : β → γ) :
    Setoid.ker f ≤ Setoid.ker (h ∘ f) :=
  Setoid.le_def.mpr fun hxy => congrArg h hxy

/-- Two elements are related by an indexed meet of setoids when every setoid relates them.
[UPSTREAM] -/
theorem Setoid.iInf_iff {α : Type*} {ι : Sort*} {f : ι → Setoid α} {a b : α} :
    (⨅ i, f i) a b ↔ ∀ i, f i a b := by
  rw [iInf, Setoid.sInf_iff]
  simp

/-- The kernel of a map into a type with decidable equality is decidable. [UPSTREAM] -/
instance Setoid.ker.decidableRel {α β : Type*} (f : α → β) [DecidableEq β] :
    DecidableRel (⇑(Setoid.ker f)) :=
  λ a b => inferInstanceAs (Decidable (f a = f b))

/-- Equality of setoids on a finite type is decided pairwise. [UPSTREAM] -/
instance Setoid.decidableEqOfDecidableRel {α : Type*} [Fintype α] (s t : Setoid α)
    [DecidableRel (⇑s)] [DecidableRel (⇑t)] : Decidable (s = t) :=
  decidable_of_iff (∀ a b, s a b ↔ t a b) Setoid.ext_iff.symm
