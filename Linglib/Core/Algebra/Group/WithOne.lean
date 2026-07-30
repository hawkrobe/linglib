/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.WithOne.Basic`.
-/
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Data.Fintype.Option

/-!
# Finiteness and surjectivity for `WithOne`

`WithOne α` is finite when `α` is, and `WithOne.lift f` is surjective exactly when `1` and the
range of `f` cover the target.
-/

namespace WithOne

variable {α M : Type*}

instance [Finite α] : Finite (WithOne α) := inferInstanceAs (Finite (Option α))

theorem lift_surjective [Mul α] [MulOneClass M] {f : α →ₙ* M} :
    Function.Surjective (lift f) ↔ ∀ m, m = 1 ∨ m ∈ Set.range f := by
  constructor
  · rintro h m
    obtain ⟨x, rfl⟩ := h m
    induction x with
    | one => exact .inl (map_one _)
    | coe a => exact .inr ⟨a, (lift_coe f a).symm⟩
  · rintro h m
    rcases h m with rfl | ⟨a, rfl⟩
    exacts [⟨1, map_one _⟩, ⟨a, lift_coe f a⟩]

end WithOne
