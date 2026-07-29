/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.GroupTheory.Congruence.Syntactic`.
-/
import Mathlib.GroupTheory.Congruence.Basic

/-!
# The syntactic congruence of a subset of a monoid

Two elements are *syntactically congruent* for `P` when no two-sided context distinguishes their
membership. The quotient is the coarsest one on which membership of `P` is well defined, which is
the content of `Set.le_syntacticCon`.

This is the general form of the definition ([pin-mfa] states it for a subset of a semigroup, with
contexts ranging over the monoid obtained by adjoining an identity); languages are the case
`M = FreeMonoid α`.
-/

namespace Set

variable {M : Type*} [Monoid M] {P : Set M} {s t : M}

/-- The *syntactic congruence* of `P` identifies elements that no two-sided context separates. -/
def syntacticCon (P : Set M) : Con M where
  r s t := ∀ x y : M, x * s * y ∈ P ↔ x * t * y ∈ P
  iseqv := ⟨fun _ _ _ => Iff.rfl, fun h x y => (h x y).symm,
    fun h h' x y => (h x y).trans (h' x y)⟩
  mul' := fun {a b c d} h h' x y => by
    have h1 := h x (c * y)
    have h2 := h' (x * b) y
    simp only [← mul_assoc] at h1 h2 ⊢
    exact h1.trans h2

theorem syntacticCon_iff : P.syntacticCon s t ↔ ∀ x y : M, x * s * y ∈ P ↔ x * t * y ∈ P := Iff.rfl

theorem mem_iff_of_syntacticCon (h : P.syntacticCon s t) : s ∈ P ↔ t ∈ P := by simpa using h 1 1

/-- The syntactic congruence is the coarsest congruence saturating `P`. -/
theorem le_syntacticCon {c : Con M} (h : ∀ ⦃s t⦄, c s t → (s ∈ P ↔ t ∈ P)) :
    c ≤ P.syntacticCon :=
  fun {_ _} hst x y => h (c.mul (c.mul (c.refl x) hst) (c.refl y))

end Set
