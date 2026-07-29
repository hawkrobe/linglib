/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.FreeMonoid.FreeSemigroup`, where
`FreeMonoid.equivWithOneFreeSemigroup` already lives.
-/
import Mathlib.Algebra.FreeMonoid.FreeSemigroup
import Mathlib.Algebra.Group.WithOne.Basic

/-!
# Transporting a free-semigroup homomorphism to the free monoid

A homomorphism out of `FreeSemigroup α` extends to one out of `FreeMonoid α` by adjoining an
identity to its codomain. Composing `WithOne.lift` — the universal property of `WithOne` — with
`FreeMonoid.equivWithOneFreeSemigroup` gives that extension directly.

The empty word is sent to `1`, so statements quantified over two-sided contexts need no case
analysis on whether a context is empty: the missing factor is the identity.
-/

namespace FreeSemigroup

variable {α T : Type*} [Semigroup T] (η : FreeSemigroup α →ₙ* T)

/-- A free-semigroup homomorphism, extended to the free monoid by adjoining an identity to its
codomain. -/
noncomputable def toWithOneHom : FreeMonoid α →* WithOne T :=
  (WithOne.lift (WithOne.coeMulHom.comp η)).comp
    FreeMonoid.equivWithOneFreeSemigroup.toMonoidHom

@[simp] theorem toWithOneHom_one : toWithOneHom η 1 = 1 := map_one _

@[simp] theorem toWithOneHom_of (x : α) :
    toWithOneHom η (FreeMonoid.of x) = (η (of x) : WithOne T) := by
  simp [toWithOneHom, FreeMonoid.equivWithOneFreeSemigroup]

@[simp] theorem toWithOneHom_toFreeMonoid (u : FreeSemigroup α) :
    toWithOneHom η (toFreeMonoid u) = (η u : WithOne T) := by
  induction u using FreeSemigroup.recOnMul with
  | ih1 x => simp
  | ih2 x y _ hy => simp [map_mul, hy]

end FreeSemigroup
