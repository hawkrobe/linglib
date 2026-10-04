/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The antipode of a commutative Hopf algebra is an involution

In the convolution group `WithConv (A →ₐ[R] A)` of a commutative Hopf algebra `A`, the inverse of
`f` is `f ∘ S`. So the antipode `S` is the inverse of the identity, `S ∘ S` is the inverse of `S`,
and `S ∘ S` is the identity.

[UPSTREAM] Belongs in `Mathlib/RingTheory/HopfAlgebra/Convolution.lean`, settling the TODO on
commutative Hopf algebras in `Mathlib/RingTheory/HopfAlgebra/Basic.lean`.

## References

* [grinberg-reiner-2020]
-/

@[expose] public section

namespace HopfAlgebra

open WithConv

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]

theorem antipodeAlgHom_comp_antipodeAlgHom :
    (antipodeAlgHom R A).comp (antipodeAlgHom R A) = .id R A :=
  congr(ofConv $(inv_inv (toConv (AlgHom.id R A))))

/-- See Corollary 1.4.12 in [grinberg-reiner-2020]. -/
@[simp]
theorem antipode_antipode (a : A) : antipode R (antipode R a) = a :=
  congr($antipodeAlgHom_comp_antipodeAlgHom a)

theorem antipode_involutive : Function.Involutive (antipode R : A → A) :=
  antipode_antipode

end HopfAlgebra
