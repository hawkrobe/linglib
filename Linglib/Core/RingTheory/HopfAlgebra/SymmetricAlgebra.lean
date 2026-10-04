/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Hopf algebra structure on `SymmetricAlgebra R M`

The generators `ι R M x` of the symmetric algebra are primitive. When `M` is an additive group the
antipode is the algebra endomorphism induced by negation on `M`, over any commutative semiring
`R`: it sends a polynomial `f(x₁, …, xₙ)` to `f(-x₁, …, -xₙ)`, and over a ring it multiplies a
product of `k` generators by `(-1) ^ k`.

[UPSTREAM] Belongs in `Mathlib/RingTheory/HopfAlgebra/SymmetricAlgebra.lean`, except the `ιMulti`
lemmas, which follow `SymmetricAlgebra.ιMulti`.

## References

* [grinberg-reiner-2020]
-/

@[expose] public section

namespace SymmetricAlgebra

open Bialgebra HopfAlgebra

variable {M : Type*} {κ : Type*} [Fintype κ]

section CommSemiring

variable (R : Type*) [CommSemiring R]

theorem isPrimitiveElem_ι [AddCommMonoid M] [Module R M] (x : M) : IsPrimitiveElem R (ι R M x) where
  counit_eq_zero := counit_ι R M x
  comul_eq_tmul_add_tmul := by rw [comul_ι, add_comm]

variable [AddCommGroup M] [Module R M]

instance instHopfAlgebra : HopfAlgebra R (SymmetricAlgebra R M) :=
  .ofAlgHom (lift (ι R M ∘ₗ (-LinearMap.id)))
    (by ext x; simp [algebraMapInv_ι, ← (ι R M).map_add])
    (by ext x; simp [algebraMapInv_ι, ← (ι R M).map_add])

@[simp]
theorem antipode_ι (x : M) : antipode R (ι R M x) = ι R M (-x) :=
  lift_ι_apply _ x

theorem antipodeAlgHom_eq :
    antipodeAlgHom R (SymmetricAlgebra R M) = lift (ι R M ∘ₗ (-LinearMap.id)) :=
  rfl

/-- See Example 1.4.18 in [grinberg-reiner-2020]. -/
theorem antipode_ιMulti (x : κ → M) : antipode R (ιMulti R M κ x) = ιMulti R M κ (-x) := by
  rw [ιMulti_apply, ← antipodeAlgHom_apply, map_prod]
  simp [ιMulti_apply]

end CommSemiring

section CommRing

variable (R : Type*) [CommRing R] [AddCommGroup M] [Module R M]

theorem antipode_ιMulti_eq_smul (x : κ → M) :
    antipode R (ιMulti R M κ x) = (-1 : R) ^ Fintype.card κ • ιMulti R M κ x := by
  rw [antipode_ιMulti]
  simpa [Pi.neg_def] using (ιMulti R M κ).map_smul_univ (fun _ ↦ (-1 : R)) x

end CommRing

end SymmetricAlgebra
