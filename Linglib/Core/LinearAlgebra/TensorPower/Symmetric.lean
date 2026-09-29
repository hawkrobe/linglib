/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-!
# The universal property of the symmetric tensor power

A multilinear map `f : (ι → M) → N` invariant under permutations of its arguments descends to a
linear map `SymmetricPower.lift f hf : Sym[R] ι M →ₗ[R] N`, and linear maps out of `Sym[R] ι M`
are determined by their values on `⨂ₛ[R] i, x i` (`SymmetricPower.ext`). This is the universal
property TODO of `Mathlib/LinearAlgebra/TensorPower/Symmetric.lean`.

## Implementation notes

The symmetry hypothesis has the shape of the field `SymmetricMap.map_perm'` of mathlib4#41426,
whose dependent mathlib4#41444 packages `lift` as a linear equivalence out of symmetric
multilinear maps. This file is a stand-in until those land.
-/

@[expose] public section

namespace SymmetricPower

open TensorProduct Equiv

universe u v w
variable {R ι : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

@[simp]
theorem mk_tprod (x : ι → M) : mk R ι M (PiTensorProduct.tprod R x) = tprod R x :=
  rfl

/-- A multilinear map `(ι → M) → N` invariant under permutations of its arguments descends to a
linear map `Sym[R] ι M →ₗ[R] N`. -/
def lift (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (hf : ∀ (x : ι → M) (σ : Perm ι), f (fun i ↦ x (σ i)) = f x) : Sym[R] ι M →ₗ[R] N where
  toFun := AddCon.lift _ (PiTensorProduct.lift f).toAddMonoidHom <| AddCon.addConGen_le.2 <| by
    rintro _ _ ⟨σ, x⟩
    simpa [AddCon.ker_rel] using (hf x σ).symm
  map_add' := map_add _
  map_smul' r x := by
    induction x using AddCon.induction_on with
    | H y => exact map_smul (PiTensorProduct.lift f) r y

variable {f : MultilinearMap R (fun _ : ι ↦ M) N}
  {hf : ∀ (x : ι → M) (σ : Perm ι), f (fun i ↦ x (σ i)) = f x}

@[simp]
theorem lift_tprod (x : ι → M) : lift f hf (tprod R x) = f x :=
  PiTensorProduct.lift.tprod x

@[simp]
theorem lift_comp_tprod : (lift f hf).compMultilinearMap (tprod R) = f :=
  MultilinearMap.ext fun x ↦ lift_tprod (hf := hf) x

/-- Two linear maps out of `Sym[R] ι M` that agree on `⨂ₛ[R] i, x i` are equal. -/
@[ext]
theorem ext {g₁ g₂ : Sym[R] ι M →ₗ[R] N}
    (h : g₁.compMultilinearMap (tprod R) = g₂.compMultilinearMap (tprod R)) : g₁ = g₂ :=
  LinearMap.ext_on (span_tprod_eq_top R ι M) <| by
    rintro _ ⟨x, rfl⟩
    exact congr($h x)

end SymmetricPower
