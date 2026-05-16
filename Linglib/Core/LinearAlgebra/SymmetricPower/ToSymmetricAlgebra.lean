/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.LinearAlgebra.SymmetricPower.Lift
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.FinRange

set_option autoImplicit false

/-!
# The natural map `Sym[R]^n M → SymmetricAlgebra R M`

For an `R`-module `M` and a natural number `n`, there is a canonical
linear map `Sym[R]^n M →ₗ[R] SymmetricAlgebra R M` sending a symmetric
tensor power of `n` vectors to their product in the symmetric algebra:

```
Sym[R]^n M  ∋  ⨂ₛ[R] i, g i  ↦  ι(g 0) · ι(g 1) · ⋯ · ι(g (n-1))  ∈  SymmetricAlgebra R M
```

This is symmetric (= well-defined modulo permutation of arguments)
because `SymmetricAlgebra R M` is commutative — reordering factors of a
product leaves it invariant.

## Main definitions

* `SymmetricPower.toSymmetricAlgebra n` — the linear map
  `Sym[R]^n M →ₗ[R] SymmetricAlgebra R M`.

## `[UPSTREAM]` status

Natural home: `Mathlib/LinearAlgebra/SymmetricAlgebra/Basis.lean`
sibling, or a new `Mathlib/LinearAlgebra/SymmetricAlgebra/Power.lean`.
Foundational step toward the graded iso
`SymmetricAlgebra R M ≃ₐ ⨁_n Sym[R]^n M` (Q1b.0b.2, mathlib TODO).
-/

namespace SymmetricPower

open TensorProduct Equiv

universe v
variable {R : Type} {M : Type v}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-! ## §1: The per-degree `Sym^n M → SymmetricAlgebra R M` map

For each `n`, the symmetric multilinear product
`(g : Fin n → M) ↦ ∏ᵢ ι(g i) ∈ SymmetricAlgebra R M` is symmetric (by
commutativity of `SymmetricAlgebra`) and so factors through
`Sym[R]^n M` via the universal property (`SymmetricPower.lift`). -/

/-- The multilinear product `(Fin n → M) → SymmetricAlgebra R M`,
    `g ↦ ι(g 0) · ι(g 1) · ⋯ · ι(g (n-1))`. Built as the composition of
    mathlib's `MultilinearMap.mkPiAlgebraFin` with `SymmetricAlgebra.ι`. -/
private noncomputable def productMultilinear (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ M) (SymmetricAlgebra R M) :=
  (MultilinearMap.mkPiAlgebraFin R n (SymmetricAlgebra R M)).compLinearMap
    (fun _ => SymmetricAlgebra.ι R M)

@[simp]
private theorem productMultilinear_apply (n : ℕ) (g : Fin n → M) :
    productMultilinear (R := R) (M := M) n g =
      (List.ofFn fun i => SymmetricAlgebra.ι R M (g i)).prod := by
  show (MultilinearMap.mkPiAlgebraFin R n (SymmetricAlgebra R M))
        (fun i => SymmetricAlgebra.ι R M (g i)) = _
  rw [MultilinearMap.mkPiAlgebraFin_apply]

/-- The product multilinear map is symmetric: permuting arguments
    leaves the product invariant (by commutativity of
    `SymmetricAlgebra`). -/
private theorem productMultilinear_symm (n : ℕ) (σ : Perm (Fin n)) :
    (productMultilinear (R := R) (M := M) n).domDomCongr σ =
      productMultilinear (R := R) (M := M) n := by
  ext g
  show (productMultilinear (R := R) (M := M) n) (g ∘ σ) =
       productMultilinear (R := R) (M := M) n g
  rw [productMultilinear_apply, productMultilinear_apply]
  -- Goal: (List.ofFn (fun i => ι (g (σ i)))).prod = (List.ofFn (fun i => ι (g i))).prod
  -- Use `Equiv.Perm.ofFn_comp_perm σ (fun i => ι (g i))` to get
  -- `List.ofFn ((ι ∘ g) ∘ σ) ~ List.ofFn (ι ∘ g)`, then `List.Perm.prod_eq`.
  exact (Equiv.Perm.ofFn_comp_perm σ
    (fun i => SymmetricAlgebra.ι R M (g i))).prod_eq

/-- The canonical linear map `Sym[R]^n M →ₗ[R] SymmetricAlgebra R M`.
    Sends a symmetric tensor power of `n` vectors to their product in
    the symmetric algebra. -/
noncomputable def toSymmetricAlgebra (n : ℕ) :
    Sym[R] (Fin n) M →ₗ[R] SymmetricAlgebra R M :=
  SymmetricPower.lift (productMultilinear n) (productMultilinear_symm n)

@[simp]
theorem toSymmetricAlgebra_tprod (n : ℕ) (g : Fin n → M) :
    toSymmetricAlgebra (R := R) (M := M) n (tprod R g) =
      (List.ofFn fun i => SymmetricAlgebra.ι R M (g i)).prod := by
  rw [toSymmetricAlgebra, SymmetricPower.lift_tprod, productMultilinear_apply]

/-- For `n = 1`, `toSymmetricAlgebra` recovers `ι` (composed with the
    canonical iso `Sym[R]^1 M ≅ M`).

    Specifically: `toSymmetricAlgebra 1 (tprod R (fun _ => x)) = ι(x)`. -/
@[simp]
theorem toSymmetricAlgebra_one_tprod (x : M) :
    toSymmetricAlgebra (R := R) (M := M) 1 (tprod R fun _ => x) =
      SymmetricAlgebra.ι R M x := by
  rw [toSymmetricAlgebra_tprod]
  simp

/-- For `n = 0`, `toSymmetricAlgebra` sends `tprod` of the empty function
    to `1 ∈ SymmetricAlgebra R M`. -/
@[simp]
theorem toSymmetricAlgebra_zero_tprod
    (g : Fin 0 → M) :
    toSymmetricAlgebra (R := R) (M := M) 0 (tprod R g) =
      (1 : SymmetricAlgebra R M) := by
  rw [toSymmetricAlgebra_tprod]
  simp

end SymmetricPower
