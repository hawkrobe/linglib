/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.RingTheory.Coalgebra.Basic
import Linglib.Core.RingTheory.Coalgebra.Convolution
import Linglib.Core.RingTheory.Bialgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra

/-!
# Dual-primitive functionals on a bialgebra

A linear functional `L : H →ₗ[R] R` on a bialgebra is **primitive in the
dual** if `L 1 = 0` and `L (x * y) = L x * ε y + ε x * L y`. This is the
pairing form of `Bialgebra.IsPrimitiveElem` (mathlib4#39841) for the dual of
`H`: the unit of the convolution algebra is `ε`, and the coproduct of the dual
is dual to the product on `H`, so the two conditions read `ε_∨ L = 0` and
`Δ_∨ L = 1 ⊗ L + L ⊗ 1` after pairing against `x ⊗ y`. The full linear dual
carries no coproduct, so the predicate is stated in pairing form; on the
finite dual it coincides with `IsPrimitiveElem`.

## Main declarations

* `Bialgebra.IsDualPrimitive`: the predicate, with `L 1 = 0` as a field
  (mirroring `IsSkewPrimitiveElem.counit_eq_zero`, and for the same reason:
  over a semiring it is not derivable from the product rule).
* `Bialgebra.IsDualPrimitive.lie`: closure under the convolution commutator
  bracket — the dual form of `IsPrimitiveElem.commutator`.
* `Bialgebra.dualPrimitives`: the dual primitives as a Lie subalgebra of the
  convolution algebra `WithConv (H →ₗ[R] R)`.

`[UPSTREAM]` target: `Mathlib.RingTheory.Bialgebra.Primitive` (created by
mathlib4#39841), as the dual companion of `IsPrimitiveElem`.
-/

namespace Bialgebra

open Coalgebra

section CommSemiring

variable {R : Type*} [CommSemiring R] {H : Type*} [Semiring H] [Bialgebra R H]
  {L L₁ L₂ : H →ₗ[R] R} {x y : H}

variable (R) in
/-- A linear functional `L : H →ₗ[R] R` is **primitive in the dual** of a
bialgebra `H` if `L 1 = 0` and `L (x * y) = L x * ε y + ε x * L y` — the
pairing form of `Bialgebra.IsPrimitiveElem` for the dual of `H`. -/
@[mk_iff]
structure IsDualPrimitive (L : H →ₗ[R] R) : Prop where
  /-- A dual primitive vanishes at `1` (the counit of the dual is
  evaluation at `1`). -/
  map_one_eq_zero : L 1 = 0
  /-- The derivation-like product rule (the dual comultiplication
  condition). -/
  map_mul : ∀ x y : H, L (x * y) = L x * counit y + counit x * L y

namespace IsDualPrimitive

theorem zero : IsDualPrimitive R (0 : H →ₗ[R] R) where
  map_one_eq_zero := rfl
  map_mul x y := by simp

theorem add (h₁ : IsDualPrimitive R L₁) (h₂ : IsDualPrimitive R L₂) :
    IsDualPrimitive R (L₁ + L₂) where
  map_one_eq_zero := by
    simp [h₁.map_one_eq_zero, h₂.map_one_eq_zero]
  map_mul x y := by
    simp only [LinearMap.add_apply, h₁.map_mul x y, h₂.map_mul x y]; ring

theorem smul (hL : IsDualPrimitive R L) (c : R) : IsDualPrimitive R (c • L) where
  map_one_eq_zero := by simp [hL.map_one_eq_zero]
  map_mul x y := by
    simp only [LinearMap.smul_apply, smul_eq_mul, hL.map_mul x y]; ring

/-- A dual primitive vanishes on products of counit-less elements; in
particular on decomposable basis elements of a graded bialgebra. -/
theorem map_mul_eq_zero (hL : IsDualPrimitive R L)
    (hx : counit (R := R) x = 0) (hy : counit (R := R) y = 0) : L (x * y) = 0 := by
  rw [hL.map_mul, hx, hy, mul_zero, zero_mul, add_zero]

end IsDualPrimitive

end CommSemiring

/-! ### The Lie subalgebra of dual primitives -/

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

open WithConv

variable {R : Type*} [CommRing R] {H : Type*} [Semiring H] [Bialgebra R H]
  {L L₁ L₂ : H →ₗ[R] R} {x y : H}

private theorem sum_mul_expand {ιx ιy : Type*} (𝓡x : Coalgebra.Repr R x ιx)
    (𝓡y : Coalgebra.Repr R y ιy) {M N : H →ₗ[R] R}
    (hM : IsDualPrimitive R M) (hN : IsDualPrimitive R N) :
    ∑ p ∈ 𝓡x.index ×ˢ 𝓡y.index,
        M (𝓡x.left p.1 * 𝓡y.left p.2) * N (𝓡x.right p.1 * 𝓡y.right p.2) =
      (∑ i ∈ 𝓡x.index, M (𝓡x.left i) * N (𝓡x.right i)) * counit y +
        M x * N y + N x * M y +
        counit x * ∑ j ∈ 𝓡y.index, M (𝓡y.left j) * N (𝓡y.right j) :=
  calc
    ∑ p ∈ 𝓡x.index ×ˢ 𝓡y.index,
        M (𝓡x.left p.1 * 𝓡y.left p.2) * N (𝓡x.right p.1 * 𝓡y.right p.2) =
        ∑ i ∈ 𝓡x.index, ∑ j ∈ 𝓡y.index,
          ((M (𝓡x.left i) * N (𝓡x.right i)) * (counit (𝓡y.left j) * counit (𝓡y.right j)) +
            ((M (𝓡x.left i) * counit (𝓡x.right i)) * (counit (𝓡y.left j) * N (𝓡y.right j)) +
              ((counit (𝓡x.left i) * N (𝓡x.right i)) * (M (𝓡y.left j) * counit (𝓡y.right j)) +
                (counit (𝓡x.left i) * counit (𝓡x.right i)) *
                  (M (𝓡y.left j) * N (𝓡y.right j))))) := by
      rw [Finset.sum_product]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [hM.map_mul, hN.map_mul]; ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      rw [𝓡y.sum_apply_mul_counit counit, 𝓡x.sum_apply_mul_counit M,
        𝓡y.sum_counit_mul_apply N, 𝓡x.sum_counit_mul_apply N,
        𝓡y.sum_apply_mul_counit M, 𝓡x.sum_apply_mul_counit counit]
      ring

/-- Dual primitives are closed under the convolution commutator bracket: the
Sweedler expansion of `⁅L₁, L₂⁆ (x * y)` produces cross terms symmetric in
`(L₁, L₂)`, which cancel in the commutator. The dual form of
`IsPrimitiveElem.commutator`. -/
theorem IsDualPrimitive.lie (h₁ : IsDualPrimitive R L₁) (h₂ : IsDualPrimitive R L₂) :
    IsDualPrimitive R (⁅toConv L₁, toConv L₂⁆ : WithConv (H →ₗ[R] R)).ofConv where
  map_one_eq_zero := by
    have key : ∀ M N : H →ₗ[R] R, IsDualPrimitive R M →
        (toConv M * toConv N : WithConv (H →ₗ[R] R)) 1 = 0 := fun M N hM => by
      rw [LinearMap.convMul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
        TensorProduct.map_tmul, LinearMap.mul'_apply, hM.map_one_eq_zero, zero_mul]
    rw [Ring.lie_def]
    show (toConv L₁ * toConv L₂ : WithConv (H →ₗ[R] R)) 1 -
        (toConv L₂ * toConv L₁ : WithConv (H →ₗ[R] R)) 1 = 0
    rw [key _ _ h₁, key _ _ h₂, sub_zero]
  map_mul x y := by
    rw [((ℛ R x).mul (ℛ R y)).lie_apply, (ℛ R x).lie_apply, (ℛ R y).lie_apply]
    simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left, Coalgebra.Repr.mul_right,
      Finset.sum_sub_distrib]
    rw [sum_mul_expand _ _ h₁ h₂, sum_mul_expand _ _ h₂ h₁]
    ring

variable (R H) in
/-- The dual primitives of a bialgebra `H`, as a Lie subalgebra of the
convolution algebra `WithConv (H →ₗ[R] R)` under the ring commutator bracket —
the dual-side form of the Lie algebra of primitive elements. -/
def dualPrimitives : LieSubalgebra R (WithConv (H →ₗ[R] R)) where
  carrier := {L | IsDualPrimitive R L.ofConv}
  zero_mem' := .zero
  add_mem' h₁ h₂ := h₁.add h₂
  smul_mem' c _ hL := hL.smul c
  lie_mem' h₁ h₂ := h₁.lie h₂

@[simp] theorem mem_dualPrimitives {L : WithConv (H →ₗ[R] R)} :
    L ∈ dualPrimitives R H ↔ IsDualPrimitive R L.ofConv := Iff.rfl

end CommRing

end Bialgebra
