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
# Dual primitives of a bialgebra

A linear functional `L : H →ₗ[R] R` on a bialgebra is **primitive in the
dual** when `L (x * y) = L x * ε y + ε x * L y`: the coproduct on the dual is
dual to the product on `H`, so this reads `Δ L = L ⊗ ε + ε ⊗ L` after pairing
against `x ⊗ y`.

## Main declarations

* `Bialgebra.IsDualPrimitive`: the predicate.
* `Bialgebra.IsDualPrimitive.lie`: dual primitives are closed under the
  convolution commutator bracket.
* `Bialgebra.dualPrimitives`: the dual primitives as a Lie subalgebra of the
  convolution algebra `WithConv (H →ₗ[R] R)` under the ring commutator
  bracket.

`[UPSTREAM]` candidate: mathlib has no primitives API; the structural
precedent is `Mathlib.RingTheory.Coalgebra.GroupLike`.
-/

namespace Bialgebra

open Coalgebra

section CommSemiring

variable {R : Type*} [CommSemiring R] {H : Type*} [Semiring H] [Bialgebra R H]
  {L : H →ₗ[R] R} {x y : H}

variable (R) in
/-- A linear functional `L : H →ₗ[R] R` is **primitive in the dual** of a
bialgebra `H` if `L (x * y) = L x * ε y + ε x * L y`: the coproduct on the dual
is dual to the product on `H`, so this reads `Δ L = L ⊗ ε + ε ⊗ L` after
pairing against `x ⊗ y`. -/
def IsDualPrimitive (L : H →ₗ[R] R) : Prop :=
  ∀ x y : H, L (x * y) = L x * counit y + counit x * L y

/-- A dual primitive vanishes on products of counit-less elements; in
particular on decomposable basis elements of a graded bialgebra. -/
theorem IsDualPrimitive.map_mul_eq_zero (hL : IsDualPrimitive R L)
    (hx : counit (R := R) x = 0) (hy : counit (R := R) y = 0) : L (x * y) = 0 := by
  rw [hL, hx, hy, mul_zero, zero_mul, add_zero]

end CommSemiring

/-! ### The Lie subalgebra of dual primitives -/

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

open WithConv

variable {R : Type*} [CommRing R] {H : Type*} [Semiring H] [Bialgebra R H]
  {L L₁ L₂ : H →ₗ[R] R} {x y : H}

/-- A dual primitive vanishes at `1`. -/
theorem IsDualPrimitive.map_one_eq_zero (hL : IsDualPrimitive R L) : L 1 = 0 := by
  have h : L 1 = L 1 + L 1 := by simpa using hL 1 1
  exact (add_left_cancel (a := L 1) (by rw [add_zero]; exact h)).symm

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
        rw [hM, hN]; ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      rw [𝓡y.sum_apply_mul_counit counit, 𝓡x.sum_apply_mul_counit M,
        𝓡y.sum_counit_mul_apply N, 𝓡x.sum_counit_mul_apply N,
        𝓡y.sum_apply_mul_counit M, 𝓡x.sum_apply_mul_counit counit]
      ring

/-- Dual primitives are closed under the convolution commutator bracket: the
Sweedler expansion of `⁅L₁, L₂⁆ (x * y)` produces cross terms symmetric in
`(L₁, L₂)`, which cancel in the commutator. -/
theorem IsDualPrimitive.lie (h₁ : IsDualPrimitive R L₁) (h₂ : IsDualPrimitive R L₂) :
    IsDualPrimitive R (⁅toConv L₁, toConv L₂⁆ : WithConv (H →ₗ[R] R)).ofConv := by
  intro x y
  rw [((ℛ R x).mul (ℛ R y)).lie_apply, (ℛ R x).lie_apply, (ℛ R y).lie_apply]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left, Coalgebra.Repr.mul_right,
    Finset.sum_sub_distrib]
  rw [sum_mul_expand _ _ h₁ h₂, sum_mul_expand _ _ h₂ h₁]
  ring

variable (R H) in
/-- The dual primitives of a bialgebra `H`, as a Lie subalgebra of the
convolution algebra `WithConv (H →ₗ[R] R)` under the ring commutator bracket. -/
def dualPrimitives : LieSubalgebra R (WithConv (H →ₗ[R] R)) where
  carrier := {L | IsDualPrimitive R L.ofConv}
  zero_mem' x y := by simp
  add_mem' {L₁ L₂} h₁ h₂ x y := by
    simp only [ofConv_add, LinearMap.add_apply, h₁ x y, h₂ x y]; ring
  smul_mem' c L hL x y := by
    simp only [ofConv_smul, LinearMap.smul_apply, smul_eq_mul, hL x y]; ring
  lie_mem' h₁ h₂ := h₁.lie h₂

@[simp] theorem mem_dualPrimitives {L : WithConv (H →ₗ[R] R)} :
    L ∈ dualPrimitives R H ↔ IsDualPrimitive R L.ofConv := Iff.rfl

end CommRing

end Bialgebra
