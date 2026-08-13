/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningDuality
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra

/-!
# Dual primitives of a bialgebra and the single-tree delta functionals
[marcolli-chomsky-berwick-2025]

Substrate for [marcolli-chomsky-berwick-2025]'s Lemma 1.7.3 (book pp. 78-79):
the insertion Lie algebra is the Lie algebra of primitive elements in the dual
Hopf algebra of the Hopf algebra of workspaces. This file proves the
dual-primitives side on the Connes-Kreimer bialgebra with the Δ^ρ
(deletion-remainder) coproduct.

## Main definitions

* `Bialgebra.IsDualPrimitive`: a linear functional `L : H →ₗ[R] R` on a
  bialgebra is primitive in the dual when `L (x * y) = L x * ε y + ε x * L y`.
* `Bialgebra.dualPrimitives`: the dual primitives as a Lie subalgebra of the
  convolution algebra `WithConv (H →ₗ[R] R)` under the ring commutator bracket.
* `Coalgebra.Repr.mul`: Sweedler representation of a product in a bialgebra.
* `RootedTree.ConnesKreimer.deltaSingleton`: the dual-basis functional `δ_T`
  extracting the coefficient of the singleton forest `{T}`.
* `RootedTree.ConnesKreimer.countSingleCutsRho`: number of Δ^ρ cut summands of
  `T` with cut forest `{T₁}` and remainder `T₂`.

## Main results

* `Bialgebra.IsDualPrimitive.lie`: dual primitives are closed under the
  convolution commutator bracket.
* `RootedTree.ConnesKreimer.deltaSingleton_isDualPrimitive`: each single-tree
  delta `δ_T` is a dual primitive.
* `RootedTree.ConnesKreimer.lie_deltaSingleton_apply_singleton`: the explicit
  count form `⁅δ_{T₁}, δ_{T₂}⁆ (of' {T}) = countSingleCutsRho T T₁ T₂ −
  countSingleCutsRho T T₂ T₁`, the Δ^ρ analog of the book's
  `c^T_{T₁,T₂} − c^T_{T₂,T₁}`. The Δ^c (trace-leaf) version follows via the
  strip machinery in `Coproduct/DeletionNonplanar.lean`.

The `Coalgebra.Repr` and `Bialgebra` sections are general substrate and
`[UPSTREAM]` candidates — mathlib has no primitives API. Not yet stated: the
Lie algebra isomorphism with the insertion Lie algebra
(`RootedTree.InsertionAlgebra`); this file proves the dual-primitives side
only.
-/

/-! ### Sweedler representation lemmas -/

namespace Coalgebra.Repr

open Coalgebra

variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C]
  [Coalgebra R C] {ι : Type*} {a : C}

/-- Applying `L ⊗ ε` to a Sweedler representation of `a` recovers `L a`. -/
theorem sum_apply_mul_counit (𝓡 : Repr R a ι) (L : C →ₗ[R] R) :
    ∑ i ∈ 𝓡.index, L (𝓡.left i) * counit (𝓡.right i) = L a := by
  simpa only [map_sum, LinearMap.mul'_apply, mul_one] using
    congrArg (LinearMap.mul' R R) (sum_map_tmul_counit_eq L a (repr := 𝓡))

/-- Applying `ε ⊗ L` to a Sweedler representation of `a` recovers `L a`. -/
theorem sum_counit_mul_apply (𝓡 : Repr R a ι) (L : C →ₗ[R] R) :
    ∑ i ∈ 𝓡.index, counit (𝓡.left i) * L (𝓡.right i) = L a := by
  simpa only [map_sum, LinearMap.mul'_apply, one_mul] using
    congrArg (LinearMap.mul' R R) (sum_counit_tmul_map_eq L a (repr := 𝓡))

/-- Sweedler representation of a product `x * y` in a bialgebra, indexed by
pairs: `left (i, j) = left i * left j` and `right (i, j) = right i * right j`. -/
@[simps]
noncomputable def mul {H : Type*} [Semiring H] [Bialgebra R H] {x y : H}
    {ιx ιy : Type*} (𝓡x : Repr R x ιx) (𝓡y : Repr R y ιy) :
    Repr R (x * y) (ιx × ιy) where
  index := 𝓡x.index ×ˢ 𝓡y.index
  left p := 𝓡x.left p.1 * 𝓡y.left p.2
  right p := 𝓡x.right p.1 * 𝓡y.right p.2
  eq := by
    rw [Bialgebra.comul_mul, ← 𝓡x.eq, ← 𝓡y.eq, Finset.sum_product, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

open WithConv in
/-- The ring commutator bracket on the convolution algebra, evaluated through a
Sweedler representation. -/
theorem lie_apply {A : Type*} [Ring A] [Algebra R A] (𝓡 : Repr R a ι)
    (f g : WithConv (C →ₗ[R] A)) :
    ⁅f, g⁆ a =
      ∑ i ∈ 𝓡.index, (f (𝓡.left i) * g (𝓡.right i) - g (𝓡.left i) * f (𝓡.right i)) := by
  rw [Ring.lie_def]
  show (f * g) a - (g * f) a = _
  rw [𝓡.convMul_apply, 𝓡.convMul_apply, Finset.sum_sub_distrib]

end Coalgebra.Repr

/-! ### Dual primitives -/

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

/-! ### Single-tree delta functionals on Connes-Kreimer -/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

variable {R : Type*} [CommRing R] {α : Type*}

variable (R) in
/-- The dual-basis functional `δ_T` on a singleton forest: extracts the
coefficient of `{T}` from a Connes-Kreimer element. -/
noncomputable def deltaSingleton (T : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] R :=
  lcoeff ({T} : Forest (Nonplanar α))

theorem deltaSingleton_of' (T : Nonplanar α) (F : Forest (Nonplanar α))
    [Decidable (F = ({T} : Forest (Nonplanar α)))] :
    deltaSingleton R T (of' F) = if F = ({T} : Forest (Nonplanar α)) then 1 else 0 := by
  rw [deltaSingleton, lcoeff_apply, coeff_of']

@[simp] theorem deltaSingleton_of'_self (T : Nonplanar α) :
    deltaSingleton R T (of' ({T} : Forest (Nonplanar α))) = 1 := by
  classical rw [deltaSingleton_of', if_pos rfl]

theorem deltaSingleton_ofTree (T T' : Nonplanar α) [Decidable (T' = T)] :
    deltaSingleton R T (ofTree T') = if T' = T then 1 else 0 := by
  classical
  rw [show (ofTree T' : ConnesKreimer R (Nonplanar α)) =
    of' ({T'} : Forest (Nonplanar α)) from rfl, deltaSingleton_of']
  simp [Multiset.singleton_inj]

@[simp] theorem deltaSingleton_ofTree_self (T : Nonplanar α) :
    deltaSingleton R T (ofTree T) = 1 := by
  classical rw [deltaSingleton_ofTree, if_pos rfl]

@[simp] theorem deltaSingleton_one (T : Nonplanar α) :
    deltaSingleton R T (1 : ConnesKreimer R (Nonplanar α)) = 0 := by
  classical
  rw [← of'_zero, deltaSingleton_of', if_neg]
  exact fun h => by simpa using congrArg Multiset.card h

/-! ### Cut counting -/

variable [DecidableEq α]

open scoped Classical in
/-- Number of Δ^ρ cut summands of `T` whose cut forest is `{T₁}` and whose
remainder tree is `T₂` — the Δ^ρ analog of the count `c^T_{T₁,T₂}` of
[marcolli-chomsky-berwick-2025]. -/
noncomputable def countSingleCutsRho (T T₁ T₂ : Nonplanar α) : ℕ :=
  (cutSummandsN T).countP fun p => p.1 = ({T₁} : Forest (Nonplanar α)) ∧ p.2 = T₂

private theorem countSingleCutsRho_countP (T T₁ T₂ : Nonplanar α)
    [DecidablePred fun p : Forest (Nonplanar α) × Nonplanar α =>
      p.1 = ({T₁} : Forest (Nonplanar α)) ∧ p.2 = T₂] :
    countSingleCutsRho T T₁ T₂ =
      (cutSummandsN T).countP fun p => p.1 = ({T₁} : Forest (Nonplanar α)) ∧ p.2 = T₂ := by
  unfold countSingleCutsRho; congr!

private theorem sum_map_indicator {β : Type*} (s : Multiset β) (p : β → Prop)
    [DecidablePred p] :
    (s.map fun b => if p b then (1 : R) else 0).sum = s.countP p := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => by_cases h : p a <;> simp [h, ih, add_comm]

/-! ### Single-tree deltas are dual primitives -/

variable [CharZero R] [NoZeroDivisors R]

private theorem coalgebraCounit_apply (z : ConnesKreimer R (Nonplanar α)) :
    CoalgebraStruct.counit (R := R) z = counit z := rfl

/-- `δ_T` is a dual primitive: the bialgebraic content of
[marcolli-chomsky-berwick-2025]'s observation (book p. 79) that primitives in
the dual are exactly the single-tree deltas. -/
theorem deltaSingleton_isDualPrimitive (T : Nonplanar α) :
    IsDualPrimitive R (deltaSingleton R T) := by
  classical
  have key : (LinearMap.mul R (ConnesKreimer R (Nonplanar α))).compr₂ (deltaSingleton R T) =
      (deltaSingleton R T).smulRight CoalgebraStruct.counit +
        (CoalgebraStruct.counit).smulRight (deltaSingleton R T) := by
    refine lhom_ext' fun F => lhom_ext' fun G => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.add_apply,
      LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, coalgebraCounit_apply]
    rw [← of'_add]
    simp only [deltaSingleton_of', counit_of', ite_zero_mul_ite_zero, one_mul]
    have hiff : F + G = ({T} : Forest (Nonplanar α)) ↔
        (F = ({T} : Forest (Nonplanar α)) ∧ G.card = 0) ∨
          (F.card = 0 ∧ G = ({T} : Forest (Nonplanar α))) := by
      constructor
      · intro hFG
        have hcard : F.card + G.card = 1 := by
          simpa using congrArg Multiset.card hFG
        rcases Nat.add_eq_one_iff.mp hcard with ⟨hF, hG⟩ | ⟨hF, hG⟩
        · exact Or.inr ⟨hF, by rwa [Multiset.card_eq_zero.mp hF, zero_add] at hFG⟩
        · exact Or.inl ⟨by rwa [Multiset.card_eq_zero.mp hG, add_zero] at hFG, hG⟩
      · rintro (⟨rfl, hG⟩ | ⟨hF, rfl⟩)
        · rw [Multiset.card_eq_zero.mp hG, add_zero]
        · rw [Multiset.card_eq_zero.mp hF, zero_add]
    simp only [hiff]
    by_cases h₁ : F = ({T} : Forest (Nonplanar α)) ∧ G.card = 0 <;>
      by_cases h₂ : F.card = 0 ∧ G = ({T} : Forest (Nonplanar α))
    · simp_all
    · simp_all
    · simp_all
    · rw [if_neg (not_or.mpr ⟨h₁, h₂⟩), if_neg h₁, if_neg h₂, add_zero]
  intro x y
  simpa using LinearMap.congr_fun (LinearMap.congr_fun key x) y

/-- [marcolli-chomsky-berwick-2025] Lemma 1.7.3, membership form: single-tree
deltas lie in the Lie subalgebra of dual primitives (so their brackets do too,
by `LieSubalgebra.lie_mem`). -/
theorem toConv_deltaSingleton_mem_dualPrimitives (T : Nonplanar α) :
    toConv (deltaSingleton R T) ∈
      dualPrimitives R (ConnesKreimer R (Nonplanar α)) :=
  deltaSingleton_isDualPrimitive T

/-! ### The explicit count formula -/

private theorem comul_of'_singleton (T : Nonplanar α) :
    (Coalgebra.comul (R := R) (of' ({T} : Forest (Nonplanar α))) :
        ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) =
      comulTreeN T := by
  show comulAlgHomN (R := R) (of' ({T} : Forest (Nonplanar α))) = _
  rw [comulAlgHomN_apply_of']
  show comulForestN (R := R) ({T} : Forest (Nonplanar α)) = comulTreeN T
  unfold comulForestN
  rw [Multiset.map_singleton, Multiset.prod_singleton]

/-- The convolution product of two single-tree deltas evaluated on a
single-tree basis vector counts the Δ^ρ cut summands of `T` extracting `{T₁}`
and leaving `T₂`. -/
theorem convMul_deltaSingleton_apply_singleton (T T₁ T₂ : Nonplanar α) :
    (toConv (deltaSingleton R T₁) * toConv (deltaSingleton R T₂) :
        WithConv (ConnesKreimer R (Nonplanar α) →ₗ[R] R))
        (of' ({T} : Forest (Nonplanar α))) =
      countSingleCutsRho T T₁ T₂ := by
  classical
  rw [LinearMap.convMul_apply, comul_of'_singleton]
  unfold comulTreeN
  rw [map_add, map_add, map_multiset_sum, map_multiset_sum]
  simp only [Multiset.map_map, Function.comp_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply, deltaSingleton_one, mul_zero, zero_add,
    deltaSingleton_of', deltaSingleton_ofTree, ite_zero_mul_ite_zero, one_mul]
  rw [sum_map_indicator, countSingleCutsRho_countP]

/-- **[marcolli-chomsky-berwick-2025] Lemma 1.7.3** (Δ^ρ explicit form): the
commutator bracket of two single-tree deltas evaluated on a single-tree basis
vector is the antisymmetrized single-cut count, the Δ^ρ analog of the book's
`c^T_{T₁,T₂} − c^T_{T₂,T₁}`. The Δ^c (trace-leaf) version follows via the
strip bijection in `Coproduct/DeletionNonplanar.lean`. -/
theorem lie_deltaSingleton_apply_singleton (T T₁ T₂ : Nonplanar α) :
    (⁅toConv (deltaSingleton R T₁), toConv (deltaSingleton R T₂)⁆ :
        WithConv (ConnesKreimer R (Nonplanar α) →ₗ[R] R))
        (of' ({T} : Forest (Nonplanar α))) =
      (countSingleCutsRho T T₁ T₂ : R) - countSingleCutsRho T T₂ T₁ := by
  rw [Ring.lie_def]
  show (toConv (deltaSingleton R T₁) * toConv (deltaSingleton R T₂) :
        WithConv (ConnesKreimer R (Nonplanar α) →ₗ[R] R))
        (of' ({T} : Forest (Nonplanar α))) -
      (toConv (deltaSingleton R T₂) * toConv (deltaSingleton R T₁) :
        WithConv (ConnesKreimer R (Nonplanar α) →ₗ[R] R))
        (of' ({T} : Forest (Nonplanar α))) = _
  rw [convMul_deltaSingleton_apply_singleton, convMul_deltaSingleton_apply_singleton]

end ConnesKreimer

end RootedTree
