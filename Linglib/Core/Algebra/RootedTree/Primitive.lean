/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningDuality
import Linglib.Core.RingTheory.Bialgebra.Primitive

open RoseTree RoseTree.Nonplanar

/-!
# Dual-primitive functionals on the Connes-Kreimer bialgebra
[marcolli-chomsky-berwick-2025]

Substrate for [marcolli-chomsky-berwick-2025]'s Lemma 1.7.3 (book pp. 78-79):
the insertion Lie algebra is the Lie algebra of primitive elements in the dual
Hopf algebra of the Hopf algebra of workspaces. This file proves the
dual-primitives side on the Connes-Kreimer bialgebra with the Δ^ρ
(deletion-remainder) coproduct, specializing the general
`Bialgebra.dualPrimitives` theory of `Core/RingTheory/Bialgebra/Primitive`.

## Main definitions

* `ConnesKreimer.deltaSingleton`: the dual-basis functional `δ_T`
  extracting the coefficient of the singleton forest `{T}`.
* `ConnesKreimer.countSingleCutsRho`: number of Δ^ρ cut summands of
  `T` with cut forest `{T₁}` and remainder `T₂`.

## Main results

* `ConnesKreimer.deltaSingleton_isDualPrimitive`: each single-tree
  delta `δ_T` is a dual primitive.
* `ConnesKreimer.lie_deltaSingleton_apply_ofTree`: the explicit
  count form `⁅δ_{T₁}, δ_{T₂}⁆ (ofTree T) = countSingleCutsRho T T₁ T₂ −
  countSingleCutsRho T T₂ T₁`, the Δ^ρ analog of the book's
  `c^T_{T₁,T₂} − c^T_{T₂,T₁}`. The Δ^c (trace-leaf) version follows via the
  strip machinery in `Coproduct/DeletionNonplanar.lean`.

Not yet stated: the Lie algebra isomorphism with the insertion Lie algebra
(`InsertionAlgebra`); this file proves the dual-primitives side
only.
-/


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
  refine ⟨deltaSingleton_one T, ?_⟩
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

private theorem comul_ofTree (T : Nonplanar α) :
    (Coalgebra.comul (R := R) (ofTree T) :
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
theorem convMul_deltaSingleton_apply_ofTree (T T₁ T₂ : Nonplanar α) :
    (toConv (deltaSingleton R T₁) * toConv (deltaSingleton R T₂)) (ofTree T) =
      countSingleCutsRho T T₁ T₂ := by
  classical
  rw [LinearMap.convMul_apply, comul_ofTree]
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
theorem lie_deltaSingleton_apply_ofTree (T T₁ T₂ : Nonplanar α) :
    ⁅toConv (deltaSingleton R T₁), toConv (deltaSingleton R T₂)⁆ (ofTree T) =
      (countSingleCutsRho T T₁ T₂ : R) - countSingleCutsRho T T₂ T₁ := by
  simp only [Ring.lie_def, ofConv_sub, LinearMap.sub_apply,
    convMul_deltaSingleton_apply_ofTree]

end ConnesKreimer

