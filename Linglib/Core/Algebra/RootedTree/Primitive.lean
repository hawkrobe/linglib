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

The paper's dual-basis functional `δ_T` is `lcoeff R {T}`; the cut count
`countSingleCutsRho` lives with `cutSummandsN` in `Coproduct/PruningNonplanar`.

## Main results

* `ConnesKreimer.lcoeff_singleton_isDualPrimitive`: each single-tree
  delta `δ_T` is a dual primitive.
* `ConnesKreimer.lie_lcoeff_singleton_apply_ofTree`: the explicit
  count form `⁅δ_{T₁}, δ_{T₂}⁆ (ofTree T) = countSingleCutsRho T T₁ T₂ −
  countSingleCutsRho T T₂ T₁`, the Δ^ρ analog of the book's
  `c^T_{T₁,T₂} − c^T_{T₂,T₁}`. The Δ^c (trace-leaf) version follows via the
  strip machinery in `Coproduct/Deletion.lean`.

Not yet stated: the Lie algebra isomorphism with the insertion Lie algebra
(`InsertionAlgebra`); this file proves the dual-primitives side
only.
-/


namespace ConnesKreimer

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

variable {R : Type*} [CommRing R] {α : Type*} (T T₁ T₂ : Nonplanar α)

/-! ### Single-tree deltas are dual primitives -/

variable [DecidableEq α]

variable [CharZero R] [NoZeroDivisors R]

/-- The single-tree delta `δ_T = lcoeff R {T}` is a dual primitive: the
bialgebraic content of [marcolli-chomsky-berwick-2025]'s observation (book
p. 79) that primitives in the dual are exactly the single-tree deltas. -/
theorem lcoeff_singleton_isDualPrimitive :
    IsDualPrimitive R (lcoeff R ({T} : Forest (Nonplanar α))) := by
  classical
  refine ⟨by rw [← of'_zero, lcoeff_apply, coeff_of',
    if_neg (Multiset.zero_ne_singleton T)], ?_⟩
  have key : (LinearMap.mul R (ConnesKreimer R (Nonplanar α))).compr₂ (lcoeff R {T}) =
      (lcoeff R ({T} : Forest (Nonplanar α))).smulRight CoalgebraStruct.counit +
        (CoalgebraStruct.counit).smulRight (lcoeff R {T}) := by
    refine lhom_ext' fun F => lhom_ext' fun G => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.add_apply,
      LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, coalgebraCounit_apply]
    rw [← of'_add]
    simp only [lcoeff_apply, coeff_of', counit_of', ite_zero_mul_ite_zero, one_mul]
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
theorem toConv_lcoeff_singleton_mem_dualPrimitives :
    toConv (lcoeff R ({T} : Forest (Nonplanar α))) ∈
      dualPrimitives R (ConnesKreimer R (Nonplanar α)) :=
  lcoeff_singleton_isDualPrimitive T

/-! ### The explicit count formula -/

/-- The convolution product of two single-tree deltas evaluated on a
single-tree basis vector counts the Δ^ρ cut summands of `T` extracting `{T₁}`
and leaving `T₂`. -/
theorem convMul_lcoeff_singleton_apply_ofTree :
    (toConv (lcoeff R {T₁}) * toConv (lcoeff R ({T₂} : Forest (Nonplanar α))))
        (ofTree T) =
      countSingleCutsRho T T₁ T₂ := by
  classical
  rw [LinearMap.convMul_apply, coalgebra_comul_apply, comulAlgHomN_apply_ofTree, comulTreeN]
  simp only [map_add, map_multiset_sum, Multiset.map_map, Function.comp_apply,
    TensorProduct.map_tmul, LinearMap.mul'_apply, ofTree, lcoeff_apply, ← of'_zero,
    coeff_of', Multiset.singleton_inj, ite_zero_mul_ite_zero, one_mul,
    Multiset.zero_ne_singleton, if_false, mul_zero, zero_add]
  unfold countSingleCutsRho
  rw [Multiset.countP_eq_card_filter]
  induction cutSummandsN T using Multiset.induction with
  | empty => simp
  | cons q s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons, ih]
    by_cases h : q.1 = ({T₁} : Forest (Nonplanar α)) ∧ q.2 = T₂ <;> simp [h, add_comm]

/-- The commutator of two single-tree delta functionals, evaluated at a tree
`T`, is the antisymmetrized count of single Δ^ρ cuts of `T` with cut forest
`{T₁}` and remainder `T₂`. This is Lemma 1.7.3 of
[marcolli-chomsky-berwick-2025] in Δ^ρ form; the book's
`c^T_{T₁,T₂} − c^T_{T₂,T₁}` is stated for the trace-leaf coproduct `Δ^c`,
which agrees under the trace-erasure projection (`eraseTracesAlgHom`). -/
theorem lie_lcoeff_singleton_apply_ofTree :
    ⁅toConv (lcoeff R {T₁}), toConv (lcoeff R ({T₂} : Forest (Nonplanar α)))⁆
        (ofTree T) =
      (countSingleCutsRho T T₁ T₂ : R) - countSingleCutsRho T T₂ T₁ := by
  simp only [Ring.lie_def, ofConv_sub, LinearMap.sub_apply,
    convMul_lcoeff_singleton_apply_ofTree]

end ConnesKreimer

