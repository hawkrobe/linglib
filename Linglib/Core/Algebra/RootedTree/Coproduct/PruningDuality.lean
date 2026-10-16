/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.BigOperators.Multiset
public import Linglib.Core.Algebra.RootedTree.BMinus
public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Duality of the Grossman–Larson product and the pruning coproduct

Under the symmetry-weighted pairing, the Grossman–Larson product is the transpose of the pruning
coproduct `Δ^ρ`: `⟨x ⋆ y, z⟩ = ⟨y ⊗ x, Δ^ρ z⟩`. So the pairing turns the Grossman–Larson product
into the convolution product of linear functionals on the Connes–Kreimer bialgebra, in the
opposite order. Hoffman states the duality in this form, as a map of the Grossman–Larson algebra
to the graded dual.

## Main results

* `ConnesKreimer.pairing_gl_eq_pairing_coproduct_Rho`: the duality
  `⟨x ⋆ y, z⟩ = pairing₂ (y ⊗ x) (Δ^ρ z)`.
* `ConnesKreimer.toConv_pairing_product`: `⟨x ⋆ y, ·⟩ = ⟨y, ·⟩ * ⟨x, ·⟩` in the convolution
  algebra of linear functionals.
* `ConnesKreimer.pairing_product_assoc`: the two triple products pair equally against everything,
  since the convolution product is associative.

## Implementation notes

The tensor slots of the duality are crossed. The product `x ⋆ y` grafts the trees of `y` onto the
host `x`, while `Δ^ρ` puts the pruned crown in the first tensor slot and the trunk in the second,
so `y` pairs against crowns and `x` against trunks. The uncrossed statement is false: for the
one-vertex trees `x = •_p` and `y = •_q` and the chain `z` with root `p` and leaf `q`, the left
side is `1` and `pairing₂ (x ⊗ y) (Δ^ρ z)` is `0`.

The duality is proved by strong induction on the total weight of a basis forest `z = of' C`. The
one-tree step uses the adjunction of `B⁺` and `B⁻` (`BMinus.lean`) and the Hochschild cocycle
property; the step for several trees uses the product rule of the pairing.

## References

* [foissy-2002]
* [oudom-guin-2008]
* [hoffman-2003]
-/

@[expose] public section

open RoseTree UnorderedTree WithConv

namespace ConnesKreimer

open scoped TensorProduct
open GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### Adjoint through the second tensor slot -/

/-- `B⁺_a` on the second tensor factor transposes to `B⁻_a` on the second slot of `pairing₂`. -/
private lemma pairing₂_lTensor_bPlusLin (a : α)
    (u v : ConnesKreimer R (UnorderedTree α))
    (V : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    pairing₂ (R := R) (u ⊗ₜ[R] v)
        ((LinearMap.lTensor _ (bPlusLin (R := R) a)) V) =
      pairing₂ (R := R) (u ⊗ₜ[R] (bMinusLin (R := R) a v)) V := by
  induction V using TensorProduct.inductionOn with
  | tmul p q =>
    rw [LinearMap.lTensor_tmul, pairing₂_tmul_tmul, pairing₂_tmul_tmul,
        ← bMinusLin_pairing_adjoint]
  | add V₁ V₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

/-! ### Tensor-square of the pairing product rule -/

/-- The product rule of the pairing holds through both slots of `pairing₂`, where pairing two
basis forests against a product splits each of them over its antidiagonal. -/
private lemma pairing₂_of'_of'_mul (A B : Forest (UnorderedTree α))
    (U V : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    pairing₂ (R := R) (ConnesKreimer.of' B ⊗ₜ[R] ConnesKreimer.of' A) (U * V) =
      ((Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).map (fun pq =>
        pairing₂ (R := R)
            (ConnesKreimer.of' pq.2.1 ⊗ₜ[R] ConnesKreimer.of' pq.1.1) U *
        pairing₂ (R := R)
            (ConnesKreimer.of' pq.2.2 ⊗ₜ[R] ConnesKreimer.of' pq.1.2) V)).sum := by
  induction U using TensorProduct.inductionOn with
  | add U₁ U₂ ih₁ ih₂ =>
    rw [add_mul, map_add, ih₁, ih₂, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun pq _ => ?_)
    rw [map_add, add_mul]
  | tmul u₁ u₂ =>
    induction V using TensorProduct.inductionOn with
    | add V₁ V₂ ih₁ ih₂ =>
      rw [mul_add, map_add, ih₁, ih₂, ← Multiset.sum_map_add]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun pq _ => ?_)
      rw [map_add, mul_add]
    | tmul v₁ v₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairing₂_tmul_tmul,
          pairing_of'_mul B u₁ v₁,
          pairing_of'_mul A u₂ v₂]
      rw [show ((Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).map (fun pq =>
            pairing₂ (R := R)
                (ConnesKreimer.of' pq.2.1 ⊗ₜ[R] ConnesKreimer.of' pq.1.1)
                (u₁ ⊗ₜ[R] u₂) *
            pairing₂ (R := R)
                (ConnesKreimer.of' pq.2.2 ⊗ₜ[R] ConnesKreimer.of' pq.1.2)
                (v₁ ⊗ₜ[R] v₂))) =
          ((Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).map (fun pq =>
            (pairing (R := R)
                (ConnesKreimer.of' pq.1.1) u₂ *
             pairing (R := R)
                (ConnesKreimer.of' pq.1.2) v₂) *
            (pairing (R := R)
                (ConnesKreimer.of' pq.2.1) u₁ *
             pairing (R := R)
                (ConnesKreimer.of' pq.2.2) v₁))) from
        Multiset.map_congr rfl fun pq _ => by
          rw [pairing₂_tmul_tmul, pairing₂_tmul_tmul]; ring]
      rw [Multiset.sum_map_product_mul (Multiset.antidiagonal A)
          (Multiset.antidiagonal B)
          (fun pa => pairing (R := R)
              (ConnesKreimer.of' pa.1) u₂ *
            pairing (R := R) (ConnesKreimer.of' pa.2) v₂)
          (fun pb => pairing (R := R)
              (ConnesKreimer.of' pb.1) u₁ *
            pairing (R := R) (ConnesKreimer.of' pb.2) v₁)]
      ring

/-! ### The duality theorem -/

/-- The Grossman–Larson product is the transpose of the pruning coproduct under the
symmetry-weighted pairing, `⟨x ⋆ y, z⟩ = pairing₂ (y ⊗ x) (Δ^ρ z)`. The tensor slots are crossed:
the grafted factor `y` pairs against the pruned crowns and the host `x` against the trunks. -/
theorem pairing_gl_eq_pairing_coproduct_Rho (x y z : ConnesKreimer R (UnorderedTree α)) :
    pairing (product x y) z = pairing₂ (R := R) (y ⊗ₜ[R] x) (comulAlgHomN (R := R) z) := by
  -- Core statement at basis `z = of' C`, strong induction on total weight.
  suffices core : ∀ (n : ℕ) (C : Forest (UnorderedTree α)),
      (C.map UnorderedTree.numNodes).sum = n →
      ∀ x y : ConnesKreimer R (UnorderedTree α),
      pairing (R := R)
          (product x y) (ConnesKreimer.of' C) =
        pairing₂ (R := R) (y ⊗ₜ[R] x)
          (comulAlgHomN (R := R) (ConnesKreimer.of' C)) by
    have h : pairing (R := R) (product x y) =
        (pairing₂ (R := R) (y ⊗ₜ[R] x)).comp
          (comulAlgHomN (R := R)).toLinearMap :=
      ConnesKreimer.lhom_ext' fun C => core _ C rfl x y
    exact LinearMap.congr_fun h z
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro C hC x y
    rcases Multiset.empty_or_exists_mem C with hC0 | ⟨T, hT⟩
    · -- Base: C = 0, both sides are counits.
      subst hC0
      rw [ConnesKreimer.of'_zero,
          show comulAlgHomN (R := R) (1 : ConnesKreimer R (UnorderedTree α)) = 1 from
            map_one _,
          show (1 : ConnesKreimer R (UnorderedTree α) ⊗[R]
              ConnesKreimer R (UnorderedTree α)) =
            (1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R]
              (1 : ConnesKreimer R (UnorderedTree α)) from
            Algebra.TensorProduct.one_def,
          pairing₂_tmul_tmul, pairing_one_right, pairing_one_right,
          pairing_one_right]
      rw [counit_product]
      exact mul_comm _ _
    · obtain ⟨C', rfl⟩ := Multiset.exists_cons_of_mem hT
      rcases Multiset.empty_or_exists_mem C' with hC'0 | ⟨T₂, hT₂⟩
      · -- Single tree: C = {T}, T = B⁺_a W; the B⁻ recurrences match.
        subst hC'0
        -- Weight bookkeeping: (children T) is one lighter than T.
        have hwT : ((T ::ₘ (0 : Forest (UnorderedTree α))).map
            UnorderedTree.numNodes).sum = T.numNodes := by
          rw [Multiset.map_cons, Multiset.map_zero, Multiset.sum_cons,
              Multiset.sum_zero]
          omega
        have hTn : T.numNodes = n := by rw [← hwT, hC]
        have hwW : T.numNodes =
            ((UnorderedTree.children T).map UnorderedTree.numNodes).sum + 1 := by
          conv_lhs => rw [← UnorderedTree.node_eta T]
          rw [UnorderedTree.numNodes_node]
        have hWlt : ((UnorderedTree.children T).map UnorderedTree.numNodes).sum < n := by
          omega
        -- Convert `of' {T}` to `B⁺_a (of' W)`.
        have hofT : (ConnesKreimer.of' (R := R) (T ::ₘ (0 : Forest (UnorderedTree α))) :
            ConnesKreimer R (UnorderedTree α)) =
            bPlusLin (R := R) (UnorderedTree.value T)
              (ConnesKreimer.of' (UnorderedTree.children T)) := by
          rw [bPlusLin_of', UnorderedTree.node_eta]
          rfl
        rw [hofT]
        -- LHS: the B⁺/B⁻ recurrence.
        rw [pairing_apply_bPlus_gl_mul]
        -- RHS: the Hochschild cocycle + adjoint.
        rw [show comulAlgHomN (R := R)
              (bPlusLin (R := R) (UnorderedTree.value T)
                (ConnesKreimer.of' (UnorderedTree.children T))) =
            comulTreeN (R := R)
              (UnorderedTree.node (UnorderedTree.value T)
                (UnorderedTree.children T)) from by
          rw [bPlusLin_of', comulAlgHomN_apply_ofTree]]
        rw [comulTreeN_node_cocycle, map_add, pairing₂_tmul_tmul,
            pairing₂_lTensor_bPlusLin]
        -- Term 1: adjoint identity; Term 2: induction hypothesis.
        rw [show comulForestN (R := R) (UnorderedTree.children T) =
            comulAlgHomN (R := R)
              (ConnesKreimer.of' (UnorderedTree.children T)) from
          (comulAlgHomN_apply_of' _).symm]
        rw [← IH _ hWlt (UnorderedTree.children T) rfl
            (bMinusLin (R := R) (UnorderedTree.value T) x) y]
        rw [show (ConnesKreimer.ofTree (R := R)
              (UnorderedTree.node (UnorderedTree.value T)
                (UnorderedTree.children T)) :
              ConnesKreimer R (UnorderedTree α)) =
            bPlusLin (R := R) (UnorderedTree.value T)
              (ConnesKreimer.of' (UnorderedTree.children T)) from
          (bPlusLin_of' _ _).symm]
        rw [← bMinusLin_pairing_adjoint, pairing_one_right]
        ring
      · -- Multi-tree: C = T ::ₘ C' with C' ≠ 0; split and use both
        -- product rules + the induction hypothesis at both factors.
        -- Weight bookkeeping.
        have hsum : T.numNodes + (C'.map UnorderedTree.numNodes).sum = n := by
          rw [← hC, Multiset.map_cons, Multiset.sum_cons]
        have hT2pos : 0 < UnorderedTree.numNodes T₂ := UnorderedTree.numNodes_pos T₂
        have hC'ge : UnorderedTree.numNodes T₂ ≤ (C'.map UnorderedTree.numNodes).sum :=
          Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _
            (Multiset.mem_map_of_mem _ hT₂)
        have hTpos : 0 < T.numNodes := UnorderedTree.numNodes_pos T
        have hTlt : ((({T} : Forest (UnorderedTree α))).map UnorderedTree.numNodes).sum < n := by
          rw [Multiset.map_singleton, Multiset.sum_singleton]
          omega
        have hC'lt : (C'.map UnorderedTree.numNodes).sum < n := by omega
        -- Reduce x, y to basis vectors (both sides are bilinear in (x, y)).
        refine ConnesKreimer.induction_linear x ?_ ?_ ?_
        · simp only [TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply]
        · intro a b iha ihb
          simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply]
          exact congrArg₂ (· + ·) iha ihb
        · intro A rA
          rw [← ConnesKreimer.smul_of']
          simp only [TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply]
          refine congrArg (rA • ·) ?_
          refine ConnesKreimer.induction_linear y ?_ ?_ ?_
          · simp only [TensorProduct.zero_tmul, map_zero, LinearMap.zero_apply]
          · intro a b iha ihb
            simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply]
            exact congrArg₂ (· + ·) iha ihb
          · intro B rB
            rw [← ConnesKreimer.smul_of']
            simp only [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply]
            refine congrArg (rB • ·) ?_
            -- Basis case: split off the head tree and use both product rules.
            have hsplit : (ConnesKreimer.of' (R := R) (T ::ₘ C') :
                ConnesKreimer R (UnorderedTree α)) =
                ConnesKreimer.of' ({T} : Forest (UnorderedTree α)) *
                  ConnesKreimer.of' C' := by
              rw [← ConnesKreimer.of'_add, Multiset.singleton_add]
            rw [hsplit, pairing_product_of'_mul_of',
                map_mul, pairing₂_of'_of'_mul]
            refine congrArg Multiset.sum (Multiset.map_congr rfl fun pq _ => ?_)
            rw [IH _ hTlt ({T} : Forest (UnorderedTree α)) rfl
                  (ConnesKreimer.of' pq.1.1) (ConnesKreimer.of' pq.2.1),
                IH _ hC'lt C' rfl
                  (ConnesKreimer.of' pq.1.2) (ConnesKreimer.of' pq.2.2)]

/-! ### The pairing as a map to the convolution algebra -/

/-- The pairing turns the Grossman–Larson product into the convolution product of linear
functionals, in the opposite order. -/
theorem toConv_pairing_product (x y : ConnesKreimer R (UnorderedTree α)) :
    toConv (pairing (R := R) (product x y)) = toConv (pairing y) * toConv (pairing x) := by
  ext z
  have h : LinearMap.mul' R R ∘ₗ TensorProduct.map (pairing (R := R) y) (pairing x) =
      pairing₂ (y ⊗ₜ[R] x) := TensorProduct.ext' fun _ _ ↦ rfl
  exact (pairing_gl_eq_pairing_coproduct_Rho x y (ConnesKreimer.of' z)).trans
    (LinearMap.congr_fun h _).symm

/-- The two triple Grossman–Larson products pair equally against everything, since the
convolution product is associative. -/
theorem pairing_product_assoc (x y z : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) (product (product x y) z) = pairing (product x (product y z)) :=
  toConv_injective <| by simp only [toConv_pairing_product, mul_assoc]

/-- `Δ^ρ` is the generic admissible-cut coproduct at the pruning cuts. -/
theorem comulAlgHomN_eq_G {R : Type*} [CommSemiring R] {α : Type*} :
    comulAlgHomN (R := R) (α := α) = comulAlgHomNG (R := R) cutSummandsN := rfl

/-- The pruning cuts are admissible, by the coassociativity and counit laws of `Δ^ρ`. -/
instance {α : Type*} : IsAdmissibleCuts (cutSummandsN (α := α)) where
  coassoc := by
    intro R _
    rw [← comulAlgHomN_eq_G]
    exact comulAlgHomN_coassoc_algHom
  counit_rTensor := by
    intro R _
    rw [← comulAlgHomN_eq_G]
    exact counit_rTensor_comulAlgHomN
  counit_lTensor := by
    intro R _
    rw [← comulAlgHomN_eq_G]
    exact counit_lTensor_comulAlgHomN

end ConnesKreimer

