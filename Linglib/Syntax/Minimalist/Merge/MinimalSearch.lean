module

public import Linglib.Syntax.Minimalist.Merge.Internal
public import Linglib.Core.Algebra.RootedTree.Coproduct.Primitive

/-!
# Minimal Search as a weighting of Merge

Marcolli, Chomsky and Berwick implement Minimal Search by weighting the terms of the coproduct
(their §1.5). Extracting an accessible term at distance `d` from its root costs `ε^d`, the costs
of simultaneous extractions multiply, and Merge pays the weight of the terms it grafts, their
`M^ε_{S,S'} = ⊔ ∘ (B^ε ⊗ id) ∘ δ_{S,S'} ∘ Δ` of (1.5.1) and (1.5.2).

The weighted coproduct `comulEps ε` scales a tree by `ε` for each level it is moved down on its
way to the left channel. At `ε = 1` it is the pruning coproduct, so the weighted Merge
`mergeOpEps 1` is Merge. At `ε = 0` only whole components reach the left channel and the coproduct
is primitive, so `mergeOpEps 0` merges two components of the workspace and nothing else. In the
limit Sideward Merge vanishes, while External Merge and Internal Merge survive (Proposition 1.5.1).

## Main definitions

* `Minimalist.Merge.comulEps`: the depth-weighted coproduct.
* `Minimalist.Merge.mergeOpEps`: Merge weighted by Minimal Search.

## Main results

* `Minimalist.Merge.comulEps_one`, `comulEps_zero`: at `ε = 1` the weighted coproduct is the
  pruning coproduct, and at `ε = 0` it is the primitive coproduct.
* `Minimalist.Merge.mergeOpEps_zero_of'_of_not_le`: at `ε = 0`, Merge vanishes unless both objects
  are components of the workspace, so every form of Sideward Merge vanishes.
* `Minimalist.Merge.mergeOpEps_zero_pair_add`, `mergeOpEps_zero_im_composition`: External and
  Internal Merge survive at `ε = 0`.

## Implementation notes

* The book weights the left channel by `ε^d` and the right channel by `ε^{-d}`, and lets `B^ε` read
  the left weight. In a tensor product over `R` the two weights would cancel, so the weight is the
  coefficient of the left channel only. The book uses the right weight only to compute the cost
  `d - d = 0` of Internal Merge, which here is the cost `0` of merging two components.
* The unit stage `M_{β,1}` grafts nothing and costs nothing (the book's rule 4), so Internal Merge
  is `mergeOpEps ε lbl Q β ∘ mergeOpUnit β`, as the book writes it in proving Proposition 1.5.1.
* The weights are polynomial in `ε`, and the limit `ε → 0` is evaluation at `ε = 0`, the book's
  `M^ε_{S,S'}|_{ε=0}`.

## TODO

The first claim of Proposition 1.5.1 also holds at every `ε`: External and Internal Merge have
weight `1`, and each Sideward configuration has weight divisible by `ε`.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.Merge

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### The empty-cut enumeration -/

instance : IsMergeCuts (emptyCuts (α := α)) where
  crown_numEdges_lt hp h := (h (congrArg Prod.fst (Multiset.mem_singleton.mp hp))).elim
  mem_subtrees_of_mem_crown hp hx := by
    rw [Multiset.mem_singleton.mp hp] at hx; exact absurd hx (Multiset.notMem_zero _)
  filter_empty T := by simp [emptyCuts, Multiset.filter_singleton]

/-! ### The weighted coproduct -/

/-- The step of the fold computing the weighted coproduct pairs the node rebuilt from its children
    with its weighted coproduct. -/
noncomputable def comulTreeEpsStep (ε : R) (a : α)
    (bs : Multiset (UnorderedTree α ×
      (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)))) :
    UnorderedTree α × (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :=
  (UnorderedTree.node a (bs.map Prod.fst),
    ofTree (UnorderedTree.node a (bs.map Prod.fst)) ⊗ₜ[R] 1 +
      TensorProduct.map (aeval fun t ↦ ε • ofTree (R := R) t).toLinearMap (bPlusLin a)
        (bs.map Prod.snd).prod)

private theorem fold_comulTreeEpsStep_fst (ε : R) (T : UnorderedTree α) :
    (T.fold (comulTreeEpsStep ε)).1 = T := by
  induction T with
  | node a F ih =>
    rw [UnorderedTree.fold_node, comulTreeEpsStep, Multiset.map_map]
    exact congrArg _ ((Multiset.map_congr rfl ih).trans (Multiset.map_id F))

/-- The depth-weighted coproduct of a tree ([marcolli-chomsky-berwick-2025] §1.5.2), in which an
    extraction at distance `d` from the root has weight `ε^d`. -/
noncomputable def comulTreeEps (ε : R) (T : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  (T.fold (comulTreeEpsStep ε)).2

/-- The weighted coproduct of a node keeps the node whole, or takes the weighted coproduct of its
    children with every extracted tree one level further down. -/
theorem comulTreeEps_node (ε : R) (a : α) (F : Forest (UnorderedTree α)) :
    comulTreeEps ε (UnorderedTree.node a F) =
      ofTree (UnorderedTree.node a F) ⊗ₜ[R] 1 +
        TensorProduct.map (aeval fun t ↦ ε • ofTree (R := R) t).toLinearMap (bPlusLin a)
          (F.map (comulTreeEps ε)).prod := by
  rw [comulTreeEps, UnorderedTree.fold_node, comulTreeEpsStep, Multiset.map_map, Multiset.map_map]
  have h : Prod.fst ∘ UnorderedTree.fold (comulTreeEpsStep (R := R) (α := α) ε) = id :=
    funext (fold_comulTreeEpsStep_fst ε)
  simp only [h, Multiset.map_id]
  rfl

/-- The depth-weighted coproduct on workspaces. -/
noncomputable def comulEps (ε : R) :
    ConnesKreimer R (UnorderedTree α) →ₐ[R]
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  aeval (comulTreeEps ε)

@[simp] theorem comulEps_ofTree (ε : R) (T : UnorderedTree α) :
    comulEps ε (ofTree T) = comulTreeEps ε T :=
  aeval_ofTree _ T

/-- At `ε = 1` every extraction has weight `1`, and the weighted coproduct is the pruning
    coproduct. -/
theorem comulEps_one : comulEps (1 : R) = comulAlgHomN (α := α) := by
  ext T
  rw [comulEps_ofTree, comulAlgHomN_apply_ofTree]
  induction T with
  | node a F ih =>
    have hθ : (aeval fun t ↦ (1 : R) • ofTree (R := R) (T := UnorderedTree α) t) = AlgHom.id R _ :=
      algHom_ext_ofTree fun t ↦ by simp
    rw [comulTreeEps_node, hθ, Multiset.map_congr rfl ih, ← comulAlgHomN_apply_ofTree,
      ← bPlusLin_of', comulAlgHomN_bPlusLin_cocycle, comulAlgHomN_apply_of']
    rfl

/-- At `ε = 0` every tree is primitive for the weighted coproduct, since only whole components reach
    the left channel. -/
theorem comulTreeEps_zero (T : UnorderedTree α) :
    comulTreeEps (0 : R) T = ofTree T ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ofTree T := by
  induction T with
  | node a F ih =>
    have hθ : (Algebra.TensorProduct.map (aeval fun t ↦ (0 : R) • ofTree (R := R) t)
        (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))) (F.map (comulTreeEps 0)).prod =
        Algebra.TensorProduct.includeRight (of' F) := by
      rw [map_multiset_prod, Multiset.map_map, ← prod_map_ofTree, map_multiset_prod,
        Multiset.map_map]
      refine congrArg _ (Multiset.map_congr rfl fun c hc ↦ ?_)
      simp [ih c hc]
    have hmap (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
        TensorProduct.map (aeval fun t ↦ (0 : R) • ofTree (R := R) t).toLinearMap (bPlusLin a) z =
          LinearMap.lTensor _ (bPlusLin a) (Algebra.TensorProduct.map
            (aeval fun t ↦ (0 : R) • ofTree (R := R) t) (AlgHom.id R _) z) := by
      induction z using TensorProduct.inductionOn with
      | tmul x y => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [comulTreeEps_node, hmap, hθ, Algebra.TensorProduct.includeRight_apply,
      LinearMap.lTensor_tmul, bPlusLin_of']

/-- At `ε = 0` the weighted coproduct is the primitive coproduct. -/
theorem comulEps_zero : comulEps (0 : R) = comulPrim (T := UnorderedTree α) :=
  comulPrim_unique _ fun T ↦ by rw [comulEps_ofTree, comulTreeEps_zero]

/-! ### Weighted Merge -/

variable [DecidableEq (UnorderedTree α)]

/-- Merge weighted by Minimal Search ([marcolli-chomsky-berwick-2025] (1.5.1)) grafts each
    matching term with the weight of its extractions. -/
noncomputable def mergeOpEps (ε : R) (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePost lbl S S' ∘ₗ (comulEps ε).toLinearMap

/-- At `ε = 1` weighted Merge is Merge. -/
theorem mergeOpEps_one (lbl : α) (S S' : UnorderedTree α) :
    mergeOpEps (1 : R) lbl S S' = mergeOp lbl S S' := by
  rw [mergeOpEps, comulEps_one]; rfl

/-- At `ε = 0` weighted Merge is Merge at the empty-cut enumeration. -/
theorem mergeOpEps_zero (lbl : α) (S S' : UnorderedTree α) :
    mergeOpEps (0 : R) lbl S S' = mergeOpG emptyCuts lbl S S' := by
  rw [mergeOpEps, comulEps_zero, ← comulAlgHomNG_emptyCuts]; rfl

/-- At `ε = 0` Merge vanishes on a workspace unless `S` and `S'` are both components of it
    ([marcolli-chomsky-berwick-2025] Proposition 1.5.1). This covers each form of Sideward Merge,
    in which `S` or `S'` is an accessible term of a component. -/
theorem mergeOpEps_zero_of'_of_not_le (lbl : α) {S S' : UnorderedTree α}
    {F : Forest (UnorderedTree α)} (h : ¬ ({S, S'} : Forest (UnorderedTree α)) ≤ F) :
    mergeOpEps (0 : R) lbl S S' (of' F) = 0 := by
  rw [mergeOpEps_zero, mergeOpG_apply_of', forestCutsG_emptyCuts,
    (Multiset.filter_eq_nil (p := fun p : Forest _ × Forest _ ↦ p.1 = {S, S'})).mpr
      fun p hp hpS ↦ h (by rw [← hpS, ← Multiset.mem_antidiagonal.mp hp]; exact le_self_add),
    Multiset.map_zero, Multiset.sum_zero, mul_zero]

/-- At `ε = 0` Merge commutes with a spectator tree `U` other than `S` and `S'`, whatever
    accessible terms `U` has. -/
theorem mergeOpEps_zero_ofTree_mul (lbl : α) {S S' U : UnorderedTree α} (hS : U ≠ S)
    (hS' : U ≠ S') (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOpEps (0 : R) lbl S S' (ofTree U * w) = ofTree U * mergeOpEps (0 : R) lbl S S' w := by
  rw [mergeOpEps, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, map_mul, comulEps_ofTree, comulTreeEps_zero, add_mul, map_add,
    ← of'_singleton, mergePost_left_mul_eq_zero_of_not_le _ _ _ _ _ ?_, zero_add,
    mul_comm ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] _), mergePost_right_one_tmul,
    mul_comm, of'_singleton]
  intro h
  rcases Multiset.mem_cons.mp (Multiset.singleton_le.mp h) with h | h
  exacts [hS h, hS' (Multiset.mem_singleton.mp h)]

/-- At `ε = 0` a spectator workspace passes through Merge whenever neither `S` nor `S'` is one of
    its components. -/
theorem mergeOpEps_zero_of'_mul (lbl : α) {S S' : UnorderedTree α} {F : Forest (UnorderedTree α)}
    (hS : S ∉ F) (hS' : S' ∉ F) (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOpEps (0 : R) lbl S S' (of' F * w) = of' F * mergeOpEps (0 : R) lbl S S' w := by
  induction F using Multiset.induction generalizing w with
  | empty => rw [of'_zero, one_mul, one_mul]
  | cons U F ih =>
    rw [Multiset.mem_cons, not_or] at hS hS'
    rw [← Multiset.singleton_add, of'_add, mul_assoc, of'_singleton,
      mergeOpEps_zero_ofTree_mul lbl (Ne.symm hS.1) (Ne.symm hS'.1), ih hS.2 hS'.2, ← mul_assoc]

/-- External Merge survives at `ε = 0` ([marcolli-chomsky-berwick-2025] Proposition 1.5.1), beside
    any spectator workspace that does not repeat `S` or `S'` as a component. -/
theorem mergeOpEps_zero_pair_add (lbl : α) {S S' : UnorderedTree α}
    {F : Forest (UnorderedTree α)} (hS : S ∉ F) (hS' : S' ∉ F) :
    mergeOpEps (0 : R) lbl S S' (of' (({S, S'} : Forest (UnorderedTree α)) + F)) =
      of' (({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + F) := by
  rw [add_comm, of'_add, mergeOpEps_zero_of'_mul lbl hS hS', mergeOpEps_zero, mergeOpG_pair,
    ← of'_add, add_comm]

/-- Internal Merge survives at `ε = 0` ([marcolli-chomsky-berwick-2025] Proposition 1.5.1), since
    its unit stage is weightless and its second stage merges two components. -/
theorem mergeOpEps_zero_im_composition (lbl : α) (β T Q : UnorderedTree α)
    (p0 : Forest (UnorderedTree α) × UnorderedTree α)
    (h_filter : (cutSummandsN T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) = {p0})
    (h_remainder : p0.2 = Q) (hTβ : T ≠ β) :
    mergeOpEps (0 : R) lbl Q β (mergeOpUnit (R := R) β (of' ({T} : Forest (UnorderedTree α)))) =
      of' ({UnorderedTree.node lbl {Q, β}} : Forest (UnorderedTree α)) := by
  rw [mergeOpUnit_eq_G, mergeOpUnitG_apply_singleton_unique β T p0 h_filter hTβ, h_remainder,
    ← of'_singleton, ← of'_add, add_comm, mergeOpEps_zero]
  exact mergeOpG_pair lbl Q β

end Minimalist.Merge
