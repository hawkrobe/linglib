module

public import Linglib.Syntax.Minimalist.Merge.Basic
public import Linglib.Syntax.Minimalist.Workspace.TraceConservation
public import Linglib.Core.Combinatorics.RootedTree.Conservation
public import Linglib.Core.Combinatorics.RootedTree.Crown
public import Linglib.Core.Algebra.RootedTree.HopfAlgebra

/-!
# External Merge

External Merge ([marcolli-chomsky-berwick-2025] Lemma 1.4.1): Merge of two components `S, S'` of
a workspace replaces them by `node lbl {S, S'}` and leaves the rest unchanged. For a two-object
workspace this holds over every cut enumeration admitting Merge (`mergeOpG_pair`), in particular
at the pruning and trace cuts. With a residual workspace `F̂` it holds at the pruning cuts when no
component of `F̂` has `S` or `S'` as a subtree (`mergeOp_pair_residual`).

The proof of `mergeOpG_pair` expands the coproduct of `{S, S'}` into four cross-terms of the
primitive terms and the cut sums of `S` and `S'`. Only the primitive term survives: a cut of `S'`
alone would need crown `{S'}`, and cuts of both would need crowns reassembling `{S, S'}`, and
both are ruled out by the edge bound of `IsMergeCuts`.

## Main results

* `Minimalist.Merge.mergeOpG_pair`, `mergeOp_pair`, `mergeOpC_pair`: External Merge on a
  two-object workspace.
* `Minimalist.Merge.mergeOp_pair_residual`: External Merge with a residual workspace.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.Merge

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq (UnorderedTree α)]

omit [DecidableEq (UnorderedTree α)] in
private theorem sum_map_ite_eq_zero {ι M : Type*} [AddCommMonoid M] {s : Multiset ι}
    {P : ι → Prop} [DecidablePred P] {f : ι → M} (h : ∀ i ∈ s, ¬ P i) :
    (s.map fun i ↦ if P i then f i else 0).sum = 0 :=
  Multiset.sum_eq_zero fun _ hx ↦ by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact ite_eq_right (h i hi)

instance : IsMergeCuts (cutSummandsN (α := α)) where
  crown_numEdges_lt := cutSummandsN_crown_numEdges_lt

instance {β : Type*} (τ : UnorderedTree (α ⊕ β) → β) : IsMergeCuts (cutSummandsCN τ) where
  crown_numEdges_lt := cutSummandsCN_crown_numEdges_lt τ

/-- External Merge of a two-object workspace, over a cut enumeration admitting Merge. -/
theorem mergeOpG_pair
    {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
    [IsMergeCuts cuts] (lbl : α) (S S' : UnorderedTree α) :
    mergeOpG (R := R) cuts lbl S S' (of' ({S, S'} : Forest (UnorderedTree α)))
      = of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) := by
  have key (F F' : Forest (UnorderedTree α)) (t t' : ConnesKreimer R (UnorderedTree α)) :
      mergePost (R := R) lbl S S' ((of' F ⊗ₜ[R] t) * (of' F' ⊗ₜ[R] t'))
        = if F + F' = {S, S'} then of' {UnorderedTree.node lbl {S, S'}} * (t * t') else 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← of'_add, mergePost_basis_tensor]
  have hpair : ({S} : Forest (UnorderedTree α)) + {S'} = {S, S'} := rfl
  have hS (p) (hp : p ∈ cuts S) : ¬ p.1 + {S'} = {S, S'} := fun h ↦
    IsMergeCuts.crown_ne_singleton hp (Multiset.add_left_inj.mp (h.trans hpair.symm))
  have hS' (p) (hp : p ∈ cuts S') : ¬ {S} + p.1 = {S, S'} := fun h ↦
    IsMergeCuts.crown_ne_singleton hp (Multiset.add_right_inj.mp (h.trans hpair.symm))
  have hSS' (p) (hp : p ∈ cuts S) (p') (hp' : p' ∈ cuts S') : ¬ p.1 + p'.1 = {S, S'} := by
    intro h
    have hsum := congrArg (fun F ↦ (F.map numEdges).sum) h
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton] at hsum
    rcases eq_or_ne p.1 0 with h1 | h1
    · have h2 : p'.1 ≠ 0 := fun h2 ↦ by simp [h1, h2] at h
      have := IsMergeCuts.crown_numEdges_lt hp' h2
      simp only [h1, Multiset.map_zero, Multiset.sum_zero] at hsum
      omega
    · have := IsMergeCuts.crown_numEdges_lt hp h1
      rcases eq_or_ne p'.1 0 with h2 | h2
      · simp only [h2, Multiset.map_zero, Multiset.sum_zero] at hsum
        omega
      · have := IsMergeCuts.crown_numEdges_lt hp' h2
        omega
  rw [mergeOpG, LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulAlgHomNG_apply_of',
    show ({S, S'} : Forest (UnorderedTree α)) = S ::ₘ S' ::ₘ 0 from rfl, comulForestNG_cons,
    comulForestNG_cons, comulForestNG_zero, mul_one, comulTreeNG, comulTreeNG]
  simp only [ofTree, add_mul, mul_add, ← Multiset.sum_map_mul_left,
    ← Multiset.sum_map_mul_right, map_add, map_multiset_sum, Multiset.map_map,
    Function.comp_def, key, ite_eq_left hpair, mul_one]
  rw [sum_map_ite_eq_zero hS, add_zero, Multiset.sum_eq_zero, add_zero]
  · rfl
  intro x hx
  obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.mp hx
  rw [ite_eq_right (hS' p' hp'), zero_add, sum_map_ite_eq_zero fun p hp ↦ hSS' p hp p' hp']

/-- External Merge of a two-object workspace at the pruning cuts. -/
theorem mergeOp_pair (lbl : α) (S S' : UnorderedTree α) :
    mergeOp (R := R) lbl S S' (of' ({S, S'} : Forest (UnorderedTree α)))
      = of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) :=
  mergeOpG_pair lbl S S'

omit [DecidableEq (UnorderedTree α)] in
/-- External Merge of a two-object workspace at the trace cuts. -/
theorem mergeOpC_pair {β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))]
    (τ : UnorderedTree (α ⊕ β) → β) (lbl : α ⊕ β) (S S' : UnorderedTree (α ⊕ β)) :
    mergeOpC (R := R) τ lbl S S' (of' ({S, S'} : Forest (UnorderedTree (α ⊕ β))))
      = of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree (α ⊕ β))) :=
  mergeOpG_pair lbl S S'

/-- Merge at the pruning cuts commutes with a spectator component `T` that has neither `S` nor
    `S'` as a subtree ([marcolli-chomsky-berwick-2025] Lemma 1.4.1). The primitive term of `T`
    does not fit inside `{S, S'}`, no nonempty cut of `T` extracts `S` or `S'`, and the empty cut
    passes `T` through to the right channel. -/
theorem mergeOp_factor_out_singleton (lbl : α) {S S' T : UnorderedTree α}
    (hT_S : S ∉ T.subtrees) (hT_S' : S' ∉ T.subtrees)
    (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOp (R := R) lbl S S' (of' ({T} : Forest (UnorderedTree α)) * w)
      = of' ({T} : Forest (UnorderedTree α)) * mergeOp (R := R) lbl S S' w := by
  obtain ⟨hT_ne_S, h_no_S_in_T_cuts⟩ := not_mem_subtrees_iff.mp hT_S
  obtain ⟨hT_ne_S', h_no_S'_in_T_cuts⟩ := not_mem_subtrees_iff.mp hT_S'
  show (mergePost (R := R) (α := α) lbl S S' ∘ₗ comulAlgHomN.toLinearMap)
       (of' ({T} : Forest (UnorderedTree α)) * w) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      show comulAlgHomN (R := R) (α := α) (of' ({T} : Forest (UnorderedTree α)))
          = comulTreeN (R := R) T from comulAlgHomN_apply_ofTree T]
  unfold comulTreeN comulTreeNG
  rw [add_mul]
  simp only [map_add]
  -- The primitive term vanishes, since `{T}` does not fit inside `{S, S'}`.
  rw [show mergePost (R := R) (α := α) lbl S S'
        ((ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α))) * comulAlgHomN w)
        = 0 from by
      rw [show (ofTree T : ConnesKreimer R (UnorderedTree α))
            = of' ({T} : Forest (UnorderedTree α)) from rfl]
      apply mergePost_left_mul_eq_zero_of_not_le
      intro h_le
      have hT_mem : T ∈ ({S, S'} : Forest (UnorderedTree α)) :=
        Multiset.subset_of_le h_le (Multiset.mem_singleton.mpr rfl)
      rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hT_mem
      exact hT_mem.elim hT_ne_S hT_ne_S']
  rw [zero_add]
  -- Split off the empty cut `(0, T)`.
  rw [← Multiset.sum_map_mul_right,
      ← Multiset.filter_add_not (fun pf => pf.1.card = 0) (cutSummandsN T),
      Multiset.map_add, Multiset.sum_add, map_add,
      cutSummandsN_filter_empty, Multiset.map_singleton, Multiset.sum_singleton]
  -- The nonempty cuts vanish: a crown inside `{S, S'}` containing neither is empty.
  rw [show mergePost (R := R) (α := α) lbl S S'
        (((cutSummandsN T).filter (fun pf => ¬ pf.1.card = 0)).map
          (fun p => (of' (R := R) p.1 ⊗ₜ[R] ofTree p.2) * comulAlgHomN w)).sum
        = 0 from by
      rw [_root_.map_multiset_sum, Multiset.map_map]
      refine Multiset.sum_eq_zero fun x hx => ?_
      obtain ⟨p, hp_filter, rfl⟩ := Multiset.mem_map.mp hx
      have hmem := Multiset.mem_filter.mp hp_filter
      show mergePost (R := R) (α := α) lbl S S'
            ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2) * comulAlgHomN w) = 0
      apply mergePost_left_mul_eq_zero_of_not_le
      intro h_le
      apply hmem.2
      rw [Multiset.card_eq_zero]
      refine Multiset.eq_zero_of_forall_notMem fun x hx_mem => ?_
      have hx_in : x ∈ ({S, S'} : Forest (UnorderedTree α)) :=
        Multiset.subset_of_le h_le hx_mem
      rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx_in
      rcases hx_in with rfl | rfl
      · exact h_no_S_in_T_cuts p hmem.1 hx_mem
      · exact h_no_S'_in_T_cuts p hmem.1 hx_mem]
  rw [add_zero]
  -- The empty cut passes `T` to the right channel.
  rw [of'_zero,
      mul_comm ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] ofTree T) (comulAlgHomN w),
      mergePost_right_one_tmul,
      mul_comm (mergePost (R := R) (α := α) lbl S S' (comulAlgHomN w)) (ofTree T)]
  rfl

/-- External Merge at the pruning cuts with a residual workspace `F̂` none of whose components has
    `S` or `S'` as a subtree ([marcolli-chomsky-berwick-2025] Lemma 1.4.1). Without the
    hypothesis Merge also matches accessible terms inside `F̂`, the Sideward cases of
    `Merge/Sideward.lean`. -/
theorem mergeOp_pair_residual (lbl : α) {S S' : UnorderedTree α}
    {Fhat : Forest (UnorderedTree α)}
    (hF : ∀ T ∈ Fhat, Disjoint ({S, S'} : Forest (UnorderedTree α)) T.subtrees) :
    mergeOp (R := R) lbl S S' (of' (({S, S'} : Forest (UnorderedTree α)) + Fhat))
      = of' (({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    exact mergeOp_pair lbl S S'
  | cons T Fhat' ih =>
    have hT_S : S ∉ T.subtrees :=
      Multiset.disjoint_left.mp (hF T (Multiset.mem_cons_self _ _)) (by simp)
    have hT_S' : S' ∉ T.subtrees :=
      Multiset.disjoint_left.mp (hF T (Multiset.mem_cons_self _ _)) (by simp)
    have ih' := ih fun U hU ↦ hF U (Multiset.mem_cons_of_mem hU)
    rw [Multiset.add_cons, Multiset.add_cons, ← Multiset.singleton_add, ← Multiset.singleton_add,
      of'_add (R := R) ({T} : Forest (UnorderedTree α)),
      of'_add (R := R) ({T} : Forest (UnorderedTree α)),
      mergeOp_factor_out_singleton lbl hT_S hT_S', ih']

end Minimalist.Merge
