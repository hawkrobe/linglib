import Linglib.Syntax.Minimalist.Merge.Basic
import Linglib.Core.Combinatorics.RootedTree.Conservation
import Linglib.Core.Combinatorics.RootedTree.CutAvoiding
import Linglib.Core.Algebra.RootedTree.HopfAlgebra

/-!
# External Merge on the algebraic carrier

External Merge (Lemma 1.4.1) on the canonical carrier `ConnesKreimer R (UnorderedTree α)`: for a
pair `(S, S') : UnorderedTree α` and a root label `lbl`, `mergeOp lbl S S'` sends the workspace `of'
{S, S'}` to `of' {UnorderedTree.node lbl {S, S'}}` (`mergeOp_pair`), and on a workspace with a
residual part `F̂` avoiding the cuts that extract `S` or `S'`, it factors through the spectator
components (`mergeOp_factor_out_singleton`, `mergeOp_pair_residual`). The carrier-level form on
`SyntacticObject` is `SyntacticObject.mergeOp_node` in `Merge/SyntacticObject.lean`.

The proof of `mergeOp_pair` expands the merge coproduct
`Δ^ρ({S, S'}) = comulTreeN S * comulTreeN S'`, distributes the primitive-plus-cut split of each
factor, and evaluates the four cross-terms via `mergePost_basis_tensor`; only the primitive ×
primitive term survives, the others vanishing because no proper cut extracts a whole tree as its
crown (`cutSummandsN_crown_ne_singleton`) and vertex conservation (`cutSummandsN_numNodes`)
forbids two crowns from reassembling `{S, S'}`. The residual case is an induction on `F̂` under
`CutAvoidingForest`, isolating the surviving empty-cut summand of `comulTreeN T` via
`cutSummandsN_filter_card_zero`.

## Main results

* `Minimalist.Merge.mergeOp_pair`: External Merge on a two-object workspace.
* `Minimalist.Merge.mergeOp_pair_residual`: External Merge with a cut-avoiding residual workspace.

## References

* [marcolli-chomsky-berwick-2025], §1.4 (Lemma 1.4.1)
-/

namespace Minimalist.Merge

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

/-- **Algebraic Merge on a 2-tree workspace** (M-C-B Lemma 1.4.1, F̂ = ∅
    subcase). For any pair `(S, S') : UnorderedTree α` and root label `lbl`,
    `mergeOp lbl S S'` applied to the basis vector `of' {S, S'}` yields
    `of' {UnorderedTree.node lbl {S, S'}}`.

    The merge coproduct `Δ^ρ({S, S'}) = comulTreeN S * comulTreeN S'` splits each
    factor into its full-extraction `ofTree T ⊗ 1` term plus the proper-cut sum;
    distributing gives 4 cross-terms. Only `prim × prim` survives
    `mergePost`; the three sum-bearing terms vanish via
    `cutSummandsN_crown_ne_singleton` (no proper cut's crown is `{S}` or `{S'}`)
    and `cutSummandsN_numNodes` (two proper crowns under-count `{S, S'}`'s
    vertices). -/
theorem mergeOp_pair {R : Type*} [CommSemiring R] {α : Type*}
    [DecidableEq (UnorderedTree α)] (lbl : α) (S S' : UnorderedTree α) :
    mergeOp (R := R) lbl S S' (of' ({S, S'} : Forest (UnorderedTree α)))
      = of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) := by
  -- Step 1: mergeOp = mergePost ∘ comulAlgHomN, applied to of' {S, S'}.
  show (mergePost (R := R) (α := α) lbl S S' ∘ₗ comulAlgHomN.toLinearMap)
       (of' ({S, S'} : Forest (UnorderedTree α))) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulAlgHomN_apply_of']
  -- Step 2: comulForestN {S, S'} = comulTreeN S * comulTreeN S'.
  rw [show comulForestN (R := R) ({S, S'} : Forest (UnorderedTree α))
        = comulTreeN (R := R) S * comulTreeN (R := R) S' from by
      rw [show ({S, S'} : Forest (UnorderedTree α)) = S ::ₘ ({S'} : Forest (UnorderedTree α))
            from rfl, comulForestN_cons,
          show ({S'} : Forest (UnorderedTree α)) = S' ::ₘ (0 : Forest (UnorderedTree α))
            from rfl, comulForestN_cons, comulForestN_zero, mul_one]]
  -- Step 3: split each comulTreeN into prim + cut-sum; distribute.
  unfold comulTreeN comulTreeNG
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- Term 1 (prim × prim): the surviving contribution.
  have h_pp :
      mergePost (R := R) (α := α) lbl S S'
          ((ofTree S ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)))
            * (ofTree S' ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α))))
        = of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← of'_singleton, ← of'_singleton,
        ← of'_add,
        show ({S} : Forest (UnorderedTree α)) + ({S'} : Forest (UnorderedTree α))
            = ({S, S'} : Forest (UnorderedTree α)) from rfl,
        mergePost_basis_tensor, if_pos rfl, mul_one]
  -- Term 2 (prim S × cut-sum S'): vanishes (crown of S' is never {S'}).
  have h_ps :
      mergePost (R := R) (α := α) lbl S S'
          ((ofTree S ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)))
            * ((cutSummandsN S').map
                (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum)
        = 0 := by
    rw [← Multiset.sum_map_mul_left, _root_.map_multiset_sum, Multiset.map_map]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
    show mergePost (R := R) (α := α) lbl S S'
          ((ofTree S ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)))
            * (of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← of'_singleton, ← of'_add,
        mergePost_basis_tensor, if_neg]
    intro hcontra
    apply cutSummandsN_crown_ne_singleton S' p hp
    have heq : ({S} : Forest (UnorderedTree α)) + p.1
             = ({S} : Forest (UnorderedTree α)) + ({S'} : Forest (UnorderedTree α)) := by
      rw [hcontra]; rfl
    exact Multiset.add_right_inj.mp heq
  -- Term 3 (cut-sum S × prim S'): symmetric (crown of S is never {S}).
  have h_sp :
      mergePost (R := R) (α := α) lbl S S'
          (((cutSummandsN S).map
              (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum
            * (ofTree S' ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α))))
        = 0 := by
    rw [← Multiset.sum_map_mul_right, _root_.map_multiset_sum, Multiset.map_map]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
    show mergePost (R := R) (α := α) lbl S S'
          ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)
            * (ofTree S' ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)))) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← of'_singleton, ← of'_add,
        mergePost_basis_tensor, if_neg]
    intro hcontra
    apply cutSummandsN_crown_ne_singleton S p hp
    have heq : p.1 + ({S'} : Forest (UnorderedTree α))
             = ({S} : Forest (UnorderedTree α)) + ({S'} : Forest (UnorderedTree α)) := by
      rw [hcontra]; rfl
    exact Multiset.add_left_inj.mp heq
  -- Term 4 (cut-sum S × cut-sum S'): two proper crowns can't reassemble {S, S'}.
  have h_ss :
      mergePost (R := R) (α := α) lbl S S'
          (((cutSummandsN S).map
              (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum
            * ((cutSummandsN S').map
                (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum)
        = 0 := by
    rw [← Multiset.sum_map_mul_right, _root_.map_multiset_sum, Multiset.map_map]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
    show mergePost (R := R) (α := α) lbl S S'
          ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)
            * ((cutSummandsN S').map
                (fun q => of' (R := R) q.1 ⊗ₜ[R] ofTree q.2)).sum) = 0
    rw [← Multiset.sum_map_mul_left, _root_.map_multiset_sum, Multiset.map_map]
    refine Multiset.sum_eq_zero fun y hy => ?_
    obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.mp hy
    show mergePost (R := R) (α := α) lbl S S'
          ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)
            * (of' (R := R) p'.1 ⊗ₜ[R] ofTree p'.2)) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← of'_add, mergePost_basis_tensor, if_neg]
    intro hcontra
    have hwS := cutSummandsN_numNodes S p hp
    have hwS' := cutSummandsN_numNodes S' p' hp'
    have hp2 := p.2.numNodes_pos
    have hp2' := p'.2.numNodes_pos
    have hfw : ((p.1 + p'.1).map UnorderedTree.numNodes).sum
             = (({S, S'} : Forest (UnorderedTree α)).map UnorderedTree.numNodes).sum := by
      rw [hcontra]
    rw [Multiset.map_add, Multiset.sum_add,
        show (({S, S'} : Forest (UnorderedTree α)).map UnorderedTree.numNodes).sum
            = S.numNodes + S'.numNodes from by
          simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
                     Multiset.map_singleton, Multiset.sum_singleton]] at hfw
    omega
  rw [h_pp, h_ps, h_sp, h_ss]
  simp only [add_zero]

/-- **Factor-out lemma** (MCB Lemma 1.4.1 Case 1, inductive step). Under
    `CutAvoiding S T` and `CutAvoiding S' T` (`T ≠ S, S'` and no Δ^ρ cut of `T`
    extracts `S` or `S'` as a crown), `mergeOp lbl S S'` commutes with left
    multiplication by the spectator `of' {T}`:

      mergeOp lbl S S' (of' {T} * w) = of' {T} * mergeOp lbl S S' w.

    Proof: `comulAlgHomN (of' {T} * w) = comulTreeN T * comulAlgHomN w`. The
    `ofTree T ⊗ 1` term vanishes (`{T} ⊄ {S, S'}`); the cut-sum splits via
    `cutSummandsN_filter_card_zero` into the surviving empty cut `(0, T)` — which
    by `UnorderedTree`-tensor commutativity and `mergePost_right_one_tmul` yields
    `of' {T} * mergeOp lbl S S' w` — and the nonempty cuts, each annihilated since
    a crown `≤ {S, S'}` containing neither `S` nor `S'` must be empty. -/
theorem mergeOp_factor_out_singleton {R : Type*} [CommSemiring R] {α : Type*}
    [DecidableEq (UnorderedTree α)] (lbl : α) {S S' T : UnorderedTree α}
    (hT_S : CutAvoiding S T) (hT_S' : CutAvoiding S' T)
    (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOp (R := R) lbl S S' (of' ({T} : Forest (UnorderedTree α)) * w)
      = of' ({T} : Forest (UnorderedTree α)) * mergeOp (R := R) lbl S S' w := by
  obtain ⟨hT_ne_S, h_no_S_in_T_cuts⟩ := hT_S
  obtain ⟨hT_ne_S', h_no_S'_in_T_cuts⟩ := hT_S'
  -- mergeOp = mergePost ∘ comulAlgHomN; split the product through the alg hom.
  show (mergePost (R := R) (α := α) lbl S S' ∘ₗ comulAlgHomN.toLinearMap)
       (of' ({T} : Forest (UnorderedTree α)) * w) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      show comulAlgHomN (R := R) (α := α) (of' ({T} : Forest (UnorderedTree α)))
          = comulTreeN (R := R) T from comulAlgHomN_apply_ofTree T]
  unfold comulTreeN comulTreeNG
  rw [add_mul]
  simp only [map_add]
  -- prim term `ofTree T ⊗ 1`: vanishes since `{T} ⊄ {S, S'}`.
  rw [show mergePost (R := R) (α := α) lbl S S'
        ((ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α))) * comulAlgHomN w)
        = 0 from by
      rw [show (ofTree T : ConnesKreimer R (UnorderedTree α))
            = of' ({T} : Forest (UnorderedTree α)) from rfl]
      apply mergePost_left_mul_eq_zero_of_not_le
      intro h_le
      have hT_mem : T ∈ ({S, S'} : Forest (UnorderedTree α)) :=
        Multiset.subset_of_le h_le (Multiset.mem_singleton.mpr rfl)
      rw [show ({S, S'} : Forest (UnorderedTree α)) = S ::ₘ ({S'} : Forest (UnorderedTree α))
            from rfl, Multiset.mem_cons, Multiset.mem_singleton] at hT_mem
      rcases hT_mem with h | h
      · exact hT_ne_S h
      · exact hT_ne_S' h]
  rw [zero_add]
  -- cut-sum: distribute, split off the empty cut `(0, T)` from the rest.
  rw [← Multiset.sum_map_mul_right,
      ← Multiset.filter_add_not (fun pf => pf.1.card = 0) (cutSummandsN T),
      Multiset.map_add, Multiset.sum_add, map_add,
      cutSummandsN_filter_card_zero, Multiset.map_singleton, Multiset.sum_singleton]
  -- nonempty cuts vanish: crown `≤ {S, S'}` with `S, S' ∉ crown` is empty.
  rw [show mergePost (R := R) (α := α) lbl S S'
        (((cutSummandsN T).filter (fun pf => ¬ pf.1.card = 0)).map
          (fun p => (of' (R := R) p.1 ⊗ₜ[R] ofTree p.2) * comulAlgHomN w)).sum
        = 0 from by
      rw [_root_.map_multiset_sum, Multiset.map_map]
      refine Multiset.sum_eq_zero fun x hx => ?_
      obtain ⟨p, hp_filter, rfl⟩ := Multiset.mem_map.mp hx
      have hmem := Multiset.mem_filter.mp hp_filter
      have hp_orig : p ∈ cutSummandsN T := hmem.1
      have hp_card : ¬ p.1.card = 0 := hmem.2
      show mergePost (R := R) (α := α) lbl S S'
            ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2) * comulAlgHomN w) = 0
      apply mergePost_left_mul_eq_zero_of_not_le
      intro h_le
      apply hp_card
      have hp1_empty : p.1 = 0 := by
        refine Multiset.eq_zero_of_forall_notMem fun x hx_mem => ?_
        have hx_in : x ∈ ({S, S'} : Forest (UnorderedTree α)) :=
          Multiset.subset_of_le h_le hx_mem
        rw [show ({S, S'} : Forest (UnorderedTree α)) = S ::ₘ ({S'} : Forest (UnorderedTree α))
              from rfl, Multiset.mem_cons, Multiset.mem_singleton] at hx_in
        rcases hx_in with h | h
        · subst h; exact h_no_S_in_T_cuts p hp_orig hx_mem
        · subst h; exact h_no_S'_in_T_cuts p hp_orig hx_mem
      rw [hp1_empty, Multiset.card_zero]]
  rw [add_zero]
  -- surviving empty cut: `(of' 0 ⊗ ofTree T) * cdw` → `of' {T} * mergeOp lbl S S' w`.
  rw [of'_zero,
      mul_comm ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] ofTree T) (comulAlgHomN w),
      mergePost_right_one_tmul,
      mul_comm (mergePost (R := R) (α := α) lbl S S' (comulAlgHomN w)) (ofTree T)]
  rfl

/-- **Algebraic Merge with residual workspace** (M-C-B Lemma 1.4.1, Case 1). For
    any pair `(S, S')` and residual workspace `Fhat` with
    `CutAvoidingForest ({S, S'}) Fhat` (S, S' ∉ Fhat as components, no cut on any
    `T ∈ Fhat` extracts S or S' — excludes the non-primitive matchings of the full
    coproduct, restricting to External Merge's member-level contribution per MCB
    Remark 1.3.8), Merge factors the spectator workspace through:

      mergeOp lbl S S' (of' ({S, S'} + Fhat)) = of' ({UnorderedTree.node lbl {S, S'}} + Fhat).

    Induction on `Fhat` via `mergeOp_factor_out_singleton`. Without the
    disjointness, `mergeOp` produces the full sum-over-matchings (including
    Sideward contributions); the Minimal-Search weighting `mergeOpCEps` eliminates those in
    the ε → 0 limit. -/
theorem mergeOp_pair_residual {R : Type*} [CommSemiring R] {α : Type*}
    [DecidableEq (UnorderedTree α)] (lbl : α) {S S' : UnorderedTree α}
    {Fhat : Forest (UnorderedTree α)}
    (hF : CutAvoidingForest ({S, S'} : Forest (UnorderedTree α)) Fhat) :
    mergeOp (R := R) lbl S S' (of' (({S, S'} : Forest (UnorderedTree α)) + Fhat))
      = of' (({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    exact mergeOp_pair lbl S S'
  | cons T Fhat' ih =>
    have hT_S := hF.head S (by simp)
    have hT_S' := hF.head S' (by simp)
    have ih' : mergeOp (R := R) lbl S S'
                  (of' (({S, S'} : Forest (UnorderedTree α)) + Fhat'))
              = of' (({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + Fhat') :=
      ih hF.of_cons
    have h_lhs_eq : ({S, S'} : Forest (UnorderedTree α)) + T ::ₘ Fhat'
                  = ({T} : Forest (UnorderedTree α))
                    + (({S, S'} : Forest (UnorderedTree α)) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : Forest (UnorderedTree α)) + Fhat' from rfl]; abel
    have h_rhs_eq : ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + T ::ₘ Fhat'
                  = ({T} : Forest (UnorderedTree α))
                    + (({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : Forest (UnorderedTree α)) + Fhat' from rfl]; abel
    rw [h_lhs_eq, h_rhs_eq,
        of'_add (R := R) ({T} : Forest (UnorderedTree α))
          (({S, S'} : Forest (UnorderedTree α)) + Fhat'),
        of'_add (R := R) ({T} : Forest (UnorderedTree α))
          (({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + Fhat'),
        mergeOp_factor_out_singleton lbl hT_S hT_S']
    exact congrArg (of' (R := R) ({T} : Forest (UnorderedTree α)) * ·) ih'

end Minimalist.Merge
