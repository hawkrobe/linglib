import Linglib.Syntax.Minimalist.Merge.Basic
import Linglib.Syntax.Minimalist.Defs
import Linglib.Syntax.Minimalist.Workspace.DeletionConservation
import Linglib.Core.Algebra.RootedTree.Coproduct.CutAvoidingNonplanar
import Linglib.Core.Algebra.RootedTree.HopfAlgebraNonplanar
import Linglib.Core.Data.RoseTree.DecEq

/-!
# External Merge bridge: algebraic ↔ linguistic
[marcolli-chomsky-berwick-2025]

Realizes M-C-B §1.4 Lemma 1.4.1 (External Merge) at the algebraic level on the
canonical carrier `ConnesKreimer R (Nonplanar α)` and bridges to linguistic
`Step.emR`/`Step.emL`.

## Contents

**Lemma 1.4.1, F̂ = ∅ subcase** (`mergeOp_pair`). For any pair
`(S, S') : Nonplanar α` and any root label `lbl`, `mergeOp lbl S S'` applied to
`of' {S, S'}` yields `of' {Nonplanar.node lbl {S, S'}}`. Proof: expand the merge
coproduct `Δ^ρ({S, S'}) = comulTreeN S * comulTreeN S'` (`comulForestN_cons`),
distribute the prim/cut split of each factor, and evaluate the 4 cross-terms via
`mergePost_basis_tensor`. Only the `prim × prim` cross-term survives; the other
three vanish because no proper cut extracts a whole tree as its crown
(`cutSummandsN_crown_ne_singleton`) and vertex conservation
(`cutSummandsN_numNodes`) forbids two crowns from reassembling `{S, S'}`.

**Lemma 1.4.1 with residual workspace F̂** (`mergeOp_factor_out_singleton`,
`mergeOp_pair_residual`, MCB "Case 1"). Under `CutAvoidingForestN ({S, S'}) F̂`
(the `cutSummandsN`-based disjointness predicate of `CutAvoidingNonplanar`: each
`T ∈ F̂` differs from `S, S'` and no Δ^ρ cut of `T` extracts either as a crown),
Merge factors through multiplication by the spectator components `of' {T}`; an
induction on F̂ assembles the full Case-1 result. `mergeOp_factor_out_singleton`
is the inductive step: `mergeOp lbl S S' (of' {T} * w) = of' {T} * mergeOp lbl S S'
w`, isolating the surviving empty-cut summand of `comulTreeN T` via
`cutSummandsN_filter_card_zero`.

The Minimalism-specific bridges (`mergeOp_emR/emL_matches_Step`) specialize to
`R = ℤ`, `α = LIToken ⊕ Unit`. They take the **head label** `L` of the merged
node and a coherence hypothesis `h_coh` factoring `(current * item).toNonplanar` as
`Nonplanar.node (Sum.inl L) {current.toNonplanar, item.toNonplanar}` — the labeling convention
fixed in `Merge.Defs`'s `planarToNonplanar` (each internal node decorated with its head
leaf). This is the coupling point that validates the carrier bridge's design.

## Deferred (substrate gap)

- **§3-4: cost-weighted Merge `M^ε` and the ε → 0 Sideward-elimination chain**
  (`mergeOp_eps_zero_*`, `em_only_chain_eps_zero`). Needs an ε-weighted Δ^ρ
  (a `cutTotalDepth` analogue on `cutSummandsN`), not yet in the substrate.
  Once it lands, the EM-only chain can ride either `mergeOp` (unweighted) or the
  cost-weighted operator.
-/

namespace Minimalist.Merge

open scoped TensorProduct
open RootedTree RootedTree.ConnesKreimer

/-- **Algebraic Merge on a 2-tree workspace** (M-C-B Lemma 1.4.1, F̂ = ∅
    subcase). For any pair `(S, S') : Nonplanar α` and root label `lbl`,
    `mergeOp lbl S S'` applied to the basis vector `of' {S, S'}` yields
    `of' {Nonplanar.node lbl {S, S'}}`.

    The merge coproduct `Δ^ρ({S, S'}) = comulTreeN S * comulTreeN S'` splits each
    factor into its full-extraction `ofTree T ⊗ 1` term plus the proper-cut sum;
    distributing gives 4 cross-terms. Only `prim × prim` survives
    `mergePost`; the three sum-bearing terms vanish via
    `cutSummandsN_crown_ne_singleton` (no proper cut's crown is `{S}` or `{S'}`)
    and `cutSummandsN_numNodes` (two proper crowns under-count `{S, S'}`'s
    vertices). -/
theorem mergeOp_pair {R : Type*} [CommSemiring R] {α : Type*}
    [DecidableEq (Nonplanar α)] (lbl : α) (S S' : Nonplanar α) :
    mergeOp (R := R) lbl S S' (of' ({S, S'} : Forest (Nonplanar α)))
      = of' ({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α)) := by
  -- Step 1: mergeOp = mergePost ∘ comulAlgHomN, applied to of' {S, S'}.
  show (mergePost (R := R) (α := α) lbl S S' ∘ₗ comulAlgHomN.toLinearMap)
       (of' ({S, S'} : Forest (Nonplanar α))) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulAlgHomN_apply_of']
  -- Step 2: comulForestN {S, S'} = comulTreeN S * comulTreeN S'.
  rw [show comulForestN (R := R) ({S, S'} : Forest (Nonplanar α))
        = comulTreeN (R := R) S * comulTreeN (R := R) S' from by
      rw [show ({S, S'} : Forest (Nonplanar α)) = S ::ₘ ({S'} : Forest (Nonplanar α))
            from rfl, comulForestN_cons,
          show ({S'} : Forest (Nonplanar α)) = S' ::ₘ (0 : Forest (Nonplanar α))
            from rfl, comulForestN_cons, comulForestN_zero, mul_one]]
  -- Step 3: split each comulTreeN into prim + cut-sum; distribute.
  unfold comulTreeN
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- Term 1 (prim × prim): the surviving contribution.
  have h_pp :
      mergePost (R := R) (α := α) lbl S S'
          ((ofTree S ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))
            * (ofTree S' ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))))
        = of' ({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← of'_singleton, ← of'_singleton,
        ← of'_add,
        show ({S} : Forest (Nonplanar α)) + ({S'} : Forest (Nonplanar α))
            = ({S, S'} : Forest (Nonplanar α)) from rfl,
        mergePost_basis_tensor, if_pos rfl, mul_one]
  -- Term 2 (prim S × cut-sum S'): vanishes (crown of S' is never {S'}).
  have h_ps :
      mergePost (R := R) (α := α) lbl S S'
          ((ofTree S ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))
            * ((cutSummandsN S').map
                (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum)
        = 0 := by
    rw [← Multiset.sum_map_mul_left, _root_.map_multiset_sum, Multiset.map_map]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
    show mergePost (R := R) (α := α) lbl S S'
          ((ofTree S ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))
            * (of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← of'_singleton, ← of'_add,
        mergePost_basis_tensor, if_neg]
    intro hcontra
    apply cutSummandsN_crown_ne_singleton S' p hp
    have heq : ({S} : Forest (Nonplanar α)) + p.1
             = ({S} : Forest (Nonplanar α)) + ({S'} : Forest (Nonplanar α)) := by
      rw [hcontra]; rfl
    exact Multiset.add_right_inj.mp heq
  -- Term 3 (cut-sum S × prim S'): symmetric (crown of S is never {S}).
  have h_sp :
      mergePost (R := R) (α := α) lbl S S'
          (((cutSummandsN S).map
              (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum
            * (ofTree S' ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))))
        = 0 := by
    rw [← Multiset.sum_map_mul_right, _root_.map_multiset_sum, Multiset.map_map]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
    show mergePost (R := R) (α := α) lbl S S'
          ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)
            * (ofTree S' ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← of'_singleton, ← of'_add,
        mergePost_basis_tensor, if_neg]
    intro hcontra
    apply cutSummandsN_crown_ne_singleton S p hp
    have heq : p.1 + ({S'} : Forest (Nonplanar α))
             = ({S} : Forest (Nonplanar α)) + ({S'} : Forest (Nonplanar α)) := by
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
    have hfw : ((p.1 + p'.1).map Nonplanar.numNodes).sum
             = (({S, S'} : Forest (Nonplanar α)).map Nonplanar.numNodes).sum := by
      rw [hcontra]
    rw [Multiset.map_add, Multiset.sum_add,
        show (({S, S'} : Forest (Nonplanar α)).map Nonplanar.numNodes).sum
            = S.numNodes + S'.numNodes from by
          simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
                     Multiset.map_singleton, Multiset.sum_singleton]] at hfw
    omega
  rw [h_pp, h_ps, h_sp, h_ss]
  simp only [add_zero]

/-- **Factor-out lemma** (MCB Lemma 1.4.1 Case 1, inductive step). Under
    `CutAvoidingN S T` and `CutAvoidingN S' T` (`T ≠ S, S'` and no Δ^ρ cut of `T`
    extracts `S` or `S'` as a crown), `mergeOp lbl S S'` commutes with left
    multiplication by the spectator `of' {T}`:

      mergeOp lbl S S' (of' {T} * w) = of' {T} * mergeOp lbl S S' w.

    Proof: `comulAlgHomN (of' {T} * w) = comulTreeN T * comulAlgHomN w`. The
    `ofTree T ⊗ 1` term vanishes (`{T} ⊄ {S, S'}`); the cut-sum splits via
    `cutSummandsN_filter_card_zero` into the surviving empty cut `(0, T)` — which
    by `Nonplanar`-tensor commutativity and `mergePost_right_one_tmul` yields
    `of' {T} * mergeOp lbl S S' w` — and the nonempty cuts, each annihilated since
    a crown `≤ {S, S'}` containing neither `S` nor `S'` must be empty. -/
theorem mergeOp_factor_out_singleton {R : Type*} [CommSemiring R] {α : Type*}
    [DecidableEq (Nonplanar α)] (lbl : α) {S S' T : Nonplanar α}
    (hT_S : CutAvoidingN S T) (hT_S' : CutAvoidingN S' T)
    (w : ConnesKreimer R (Nonplanar α)) :
    mergeOp (R := R) lbl S S' (of' ({T} : Forest (Nonplanar α)) * w)
      = of' ({T} : Forest (Nonplanar α)) * mergeOp (R := R) lbl S S' w := by
  obtain ⟨hT_ne_S, h_no_S_in_T_cuts⟩ := hT_S
  obtain ⟨hT_ne_S', h_no_S'_in_T_cuts⟩ := hT_S'
  -- mergeOp = mergePost ∘ comulAlgHomN; split the product through the alg hom.
  show (mergePost (R := R) (α := α) lbl S S' ∘ₗ comulAlgHomN.toLinearMap)
       (of' ({T} : Forest (Nonplanar α)) * w) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      show comulAlgHomN (R := R) (α := α) (of' ({T} : Forest (Nonplanar α)))
          = comulTreeN (R := R) T from comulAlgHomN_apply_ofTree T]
  unfold comulTreeN
  rw [add_mul]
  simp only [map_add]
  -- prim term `ofTree T ⊗ 1`: vanishes since `{T} ⊄ {S, S'}`.
  rw [show mergePost (R := R) (α := α) lbl S S'
        ((ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))) * comulAlgHomN w)
        = 0 from by
      rw [show (ofTree T : ConnesKreimer R (Nonplanar α))
            = of' ({T} : Forest (Nonplanar α)) from rfl]
      apply mergePost_left_mul_eq_zero_of_not_le
      intro h_le
      have hT_mem : T ∈ ({S, S'} : Forest (Nonplanar α)) :=
        Multiset.subset_of_le h_le (Multiset.mem_singleton.mpr rfl)
      rw [show ({S, S'} : Forest (Nonplanar α)) = S ::ₘ ({S'} : Forest (Nonplanar α))
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
        have hx_in : x ∈ ({S, S'} : Forest (Nonplanar α)) :=
          Multiset.subset_of_le h_le hx_mem
        rw [show ({S, S'} : Forest (Nonplanar α)) = S ::ₘ ({S'} : Forest (Nonplanar α))
              from rfl, Multiset.mem_cons, Multiset.mem_singleton] at hx_in
        rcases hx_in with h | h
        · subst h; exact h_no_S_in_T_cuts p hp_orig hx_mem
        · subst h; exact h_no_S'_in_T_cuts p hp_orig hx_mem
      rw [hp1_empty, Multiset.card_zero]]
  rw [add_zero]
  -- surviving empty cut: `(of' 0 ⊗ ofTree T) * cdw` → `of' {T} * mergeOp lbl S S' w`.
  rw [of'_zero,
      mul_comm ((1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R] ofTree T) (comulAlgHomN w),
      mergePost_right_one_tmul,
      mul_comm (mergePost (R := R) (α := α) lbl S S' (comulAlgHomN w)) (ofTree T)]
  rfl

/-- **Algebraic Merge with residual workspace** (M-C-B Lemma 1.4.1, Case 1). For
    any pair `(S, S')` and residual workspace `Fhat` with
    `CutAvoidingForestN ({S, S'}) Fhat` (S, S' ∉ Fhat as components, no cut on any
    `T ∈ Fhat` extracts S or S' — excludes the non-primitive matchings of the full
    coproduct, restricting to External Merge's member-level contribution per MCB
    Remark 1.3.8), Merge factors the spectator workspace through:

      mergeOp lbl S S' (of' ({S, S'} + Fhat)) = of' ({Nonplanar.node lbl {S, S'}} + Fhat).

    Induction on `Fhat` via `mergeOp_factor_out_singleton`. Without the
    disjointness, `mergeOp` produces the full sum-over-matchings (including
    Sideward contributions); MCB eliminate those via Minimal-Search cost weighting
    in the ε → 0 limit (the deferred `M^ε` arc). -/
theorem mergeOp_pair_residual {R : Type*} [CommSemiring R] {α : Type*}
    [DecidableEq (Nonplanar α)] (lbl : α) {S S' : Nonplanar α}
    {Fhat : Forest (Nonplanar α)}
    (hF : CutAvoidingForestN ({S, S'} : Forest (Nonplanar α)) Fhat) :
    mergeOp (R := R) lbl S S' (of' (({S, S'} : Forest (Nonplanar α)) + Fhat))
      = of' (({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α)) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    exact mergeOp_pair lbl S S'
  | cons T Fhat' ih =>
    obtain ⟨hT_S, hT_S'⟩ := CutAvoidingForestN.head_pair hF
    have ih' : mergeOp (R := R) lbl S S'
                  (of' (({S, S'} : Forest (Nonplanar α)) + Fhat'))
              = of' (({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α)) + Fhat') :=
      ih hF.of_cons
    have h_lhs_eq : ({S, S'} : Forest (Nonplanar α)) + T ::ₘ Fhat'
                  = ({T} : Forest (Nonplanar α))
                    + (({S, S'} : Forest (Nonplanar α)) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : Forest (Nonplanar α)) + Fhat' from rfl]; abel
    have h_rhs_eq : ({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α)) + T ::ₘ Fhat'
                  = ({T} : Forest (Nonplanar α))
                    + (({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α)) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : Forest (Nonplanar α)) + Fhat' from rfl]; abel
    rw [h_lhs_eq, h_rhs_eq,
        of'_add (R := R) ({T} : Forest (Nonplanar α))
          (({S, S'} : Forest (Nonplanar α)) + Fhat'),
        of'_add (R := R) ({T} : Forest (Nonplanar α))
          (({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α)) + Fhat'),
        mergeOp_factor_out_singleton lbl hT_S hT_S']
    exact congrArg (of' (R := R) ({T} : Forest (Nonplanar α)) * ·) ih'

/-! The linguistic External-Merge bridges `mergeOp_emR/emL_matches_Step` (which
related `mergeOp (Sum.inl L)` on the head-decorated `toNonplanar` projection to the
legacy `Step.emR/emL`) have been retired by the single-carrier migration. On the
bare `SyntacticObject` carrier the bridge is `Workspace.lean`'s `SyntacticObject.merge_toForest`
(`mergeOp_pair` with the bare `Sum.inr ()` label). -/

end Minimalist.Merge
