import Linglib.Syntax.Minimalist.Merge.External

/-!
# Internal Merge bridge: algebraic ↔ linguistic
[marcolli-chomsky-berwick-2025]

Realizes M-C-B Proposition 1.4.2 (book p. 50): Internal Merge as a
**composition of two algebraic Merges** on the canonical carrier
`ConnesKreimer R (Nonplanar α)` —

  IM(mover, T) = mergeOp lbl mover (T/mover) ∘ mergeOpUnit mover

where the first stage `mergeOpUnit mover` selects the Δ^ρ cut on `T` whose crown
forest equals `{mover}` (yielding `mover ⊗ (T/mover)`), and the second stage
performs External Merge between mover and the deletion-quotient.

## Contents

- `mergeOpUnit_apply_singleton{,_unique}`: per-cut decomposition of the unit-mover
  stage `mergeOpUnit β`. Surviving contributions are exactly the `cutSummandsN T`
  summands `p` with `p.1 = {β}`. Under uniqueness (the filtered sub-multiset is the
  singleton `{p0}`), the sum collapses.
- `mergeOp_im_composition`, `mergeOp_im_composition_moverLeft`: the IM composition
  theorem. Under the unique-cut hypothesis, the two-stage pipeline reduces to EM
  Case 1 (`mergeOp_pair`).
- `mergeOp_im_matches_Step`: bridge to linguistic `Step.im` via
  `((Step.im mover traceId).apply current).toNonplanar`.

## Deferred (substrate gap)

§4 — IM cost-survival at ε = 0 (`mergeOp_eps_zero_im_*`, MCB Prop 1.5.1 bullet 3)
— rides the same ε-weighted Δ^ρ gap as `External`'s ε arc (no `cutTotalDepth` on
`cutSummandsN`). Queued behind that substrate.

**Caveat (M-C-B p. 52 "virtual particles"):** the `mergeOpUnit` stage M_{β,1} is
virtual — not a stand-alone Merge in M-C-B's formalism. It is introduced as a
bookkeeping device to factor IM as composition; the linguistic Merge is the full
IM, not the unit stage on its own.
-/

namespace Minimalist.Merge

open scoped TensorProduct
open RootedTree RootedTree.ConnesKreimer

/-- **Per-cut reduction of `mergeOpUnit β (of' {T})`.** Unfolds the operator chain
    through `comulTreeN`'s primitive-plus-cut-sum decomposition; each cut's
    contribution is filtered by `mergePostUnit`'s `δ_{β, 1}` projection, surviving
    only when the crown forest equals `{β}`.

    The primitive `ofTree T ⊗ 1` term contributes `of' {β}` if `T = β`, else 0. -/
theorem mergeOpUnit_apply_singleton {α : Type*} [DecidableEq (Nonplanar α)]
    {R : Type*} [CommSemiring R] (β T : Nonplanar α) :
    mergeOpUnit (R := R) β (of' ({T} : Forest (Nonplanar α)))
      = (if T = β then of' ({β} : Forest (Nonplanar α)) else 0)
        + ((cutSummandsN T).map
            (fun p => if p.1 = ({β} : Forest (Nonplanar α))
              then of' (R := R) ({β} : Forest (Nonplanar α)) * ofTree p.2 else 0)).sum := by
  -- mergeOpUnit β = mergePostUnit β ∘ comulAlgHomN; reduce on of' {T} = ofTree T.
  show (mergePostUnit (R := R) (α := α) β ∘ₗ comulAlgHomN.toLinearMap)
       (of' ({T} : Forest (Nonplanar α))) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      show comulAlgHomN (R := R) (α := α) (of' ({T} : Forest (Nonplanar α)))
          = comulTreeN (R := R) T from comulAlgHomN_apply_ofTree T]
  unfold comulTreeN
  rw [map_add]
  congr 1
  · -- primitive part: `if {T} = {β} then of' {β} * 1 else 0` ↔ `if T = β then of' {β} else 0`.
    rw [show (ofTree T : ConnesKreimer R (Nonplanar α)) = of' ({T} : Forest (Nonplanar α))
          from rfl, mergePostUnit_basis_tensor]
    by_cases hTβ : T = β
    · rw [if_pos hTβ, if_pos (by rw [hTβ]), mul_one]
    · rw [if_neg hTβ, if_neg (fun h => hTβ (Multiset.singleton_inj.mp h))]
  · -- cut sum: each summand reduces via `mergePostUnit_basis_tensor`.
    rw [_root_.map_multiset_sum, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun p _ => ?_
    show mergePostUnit (R := R) (α := α) β (of' (R := R) p.1 ⊗ₜ[R] ofTree p.2) = _
    rw [mergePostUnit_basis_tensor]

/-- **Unique-cut specialization of `mergeOpUnit_apply_singleton`.** When `T ≠ β`
    (β is not the whole tree, so the primitive part vanishes) and `p0` is the
    *unique* `cutSummandsN T` summand with crown `{β}` (the filtered sub-multiset
    is `{p0}`), the per-cut sum collapses to a single contribution `of' {β} *
    ofTree p0.2` — pulling `β` out of `T` and leaving the deletion-remainder on the
    right channel.

    **Uniqueness is a substrate convenience, not a M-C-B requirement.** MCB Prop
    1.4.2 only requires "β is an accessible term of a component isomorphic to T",
    allowing multi-occurrence (a sum output). The single-summand hypothesis matches
    the worked example (book pp. 52–53). -/
theorem mergeOpUnit_apply_singleton_unique
    {α : Type*} [DecidableEq (Nonplanar α)] {R : Type*} [CommSemiring R]
    (β T : Nonplanar α) (p0 : Forest (Nonplanar α) × Nonplanar α)
    (h_filter : (cutSummandsN T).filter (fun p => p.1 = ({β} : Forest (Nonplanar α)))
      = {p0})
    (hTβ : T ≠ β) :
    mergeOpUnit (R := R) β (of' ({T} : Forest (Nonplanar α)))
      = of' (R := R) ({β} : Forest (Nonplanar α)) * ofTree p0.2 := by
  have hp0_cf : p0.1 = ({β} : Forest (Nonplanar α)) := by
    have hp0_mem : p0 ∈ (cutSummandsN T).filter (fun p => p.1 = ({β} : Forest (Nonplanar α))) := by
      rw [h_filter]; exact Multiset.mem_singleton_self p0
    exact (Multiset.mem_filter.mp hp0_mem).2
  rw [mergeOpUnit_apply_singleton, if_neg hTβ, zero_add,
      ← Multiset.filter_add_not (fun p => p.1 = ({β} : Forest (Nonplanar α))) (cutSummandsN T),
      Multiset.map_add, Multiset.sum_add, h_filter,
      Multiset.map_singleton, Multiset.sum_singleton, if_pos hp0_cf,
      show (((cutSummandsN T).filter (fun p => ¬ p.1 = ({β} : Forest (Nonplanar α)))).map
            (fun p => if p.1 = ({β} : Forest (Nonplanar α))
              then of' (R := R) ({β} : Forest (Nonplanar α)) * ofTree p.2 else 0)).sum = 0 from by
        refine Multiset.sum_eq_zero fun x hx => ?_
        obtain ⟨p, hp_filter, rfl⟩ := Multiset.mem_map.mp hx
        rw [if_neg (Multiset.mem_filter.mp hp_filter).2],
      add_zero]

/-- **M-C-B Proposition 1.4.2 (book p. 50): Internal Merge as composition,
    mover-LEFT order.** `Step.im mover traceId current = .node mover (current.replace
    mover (mkTrace traceId))` has mover LEFT, traced (the algebraic `Q`) RIGHT. The
    two-step composition `mergeOp lbl β Q ∘ mergeOpUnit β` applied to `{T}` produces
    `of' {Nonplanar.node lbl {β, Q}}`, where `Q = T/β` is the deletion-remainder of
    the unique cut extracting β.

    The label `lbl` of the merged root is a parameter (the operator layer is
    label-generic). -/
theorem mergeOp_im_composition_moverLeft
    {α : Type*} [DecidableEq (Nonplanar α)] {R : Type*} [CommSemiring R]
    (lbl : α) (β T Q : Nonplanar α) (p0 : Forest (Nonplanar α) × Nonplanar α)
    (h_filter : (cutSummandsN T).filter (fun p => p.1 = ({β} : Forest (Nonplanar α)))
      = {p0})
    (h_remainder : p0.2 = Q)
    (hTβ : T ≠ β) :
    mergeOp (R := R) lbl β Q
        (mergeOpUnit (R := R) β (of' ({T} : Forest (Nonplanar α))))
      = of' ({Nonplanar.node lbl {β, Q}} : Forest (Nonplanar α)) := by
  rw [mergeOpUnit_apply_singleton_unique β T p0 h_filter hTβ, h_remainder,
      ← of'_singleton, ← of'_add]
  -- {β} + {Q} = {β, Q} definitionally (mover-LEFT order, no swap).
  exact mergeOp_pair lbl β Q

/-- **IM composition, Q-LEFT (M-C-B `M_{T/β, β}`) order.** Q is the LEFT argument of
    the second merge; the result has Q-LEFT, β-RIGHT structure
    `of' {Nonplanar.node lbl {Q, β}}`. -/
theorem mergeOp_im_composition
    {α : Type*} [DecidableEq (Nonplanar α)] {R : Type*} [CommSemiring R]
    (lbl : α) (β T Q : Nonplanar α) (p0 : Forest (Nonplanar α) × Nonplanar α)
    (h_filter : (cutSummandsN T).filter (fun p => p.1 = ({β} : Forest (Nonplanar α)))
      = {p0})
    (h_remainder : p0.2 = Q)
    (hTβ : T ≠ β) :
    mergeOp (R := R) lbl Q β
        (mergeOpUnit (R := R) β (of' ({T} : Forest (Nonplanar α))))
      = of' ({Nonplanar.node lbl {Q, β}} : Forest (Nonplanar α)) := by
  rw [mergeOpUnit_apply_singleton_unique β T p0 h_filter hTβ, h_remainder,
      ← of'_singleton, ← of'_add,
      show ({β} : Forest (Nonplanar α)) + {Q} = ({Q, β} : Forest (Nonplanar α))
        from add_comm _ _]
  exact mergeOp_pair lbl Q β

/-! The linguistic Internal-Merge bridge `mergeOp_im_matches_Step` (which related the
`mergeOp ∘ mergeOpUnit` composition on the head-decorated `toNonplanar` projection to
the legacy `Step.im` + `⊕ Nat` trace index) has been retired by the single-carrier
migration. On the bare `SO` carrier the bridge is `Workspace.lean`'s
`SO.intMerge_toForest` (`mergeOp_im_composition` with the bare `Sum.inr ()` label and
the index-free `SO.traceLeaf`). -/

end Minimalist.Merge
