module

public import Linglib.Syntax.Minimalist.Merge.External

/-!
# Internal Merge

Internal Merge ([marcolli-chomsky-berwick-2025] Proposition 1.4.2) is the composition
`M_{T/β,β} ∘ M_{β,1}`. The unit stage selects a cut of `T` with crown `{β}`, giving the two-object
workspace `{β, T/β}`, and External Merge then merges `β` with the quotient. When one cut extracts
`β`, the composition yields `node lbl {T/β, β}` over every cut enumeration admitting Merge
(`mergeOpG_im_composition`). At the pruning cuts the quotient is the deletion remainder; at the
trace cuts it keeps a trace in place of `β` (`mergeOpC_im_composition`).

## Main results

* `Minimalist.Merge.mergeOpUnitG_apply_singleton`, `mergeOpUnitG_apply_singleton_unique`: the
  unit stage on one tree, a sum over the cuts with crown `{β}`.
* `Minimalist.Merge.mergeOpG_im_composition`, `mergeOp_im_composition`,
  `mergeOpC_im_composition`: Internal Merge as a composition of Merges.

## Implementation notes

The composition theorems assume a single cut extracting `β`, as in the book's worked example.
Proposition 1.4.2 does not; with several occurrences of `β` the unit stage is a sum over them
(`mergeOpUnitG_apply_singleton`).

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.Merge

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq (UnorderedTree α)]
  {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}

/-- On one tree `T`, the primitive term of the unit stage contributes `β` if `T = β`, and each
    cut with crown `{β}` contributes `β` beside its trunk. -/
theorem mergeOpUnitG_apply_singleton (β T : UnorderedTree α) :
    mergeOpUnitG (R := R) cuts β (of' ({T} : Forest (UnorderedTree α)))
      = (if T = β then of' ({β} : Forest (UnorderedTree α)) else 0)
        + ((cuts T).map
            (fun p => if p.1 = ({β} : Forest (UnorderedTree α))
              then of' (R := R) ({β} : Forest (UnorderedTree α)) * ofTree p.2 else 0)).sum := by
  rw [mergeOpUnitG, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    show (of' ({T} : Forest (UnorderedTree α)) : ConnesKreimer R (UnorderedTree α)) = ofTree T
      from rfl, comulAlgHomNG_apply_ofTree, comulTreeNG, map_add, map_multiset_sum,
    Multiset.map_map]
  congr 1
  · rw [show (ofTree T : ConnesKreimer R (UnorderedTree α)) = of' {T} from rfl,
      mergePostUnit_basis_tensor, mul_one]
    simp only [Multiset.singleton_inj]
  · exact congrArg Multiset.sum
      (Multiset.map_congr rfl fun p _ ↦ mergePostUnit_basis_tensor β p.1 (ofTree p.2))

/-- When `T ≠ β` and exactly one cut of `T` has crown `{β}`, the unit stage moves `β` to its own
    component beside that cut's trunk. -/
theorem mergeOpUnitG_apply_singleton_unique (β T : UnorderedTree α)
    (p0 : Forest (UnorderedTree α) × UnorderedTree α)
    (h_filter : (cuts T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) = {p0})
    (hTβ : T ≠ β) :
    mergeOpUnitG (R := R) cuts β (of' ({T} : Forest (UnorderedTree α)))
      = of' (R := R) ({β} : Forest (UnorderedTree α)) * ofTree p0.2 := by
  have hp0 : p0 ∈ (cuts T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) := by
    rw [h_filter]; exact Multiset.mem_singleton_self p0
  rw [mergeOpUnitG_apply_singleton, ite_eq_right hTβ, zero_add,
    ← Multiset.filter_add_not (fun p => p.1 = ({β} : Forest (UnorderedTree α))) (cuts T),
    Multiset.map_add, Multiset.sum_add, h_filter, Multiset.map_singleton, Multiset.sum_singleton,
    ite_eq_left (Multiset.mem_filter.mp hp0).2, Multiset.sum_eq_zero, add_zero]
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
  exact ite_eq_right (Multiset.mem_filter.mp hp).2

/-- Internal Merge as the composition `M_{T/β,β} ∘ M_{β,1}` over a cut enumeration admitting
    Merge, for `β` extracted from `T` by a single cut with trunk `Q`. -/
theorem mergeOpG_im_composition [IsMergeCuts cuts] (lbl : α) (β T Q : UnorderedTree α)
    (p0 : Forest (UnorderedTree α) × UnorderedTree α)
    (h_filter : (cuts T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) = {p0})
    (h_remainder : p0.2 = Q) (hTβ : T ≠ β) :
    mergeOpG (R := R) cuts lbl Q β
        (mergeOpUnitG (R := R) cuts β (of' ({T} : Forest (UnorderedTree α))))
      = of' ({UnorderedTree.node lbl {Q, β}} : Forest (UnorderedTree α)) := by
  rw [mergeOpUnitG_apply_singleton_unique β T p0 h_filter hTβ, h_remainder, ← of'_singleton,
    ← of'_add, add_comm]
  exact mergeOpG_pair lbl Q β

/-- Internal Merge at the pruning cuts. -/
theorem mergeOp_im_composition (lbl : α) (β T Q : UnorderedTree α)
    (p0 : Forest (UnorderedTree α) × UnorderedTree α)
    (h_filter : (cutSummandsN T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) = {p0})
    (h_remainder : p0.2 = Q) (hTβ : T ≠ β) :
    mergeOp (R := R) lbl Q β (mergeOpUnit (R := R) β (of' ({T} : Forest (UnorderedTree α))))
      = of' ({UnorderedTree.node lbl {Q, β}} : Forest (UnorderedTree α)) :=
  mergeOpG_im_composition lbl β T Q p0 h_filter h_remainder hTβ

omit [DecidableEq (UnorderedTree α)] in
/-- Internal Merge at the trace cuts: the mover `m` is merged with the trunk `Q`, which keeps a
    trace in its place. -/
theorem mergeOpC_im_composition {β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))]
    (τ : UnorderedTree (α ⊕ β) → β) (lbl : α ⊕ β) (m T Q : UnorderedTree (α ⊕ β))
    (p0 : Forest (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β))
    (h_filter : (cutSummandsCN τ T).filter
      (fun p => p.1 = ({m} : Forest (UnorderedTree (α ⊕ β)))) = {p0})
    (h_remainder : p0.2 = Q) (hTm : T ≠ m) :
    mergeOpC (R := R) τ lbl Q m
        (mergeOpUnitC (R := R) τ m (of' ({T} : Forest (UnorderedTree (α ⊕ β)))))
      = of' ({UnorderedTree.node lbl {Q, m}} : Forest (UnorderedTree (α ⊕ β))) :=
  mergeOpG_im_composition lbl m T Q p0 h_filter h_remainder hTm

end Minimalist.Merge
