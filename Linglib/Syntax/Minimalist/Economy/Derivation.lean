/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Derivation
public import Linglib.Syntax.Minimalist.Economy.NoComplexityLoss
public import Linglib.Syntax.Minimalist.Economy.MinimalYield.Basic

/-!
# Economy of derivations

An admissible derivation step relates the workspace of the current object, its items and the
items still to come to the workspace of the object it builds and those items. That transformation
satisfies No Complexity Loss, and Minimal Yield under trace counting when its operands are not
traces ([marcolli-chomsky-berwick-2025] §1.6). Along an admissible derivation the workspaces of its
stages therefore form a chain of economical transformations.

## Main definitions

* `Minimalist.SyntacticObject.Derivation.workspaces`: the workspaces of a derivation's stages.

## Main results

* `Minimalist.SyntacticObject.Step.noComplexityLoss`, `Step.minimalYield`: an admissible step is
  economical.
* `Minimalist.SyntacticObject.Derivation.isChain_noComplexityLoss`, `isChain_minimalYield`: so is
  every step of an admissible derivation.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.SyntacticObject

open ConnesKreimer

/-- An object with a unique accessible proper term is a Merge. -/
theorem exists_eq_merge_of_count_terms {mover current : SyntacticObject}
    (h : current.terms.count mover = 1) (hne : current ≠ mover) : ∃ l r, current = merge l r := by
  induction current using ind with
  | leaf tok =>
    rw [terms_leaf] at h
    exact absurd (Multiset.mem_singleton.mp (Multiset.count_pos.mp (by omega))).symm hne
  | trace =>
    rw [terms_trace] at h
    exact absurd (Multiset.mem_singleton.mp (Multiset.count_pos.mp (by omega))).symm hne
  | traceOf tok =>
    rw [terms_traceOf] at h
    exact absurd (Multiset.mem_singleton.mp (Multiset.count_pos.mp (by omega))).symm hne
  | merge l r _ _ => exact ⟨l, r, rfl⟩

theorem value_isLeft_apply (step : Step) (current : SyntacticObject) :
    (step.apply current).val.value.isLeft := by
  cases step with
  | em side item => cases side <;> simp [Step.apply]
  | im mover _ => simp [Step.apply]

private theorem traceLeafCount_lt_numNodes {S : SyntacticObject} (h : S.val.value.isLeft) :
    S.val.traceLeafCount < S.val.numNodes := by
  obtain ⟨a, ha⟩ := Sum.isLeft_iff.mp h
  exact UnorderedTree.traceLeafCount_lt_numNodes_of_rootInl _ a ha

variable {step : Step} {current : SyntacticObject} {W : Workspace}

/-- The trace cut extracting the mover of an admissible Internal Merge. -/
private theorem mem_cutSummandsCN_mover {mover : SyntacticObject} (hm : mover.val.value.isLeft)
    (h : current.terms.count mover = 1) (hne : current ≠ mover) :
    ({mover.val}, (deleteAccessible mover current).val) ∈ cutSummandsCN traceEncoder current.val :=
  Multiset.mem_of_mem_filter (p := fun p ↦ p.1 = {mover.val}) <| by
    rw [cutSummandsCN_filter_mover hm h hne]
    exact Multiset.mem_singleton_self _

/-- An admissible step satisfies No Complexity Loss. -/
theorem Step.noComplexityLoss (h : step.Admissible current W) :
    NoComplexityLoss (({current} + step.items + W).map Subtype.val)
      (({step.apply current} + W).map Subtype.val) := by
  cases step with
  | em side item =>
    rw [Step.apply_em, merge_comm]
    simp only [Step.items, Multiset.map_add, Multiset.map_singleton, merge_val]
    exact NoComplexityLoss.em_case1 Vertex.bare current.val item.val _
  | im mover _ =>
    obtain ⟨hm, hc, hne, -⟩ := h
    have hw := cutSummandsCN_numNodes traceEncoder current.val _ (mem_cutSummandsCN_mover hm hc hne)
    simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_singleton] at hw
    simp only [Step.items, add_zero, Step.apply_im, Multiset.map_add, Multiset.map_singleton,
      merge_val]
    exact NoComplexityLoss.im_residual Vertex.bare (by omega) _

/-- An admissible step whose operands are not traces satisfies Minimal Yield under trace
    counting. -/
theorem Step.minimalYield (h : step.Admissible current W) (hcur : current.val.value.isLeft)
    (hitems : ∀ i ∈ step.items, i.val.value.isLeft) :
    MinimalYield UnorderedTree.accessibleCount (({current} + step.items + W).map Subtype.val)
      (({step.apply current} + W).map Subtype.val) := by
  cases step with
  | em side item =>
    rw [Step.apply_em, merge_comm]
    simp only [Step.items, Multiset.mem_singleton, forall_eq] at hitems
    simp only [Step.items, Multiset.map_add, Multiset.map_singleton, merge_val]
    exact (MinimalYield.em_pair_accessibleCount none (traceLeafCount_lt_numNodes hcur)
      (traceLeafCount_lt_numNodes hitems)).add_right _
  | im mover _ =>
    obtain ⟨hm, hc, hne, -⟩ := h
    have hp := mem_cutSummandsCN_mover hm hc hne
    obtain ⟨l, r, rfl⟩ := exists_eq_merge_of_count_terms hc hne
    simp only [Step.items, add_zero, Step.apply_im, Multiset.map_add, Multiset.map_singleton,
      merge_val, Multiset.pair_comm (deleteAccessible mover (merge l r)).val] at hp ⊢
    exact (MinimalYield.im_accessibleCount_of_cut none none traceEncoder _ _ hp mover.val
      rfl).add_right _

/-- The workspaces after each of a list of steps hold the object built so far beside the items
    still to come. -/
noncomputable def Step.workspacesAfter : List Step → SyntacticObject → List Workspace
  | [], _ => []
  | step :: steps, current =>
      ({step.apply current} + Step.itemsList steps) ::
        Step.workspacesAfter steps (step.apply current)

private theorem isChain_of_step {R : Workspace → Workspace → Prop} {P : SyntacticObject → Prop}
    (hR : ∀ {step : Step} {current : SyntacticObject} {W : Workspace}, step.Admissible current W →
      P current → (∀ i ∈ step.items, P i) →
        R ({current} + step.items + W) ({step.apply current} + W))
    (hP : ∀ step current, P (Step.apply step current)) :
    ∀ (steps : List Step) (current : SyntacticObject), Step.AdmissibleList steps current →
      P current → (∀ i ∈ Step.itemsList steps, P i) →
      List.IsChain R (({current} + Step.itemsList steps) :: Step.workspacesAfter steps current)
  | [], _, _, _, _ => .singleton _
  | step :: steps, current, ⟨h, hs⟩, hcur, hitems => by
    rw [Step.itemsList_cons] at hitems ⊢
    refine .cons_cons ?_ (isChain_of_step hR hP steps _ hs (hP step current)
      fun i hi ↦ hitems i (Multiset.mem_add.mpr (.inr hi)))
    rw [← add_assoc]
    exact hR h hcur fun i hi ↦ hitems i (Multiset.mem_add.mpr (.inl hi))

namespace Derivation

/-- The workspaces of a derivation's stages hold the initial object beside its items, then after
    each step the object built so far beside the items still to come. -/
noncomputable def workspaces (d : Derivation) : List Workspace :=
  ({d.initial} + d.items) :: Step.workspacesAfter d.steps d.initial

/-- Every step of an admissible derivation satisfies No Complexity Loss. -/
theorem isChain_noComplexityLoss {d : Derivation} (hd : d.Admissible) :
    d.workspaces.IsChain
      (fun W W' : Workspace ↦ NoComplexityLoss (W.map Subtype.val) (W'.map Subtype.val)) :=
  isChain_of_step (P := fun _ ↦ True) (fun h _ _ ↦ Step.noComplexityLoss h) (fun _ _ ↦ trivial)
    d.steps d.initial hd trivial fun _ _ ↦ trivial

/-- Every step of an admissible derivation whose initial object and items are not traces satisfies
    Minimal Yield under trace counting. -/
theorem isChain_minimalYield {d : Derivation} (hd : d.Admissible)
    (hinit : d.initial.val.value.isLeft) (hitems : ∀ i ∈ d.items, i.val.value.isLeft) :
    d.workspaces.IsChain (fun W W' : Workspace ↦
      MinimalYield UnorderedTree.accessibleCount (W.map Subtype.val) (W'.map Subtype.val)) :=
  isChain_of_step (P := fun S ↦ S.val.value.isLeft) (fun h hcur hi ↦ Step.minimalYield h hcur hi)
    value_isLeft_apply d.steps d.initial hd hinit hitems

end Derivation

end Minimalist.SyntacticObject
