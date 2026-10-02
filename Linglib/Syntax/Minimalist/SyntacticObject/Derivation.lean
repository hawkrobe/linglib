/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Minimalist.Merge.SyntacticObject

/-!
# Derivations

An ordered derivation is an initial syntactic object with a sequence of Merge steps. External Merge
adds an item as the daughter on a side, and Internal Merge raises a mover: the step re-merges the
mover with the remainder `deleteAccessible mover current`, the current object with the mover's
occurrences replaced by the trace of the mover's head. Each step is the algebraic Merge on the
workspace of the current object, the items it introduces, and the items still to come, when it
matches no accessible term of those items and an Internal Merge raises a uniquely accessible term
(`Step.mergeOp_workspace`); an admissible derivation is then the iterated algebraic Merge on the
workspace of its initial object and its items (`Derivation.mergeOpList_initial`). The node being
commutative, the two sides build the same object; the side is a planarization datum that matters
only for the surface order, which `Linearization/Replay.lean` recovers on an ordered planar
accumulator, since the final object is an unordered quotient. Since `node` is noncomputable, so are
`Step.apply` and `Derivation.final`, while the movers are read off the steps. A derivation extends
by further steps, whose early stages and movers are the original's, and normalizes by moving every
External Merge to the left, which changes no stage and no mover.

## Main definitions

* `Minimalist.SyntacticObject.Side`, `Step`, `Step.apply`, `Step.mover?`, `Step.mergeOp`,
  `Step.Admissible`
* `Minimalist.SyntacticObject.Derivation`, `Derivation.final`, `stageAt`, `movedItems`, `take`,
  `append`, `leftward`, `items`, `Admissible`

## Main results

* `Minimalist.SyntacticObject.Step.apply_em`: the sides build the same object.
* `Minimalist.SyntacticObject.Step.mergeOp_workspace`: an admissible step is the algebraic Merge
  on the workspace.
* `Minimalist.SyntacticObject.Derivation.mergeOpList_initial`: an admissible derivation is the
  iterated algebraic Merge.
* `Minimalist.SyntacticObject.Derivation.stageAt_append_of_le`, `movedItems_append`: extension
  keeps the early stages and the movers.
* `Minimalist.SyntacticObject.Derivation.stageAt_leftward`, `movedItems_leftward`: the sides
  change no stage and no mover.

## References

* [marcolli-chomsky-berwick-2025], §1.2 (Definition 1.2.6) and §1.4 (Lemma 1.4.1,
  Proposition 1.4.2)
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

namespace SyntacticObject

/-! ### Steps -/

/-- External Merge attaches the new item on a side, a planarization datum that externalization
    reads and the derived object ignores. -/
inductive Side where
  | left
  | right
  deriving DecidableEq, Repr, Fintype

/-- A derivation step. `im` records only the mover; the trace it leaves is that of its head. -/
inductive Step where
  /-- External Merge, the new item as the daughter on `side`. -/
  | em (side : Side) (item : SyntacticObject)
  /-- Internal Merge raises `mover`, leaving the trace of its head in its place. -/
  | im (mover : SyntacticObject)

/-- A step builds a node: External Merge with the item on the given side, Internal Merge of the
    remainder and the mover. -/
noncomputable def Step.apply (step : Step) (current : SyntacticObject) : SyntacticObject :=
  match step with
  | .em .left item => merge item current
  | .em .right item => merge current item
  | .im mover => merge (deleteAccessible mover current) mover

theorem Step.apply_em_left (item current : SyntacticObject) :
    (Step.em .left item).apply current = merge item current := rfl

theorem Step.apply_em_right (item current : SyntacticObject) :
    (Step.em .right item).apply current = merge current item := rfl

theorem Step.apply_im (mover current : SyntacticObject) :
    (Step.im mover).apply current = merge (deleteAccessible mover current) mover := rfl

/-- The sides build the same object; they differ only at externalization. -/
theorem Step.apply_em (side : Side) (item current : SyntacticObject) :
    (Step.em side item).apply current = merge item current := by
  cases side
  · rfl
  · exact merge_comm current item

/-- The mover of an Internal-Merge step. -/
def Step.mover? : Step → Option SyntacticObject
  | .im mover => some mover
  | .em _ _ => none

@[simp] theorem Step.mover?_em (side : Side) (item : SyntacticObject) :
    (Step.em side item).mover? = none := rfl

@[simp] theorem Step.mover?_im (mover : SyntacticObject) : (Step.im mover).mover? = some mover :=
  rfl

/-- The step with its External Merge on the left; Internal Merge is unchanged. -/
def Step.leftward : Step → Step
  | .em _ item => .em .left item
  | .im mover => .im mover

@[simp] theorem Step.leftward_em (side : Side) (item : SyntacticObject) :
    (Step.em side item).leftward = .em .left item := rfl

@[simp] theorem Step.leftward_im (mover : SyntacticObject) : (Step.im mover).leftward = .im mover :=
  rfl

@[simp] theorem Step.mover?_leftward (step : Step) : step.leftward.mover? = step.mover? := by
  cases step <;> rfl

/-- A step and its leftward form build the same object. -/
theorem Step.apply_leftward (step : Step) (current : SyntacticObject) :
    step.leftward.apply current = step.apply current := by
  cases step with
  | em side item => rw [Step.leftward_em, Step.apply_em, Step.apply_em]
  | im _ => rfl

/-! ### Derivations as workspace Merges

A step merges the current object with the items it introduces, beside a spectator workspace of the
items still to come. When it matches no accessible term of the spectators, and an Internal Merge
raises a uniquely accessible proper term, the step is the algebraic Merge on the workspace
(`Step.mergeOp_workspace`), and a derivation is the iterated algebraic Merge on the workspace of its
initial object and its items (`mergeOpList_initial`). -/

/-- The item an External Merge step introduces. -/
def Step.items : Step → Workspace
  | .em _ item => {item}
  | .im _ => 0

/-- The items a list of steps introduces. -/
def Step.itemsList (steps : List Step) : Workspace :=
  (steps.map Step.items).sum

@[simp] theorem Step.itemsList_nil : Step.itemsList [] = 0 := rfl

@[simp] theorem Step.itemsList_cons (step : Step) (steps : List Step) :
    Step.itemsList (step :: steps) = step.items + Step.itemsList steps := by
  simp [Step.itemsList]

/-- A step applies an algebraic Merge at the current object: External Merge with the item, or the
    unit stage followed by External Merge of the remainder with the mover. -/
noncomputable def Step.mergeOp (step : Step)
    (current : SyntacticObject) :
    ConnesKreimer ℤ (UnorderedTree Vertex) →ₗ[ℤ] ConnesKreimer ℤ (UnorderedTree Vertex) :=
  match step with
  | .em _ item => Merge.mergeOpC traceEncoder Vertex.bare current.val item.val
  | .im mover => Merge.mergeOpC traceEncoder Vertex.bare (deleteAccessible mover current).val
      mover.val ∘ₗ Merge.mergeOpUnitC traceEncoder mover.val

/-- A step at the current object is admissible beside a spectator workspace `W` when it matches
    no accessible term of `W`, and an Internal Merge raises a uniquely accessible proper term that
    is not a trace. -/
def Step.Admissible (current : SyntacticObject)
    (W : Workspace) : Step → Prop
  | .em _ item => ∀ U ∈ W, current ∉ U.terms ∧ item ∉ U.terms
  | .im mover => mover.val.value.isLeft ∧ current.terms.count mover = 1 ∧ current ≠ mover ∧
      ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms

/-- An admissible step is the algebraic Merge on the workspace of the current object, the items
    it introduces, and the spectators. -/
theorem Step.mergeOp_workspace {step : Step}
    {current : SyntacticObject} {W : Workspace} (h : step.Admissible current W) :
    step.mergeOp current (ConnesKreimer.of' (({current} + step.items + W).map Subtype.val))
      = ConnesKreimer.of' (({step.apply current} + W).map Subtype.val) := by
  cases step with
  | em side item =>
    rw [Step.apply_em, merge_comm]
    exact mergeOpC_node_residual traceEncoder current item h
  | im mover =>
    obtain ⟨hm, hc, hne, hW⟩ := h
    exact mergeOpC_im_residual hm hc hne hW

/-- The algebraic Merges of a list of steps from the current object, composed in order. -/
noncomputable def Step.mergeOpList :
    List Step → SyntacticObject →
      ConnesKreimer ℤ (UnorderedTree Vertex) →ₗ[ℤ] ConnesKreimer ℤ (UnorderedTree Vertex)
  | [], _ => LinearMap.id
  | step :: steps, current => Step.mergeOpList steps (step.apply current) ∘ₗ step.mergeOp current

/-- Every step of a list is admissible beside the items still to come. -/
def Step.AdmissibleList : List Step → SyntacticObject → Prop
  | [], _ => True
  | step :: steps, current =>
      step.Admissible current (Step.itemsList steps) ∧
        Step.AdmissibleList steps (step.apply current)

/-- Admissible steps compose to the algebraic Merge from the workspace of the current object and
    the items they introduce to the object they build. -/
theorem Step.mergeOpList_workspace :
    ∀ (steps : List Step) (current : SyntacticObject), Step.AdmissibleList steps current →
      Step.mergeOpList steps current
          (ConnesKreimer.of' (({current} + Step.itemsList steps).map Subtype.val))
        = ConnesKreimer.of' {(steps.foldl (fun so step => step.apply so) current).val}
  | [], current, _ => by
    simp [Step.mergeOpList]
  | step :: steps, current, ⟨h, hs⟩ => by
    rw [Step.mergeOpList, LinearMap.comp_apply, Step.itemsList_cons, ← add_assoc,
      Step.mergeOp_workspace h, List.foldl_cons]
    exact Step.mergeOpList_workspace steps (step.apply current) hs

/-! ### Derivations -/

/-- An initial syntactic object with a sequence of steps. -/
structure Derivation where
  /-- The initial syntactic object (a lexical item, in canonical derivations). -/
  initial : SyntacticObject
  /-- The ordered sequence of Merge/Move steps. -/
  steps : List Step

namespace Derivation

/-- The object after every step. -/
noncomputable def final (d : Derivation) : SyntacticObject :=
  d.steps.foldl (fun so step => step.apply so) d.initial

/-- The object after the first `n` steps. -/
noncomputable def stageAt (d : Derivation) (n : Nat) : SyntacticObject :=
  (d.steps.take n).foldl (fun so step => step.apply so) d.initial

/-- The number of derivation steps. -/
def length (d : Derivation) : Nat := d.steps.length

/-- The movers of the `im` steps. -/
def movedItems (d : Derivation) : List SyntacticObject := d.steps.filterMap Step.mover?

/-- The first `n` steps. -/
def take (d : Derivation) (n : Nat) : Derivation := ⟨d.initial, d.steps.take n⟩

/-- The derivation continued by `steps`. -/
def append (d : Derivation) (steps : List Step) : Derivation := ⟨d.initial, d.steps ++ steps⟩

@[simp] theorem stageAt_zero (d : Derivation) : d.stageAt 0 = d.initial := by
  simp [stageAt]

theorem stageAt_length (d : Derivation) : d.stageAt d.steps.length = d.final := by
  simp [stageAt, final, List.take_length]

@[simp] theorem final_take (d : Derivation) (n : Nat) : (d.take n).final = d.stageAt n := rfl

/-! ### Extension

The early stages and the movers of an extended derivation are the original's. -/

@[simp] theorem length_append (d : Derivation) (steps : List Step) :
    (d.append steps).length = d.length + steps.length := by
  simp [length, append]

@[simp] theorem append_assoc (d : Derivation) (steps steps' : List Step) :
    (d.append steps).append steps' = d.append (steps ++ steps') := by
  simp [append]

/-- The first `n ≤ d.length` steps of an extension are `d`'s. -/
theorem take_append_of_le {d : Derivation} {n : Nat} (h : n ≤ d.length) (steps : List Step) :
    (d.append steps).take n = d.take n := by
  simp [take, append, List.take_append_of_le_length h]

@[simp] theorem take_length_append (d : Derivation) (steps : List Step) :
    (d.append steps).take d.length = d := by
  unfold take append
  rw [length, List.take_left]

theorem stageAt_append_of_le {d : Derivation} {n : Nat} (h : n ≤ d.length) (steps : List Step) :
    (d.append steps).stageAt n = d.stageAt n := by
  rw [← final_take, ← final_take, take_append_of_le h]

theorem final_append (d : Derivation) (steps : List Step) :
    (d.append steps).final = steps.foldl (fun so step => step.apply so) d.final := by
  simp [final, append, List.foldl_append]

@[simp] theorem movedItems_append (d : Derivation) (steps : List Step) :
    (d.append steps).movedItems = d.movedItems ++ steps.filterMap Step.mover? := by
  simp [movedItems, append, List.filterMap_append]

/-- A step at index `i` has a mover only if `i` indexes a step. -/
theorem lt_length_of_mem_mover? {d : Derivation} {i : Nat} {m : SyntacticObject}
    (h : m ∈ d.steps[i]? >>= Step.mover?) : i < d.length := by
  by_contra hlt
  rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at h
  simp at h

/-! ### The sides of External Merge

The node being commutative, the derived object does not depend on the sides at which External
Merge attaches the items; `leftward` is the normal form, and the stages and movers of a
derivation are those of its normal form. -/

/-- The derivation with every External Merge on the left. -/
def leftward (d : Derivation) : Derivation := ⟨d.initial, d.steps.map Step.leftward⟩

@[simp] theorem stageAt_leftward (d : Derivation) (n : Nat) :
    d.leftward.stageAt n = d.stageAt n := by
  simp only [stageAt, leftward, ← List.map_take, List.foldl_map, Step.apply_leftward]

@[simp] theorem final_leftward (d : Derivation) : d.leftward.final = d.final := by
  simp only [final, leftward, List.foldl_map, Step.apply_leftward]

@[simp] theorem movedItems_leftward (d : Derivation) : d.leftward.movedItems = d.movedItems := by
  simp [movedItems, leftward, List.filterMap_map]

/-- The items a derivation introduces by External Merge. -/
def items (d : Derivation) : Workspace := Step.itemsList d.steps

/-- A derivation is admissible when each of its steps is, beside the items still to come. -/
def Admissible (d : Derivation) : Prop := Step.AdmissibleList d.steps d.initial

/-- An admissible derivation is the iterated algebraic Merge on the workspace of its initial object
    and its items: the composite of its steps' Merges sends that workspace to its final object. -/
theorem mergeOpList_initial {d : Derivation} (hd : d.Admissible) :
    Step.mergeOpList d.steps d.initial (ConnesKreimer.of' (({d.initial} + d.items).map Subtype.val))
      = ConnesKreimer.of' {d.final.val} :=
  Step.mergeOpList_workspace d.steps d.initial hd

end Derivation

end SyntacticObject

/-! ### Carrier tests -/

private def demoTok (i : Nat) : SyntacticObject := SyntacticObject.leaf ⟨.simple .N [], i⟩

example :
    (Derivation.mk (demoTok 0)
      [Step.em .left (demoTok 1), Step.im (demoTok 1),
       Step.em .right (demoTok 2), Step.im (demoTok 2)]).movedItems = [demoTok 1, demoTok 2] := by
  simp [Derivation.movedItems, demoTok]

example : (Derivation.mk (demoTok 0) [Step.em .left (demoTok 1)]).length = 1 := rfl

/-- Extension keeps the movers and adds the new ones. -/
example :
    ((Derivation.mk (demoTok 0) [Step.em .left (demoTok 1)]).append
      [Step.im (demoTok 1)]).movedItems = [demoTok 1] := by
  simp [Derivation.movedItems, Derivation.append, demoTok]

/-- Raising the item a derivation has just merged is admissible, so `mergeOpList_initial` applies
    to it. -/
example :
    (Derivation.mk (demoTok 0) [Step.em .left (demoTok 1), Step.im (demoTok 1)]).Admissible := by
  have hne : merge (demoTok 1) (demoTok 0) ≠ demoTok 1 := fun h ↦ by
    have := congrArg (fun s : SyntacticObject ↦ s.val.numNodes) h
    simp [demoTok] at this
  simp only [Derivation.Admissible, Step.AdmissibleList, Step.Admissible, Step.itemsList_cons,
    Step.itemsList_nil, Step.items, Step.apply_em_left, add_zero, Multiset.notMem_zero,
    IsEmpty.forall_iff, implies_true, and_true, true_and, ne_eq, hne, not_false_eq_true]
  refine ⟨rfl, ?_⟩
  rw [terms_merge, Multiset.count_cons_of_ne hne.symm]
  simp [demoTok]

end Minimalist
