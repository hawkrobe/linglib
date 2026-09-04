/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Minimalist.SyntacticObject.Replace
import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# Derivations

An ordered derivation is an initial syntactic object with a sequence of Merge steps. External Merge
adds an item as the daughter on a side, and Internal Merge raises a mover: the step re-merges the
mover with the remainder `deleteAccessible mover current`, the current object with the mover's
occurrences replaced by the trace of the mover's head. Each step applies the carrier node, so the
derivation's Merge is the workspace Merge by construction, and the node being commutative, the two
sides build the same object; the side is a planarization datum that matters only for the surface
order, which `Linearization/Replay.lean` recovers on an ordered planar accumulator, since the final
object is an unordered quotient. Since `node` is noncomputable, so are `Step.apply` and
`Derivation.final`, while the movers are read off the steps. A derivation extends by further steps,
whose early stages and movers are the original's, and normalizes by moving every External Merge to
the left, which changes no stage and no mover.

## Main definitions

* `Minimalist.SyntacticObject.Side`, `Step`, `Step.apply`, `Step.mover?`, `deleteAccessible`
* `Minimalist.SyntacticObject.Derivation`, `Derivation.final`, `stageAt`, `movedItems`, `take`,
  `append`, `leftward`

## Main results

* `Minimalist.SyntacticObject.Step.apply_em`: the sides build the same object.
* `Minimalist.SyntacticObject.Derivation.stageAt_append_of_le`, `movedItems_append`: extension
  keeps the early stages and the movers.
* `Minimalist.SyntacticObject.Derivation.stageAt_leftward`, `movedItems_leftward`: the sides
  change no stage and no mover.

## References

* [marcolli-chomsky-berwick-2025], §1.2 (Definition 1.2.6) and §1.4 (Lemma 1.4.1,
  Proposition 1.4.2)
-/

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

namespace SyntacticObject

/-! ### Steps -/

/-- The side at which External Merge attaches the new item: the planarization datum that
    externalization reads and the derived object ignores. -/
inductive Side where
  | left
  | right
  deriving DecidableEq, Repr, Fintype

/-- A derivation step. `im` records only the mover; the trace it leaves is that of its head. -/
inductive Step where
  /-- External Merge, the new item as the daughter on `side`. -/
  | em (side : Side) (item : SyntacticObject)
  /-- Internal Merge: raise `mover`, leaving the trace of its head in its place. -/
  | im (mover : SyntacticObject)

/-- The trace a moved object leaves: the trace of its head by selection, the bare trace when it
    has none. -/
def headTrace (s : SyntacticObject) : SyntacticObject := s.selHead.elim trace traceOf

/-- The remainder `T/mover`: the current object with the mover's occurrences replaced by the
    trace of its head, the remaining tree of an admissible cut ([marcolli-chomsky-berwick-2025],
    Definition 1.2.6). For a uniquely accessible mover this is the deletion remainder that
    `Merge.mergeOp_im_composition` extracts; `replace` extends it to a chain of occurrences. -/
noncomputable def deleteAccessible (mover current : SyntacticObject) : SyntacticObject :=
  current.replace mover mover.headTrace

@[simp] theorem deleteAccessible_val (mover current : SyntacticObject) :
    (deleteAccessible mover current).val
      = UnorderedTree.replace mover.val mover.headTrace.val current.val := rfl

/-- Apply a step: External Merge is the node with the item on the given side, Internal Merge the
    node of the remainder and the mover. -/
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

end Minimalist
