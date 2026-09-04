/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Replace
import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# Derivations

An ordered derivation is an initial syntactic object with a sequence of Merge steps. External Merge
adds an item as the left or right daughter, and Internal Merge raises a mover: the step re-merges
the mover with the remainder `deleteAccessible mover current`, the current object with the mover's
occurrences replaced by the trace of the mover's head. Each step applies the carrier node, so the
derivation's Merge is the workspace Merge by construction, and the node being commutative, `emL` and
`emR` build the same object; the left-right distinction matters only for the surface order, which
`Linearization/Replay.lean` recovers on an ordered planar accumulator, since the final object is an
unordered quotient. Since `node` is noncomputable, so are `Step.apply` and `Derivation.final`, while
the movers are read off the steps.

## Main definitions

* `Minimalist.SyntacticObject.Step`, `Step.apply`, `deleteAccessible`
* `Minimalist.SyntacticObject.Derivation`, `Derivation.final`, `stageAt`, `movedItems`, `take`,
  `leftward`

## References

* [marcolli-chomsky-berwick-2025], §1.2 (Definition 1.2.6) and §1.4 (Lemma 1.4.1,
  Proposition 1.4.2)
-/

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

namespace SyntacticObject

/-! ### Steps -/

/-- A derivation step. `im` records only the mover; the trace it leaves is that of its head. -/
inductive Step where
  /-- External Merge, new item as the left daughter. -/
  | emL (item : SyntacticObject)
  /-- External Merge, new item as the right daughter. -/
  | emR (item : SyntacticObject)
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
  | .emL item  => merge item current
  | .emR item  => merge current item
  | .im mover  => merge (deleteAccessible mover current) mover

theorem Step.apply_emL (item current : SyntacticObject) :
    (Step.emL item).apply current = merge item current := rfl

theorem Step.apply_emR (item current : SyntacticObject) :
    (Step.emR item).apply current = merge current item := rfl

theorem Step.apply_im (mover current : SyntacticObject) :
    (Step.im mover).apply current = merge (deleteAccessible mover current) mover := rfl

/-- `emL` and `emR` build the same object; they differ only at externalization. -/
theorem Step.apply_emL_eq_emR (item current : SyntacticObject) :
    (Step.emL item).apply current = (Step.emR item).apply current :=
  mul_comm item current

/-- The step with its External Merge on the left; Internal Merge is unchanged. -/
def Step.leftward : Step → Step
  | .emR item => .emL item
  | step => step

@[simp] theorem Step.leftward_emL (item : SyntacticObject) : (Step.emL item).leftward = .emL item :=
  rfl

@[simp] theorem Step.leftward_emR (item : SyntacticObject) : (Step.emR item).leftward = .emL item :=
  rfl

@[simp] theorem Step.leftward_im (mover : SyntacticObject) : (Step.im mover).leftward = .im mover :=
  rfl

/-- A step and its leftward form build the same object. -/
theorem Step.apply_leftward (step : Step) (current : SyntacticObject) :
    step.leftward.apply current = step.apply current := by
  cases step with
  | emR item => exact Step.apply_emL_eq_emR item current
  | emL _ | im _ => rfl

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
def movedItems (d : Derivation) : List SyntacticObject :=
  d.steps.filterMap fun
    | .im mover => some mover
    | _ => none

/-- The first `n` steps. -/
def take (d : Derivation) (n : Nat) : Derivation := ⟨d.initial, d.steps.take n⟩

@[simp] theorem stageAt_zero (d : Derivation) : d.stageAt 0 = d.initial := by
  simp [stageAt]

theorem stageAt_length (d : Derivation) : d.stageAt d.steps.length = d.final := by
  simp [stageAt, final, List.take_length]

@[simp] theorem final_take (d : Derivation) (n : Nat) : (d.take n).final = d.stageAt n := rfl

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
  simp only [movedItems, leftward, List.filterMap_map]
  congr 1
  funext step
  cases step <;> rfl

end Derivation

end SyntacticObject

/-! ### Carrier tests -/

private def demoTok (i : Nat) : SyntacticObject := SyntacticObject.leaf ⟨.simple .N [], i⟩

example :
    (Derivation.mk (demoTok 0)
      [Step.emL (demoTok 1), Step.im (demoTok 1),
       Step.emR (demoTok 2), Step.im (demoTok 2)]).movedItems = [demoTok 1, demoTok 2] := by
  simp [Derivation.movedItems, demoTok]

example : (Derivation.mk (demoTok 0) [Step.emL (demoTok 1)]).length = 1 := rfl

end Minimalist
