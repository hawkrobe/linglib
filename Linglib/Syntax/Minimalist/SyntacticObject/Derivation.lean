/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Replace

/-!
# Derivation steps on the `SyntacticObject` carrier

P4-pre-b of the single-carrier program: the ordered **derivation** layer on the `SyntacticObject`
carrier — the sequence of Merge/Move operations producing a syntactic object — replacing
the legacy `FreeCommMagma`-based `Step`/`Derivation`.

**The derivation's Merge *is* the workspace Merge by construction.** Each step applies a
canonical MCB Merge operator (`Workspace.lean`): External Merge is `SyntacticObject.merge` (Lemma
1.4.1), Internal Merge is `SyntacticObject.intMerge` (Prop 1.4.2's `M_{T/β,β}`) on the deletion
remainder `SyntacticObject.deleteAccessible mover current` (= `T/mover`). So `Step.apply` *unfolds*
to the coproduct operators (`SyntacticObject.Step.apply_emL`/`apply_im`); the Δ^ρ-coproduct identity
is `SyntacticObject.merge_toForest`/`SyntacticObject.intMerge_toForest` — nothing is independently
stipulated then
bridged.

**Index-free traces (D2):** Internal Merge leaves the bare `SyntacticObject.traceLeaf`; chain
identity
is **workspace-level** (`Workspace`, `chainMultiplicity`, #795, MCB Def 1.2.1), not a
per-step `Nat`. The deletion remainder is realized by `SyntacticObject.replace` (#804): for a
uniquely-accessible mover this is exactly the Δ^ρ cut remainder `SyntacticObject.intMerge_toForest`
extracts, and `replace`-all is its total extension to the multi-occurrence (chain) case.

Because `SyntacticObject.node` is noncomputable, so are `Step.apply`/`Derivation.final` — concrete
trees are reasoned about structurally, not by `decide`. The **computable, `decide`-able
surface order** (externalization replay + the Π bridge, the Cinque-style word-order
readout) lives in `Linearization/Replay.lean`; it replays the linear choices on an
ordered planar accumulator, since `final` (a `Nonplanar` quotient) is unordered.
-/

namespace Minimalist

open RootedTree SyntacticObject

namespace SyntacticObject

/-! ### Steps -/

/-- A single derivation step on the `SyntacticObject` carrier. **Index-free** (D2): `im` records
    only the mover; the trace it leaves is the bare `SyntacticObject.traceLeaf`, and the mover ↔
    trace
    chain lives at the workspace level (#795), not in a per-step index. -/
inductive Step where
  /-- External Merge, new item as the left daughter. -/
  | emL (item : SyntacticObject)
  /-- External Merge, new item as the right daughter. -/
  | emR (item : SyntacticObject)
  /-- Internal Merge: raise `mover`, leaving the bare trace in its place. -/
  | im (mover : SyntacticObject)

/-- **Internal-Merge deletion remainder** `T/mover` ([marcolli-chomsky-berwick-2025]
    Def 1.2.7, the ρ-form): the syntactic object left when the moved constituent's
    accessible occurrence is cut, with the bare `SyntacticObject.traceLeaf` in its place. For a
    uniquely-accessible `mover` this is the Δ^ρ deletion remainder `p0.2` that
    `SyntacticObject.intMerge_toForest` extracts from `cutSummandsN`; `SyntacticObject.replace`
    (replace-all) is
    its total extension to the multi-occurrence case (the chain is then read at the
    workspace level, Def 1.2.1). -/
noncomputable def deleteAccessible (mover current : SyntacticObject) : SyntacticObject :=
  current.replace mover traceLeaf

@[simp] theorem deleteAccessible_val (mover current : SyntacticObject) :
    (deleteAccessible mover current).val = replaceN mover.val traceLeaf.val current.val := rfl

/-- Apply a derivation step to the current tree. **The derivation Merge *is* the
    workspace Merge by construction:** External Merge is `SyntacticObject.merge` (Lemma 1.4.1),
    Internal Merge is `SyntacticObject.intMerge` (Prop 1.4.2's `M_{T/β,β}`) applied to the deletion
    remainder `SyntacticObject.deleteAccessible mover current` (= `T/mover`). The coproduct identity
    of each is `SyntacticObject.merge_toForest`/`SyntacticObject.intMerge_toForest`. Since
    `SyntacticObject.merge` is commutative
    (`SyntacticObject.mul_comm`), `emL`/`emR` and the mover-left/remainder-left orders give the
    *same*
    `SyntacticObject` (`apply_emL_eq_emR`); the left/right distinction matters only for the surface
    (PF) order, recovered downstream by the externalization replay. -/
noncomputable def Step.apply (step : Step) (current : SyntacticObject) : SyntacticObject :=
  match step with
  | .emL item  => merge item current
  | .emR item  => merge current item
  | .im mover  => intMerge mover (deleteAccessible mover current)

/-- External Merge unfolds to the canonical workspace EM `SyntacticObject.merge` (Lemma 1.4.1). -/
theorem Step.apply_emL (item current : SyntacticObject) :
    (Step.emL item).apply current = merge item current := rfl

/-- External Merge unfolds to the canonical workspace EM `SyntacticObject.merge` (Lemma 1.4.1). -/
theorem Step.apply_emR (item current : SyntacticObject) :
    (Step.emR item).apply current = merge current item := rfl

/-- **Internal Merge unfolds to the coproduct operator by construction.** The `im` step
    *is* the canonical workspace IM `SyntacticObject.intMerge` (MCB Prop 1.4.2) on the deletion
    remainder — definitionally, not via a bridge. Composing with `SyntacticObject.intMerge_toForest`
    gives the Δ^ρ-coproduct identity on the workspace. -/
theorem Step.apply_im (mover current : SyntacticObject) :
    (Step.im mover).apply current = intMerge mover (deleteAccessible mover current) := rfl

/-- External Merge is side-indifferent on the unordered carrier: `emL` and `emR` build
    the same syntactic object (they diverge only at externalization). -/
theorem Step.apply_emL_eq_emR (item current : SyntacticObject) :
    (Step.emL item).apply current = (Step.emR item).apply current :=
  mul_comm item current

/-! ### Derivations -/

/-- An ordered derivation: an initial `SyntacticObject` together with a sequence of steps. -/
structure Derivation where
  /-- The initial syntactic object (a lexical item, in canonical derivations). -/
  initial : SyntacticObject
  /-- The ordered sequence of Merge/Move steps. -/
  steps : List Step

namespace Derivation

/-- The final tree produced by applying every step in order. -/
noncomputable def final (d : Derivation) : SyntacticObject :=
  d.steps.foldl (fun so step => step.apply so) d.initial

/-- The intermediate tree after the first `n` steps. -/
noncomputable def stageAt (d : Derivation) (n : Nat) : SyntacticObject :=
  (d.steps.take n).foldl (fun so step => step.apply so) d.initial

/-- The number of derivation steps. -/
def length (d : Derivation) : Nat := d.steps.length

/-- The movers — the subtrees that underwent Internal Merge. -/
def movedItems (d : Derivation) : List SyntacticObject :=
  d.steps.filterMap fun
    | .im mover => some mover
    | _ => none

/-- Stage `0` is the initial tree (no steps applied). -/
@[simp] theorem stageAt_zero (d : Derivation) : d.stageAt 0 = d.initial := by
  simp [stageAt]

/-- The stage at full length is the final tree. -/
theorem stageAt_length (d : Derivation) : d.stageAt d.steps.length = d.final := by
  simp [stageAt, final, List.take_length]

end Derivation

end SyntacticObject

/-! ### Worked example

The movers of a small derivation are read directly off the steps (a `filterMap`, so
this is `decide`-able even though `final` is not): a derivation that internally merges
two objects records exactly those two as moved. -/

private def demoTok (i : Nat) : SyntacticObject := lexLeaf ⟨.simple .N [], i⟩

example :
    (Derivation.mk (demoTok 0)
      [Step.emL (demoTok 1), Step.im (demoTok 1),
       Step.emR (demoTok 2), Step.im (demoTok 2)]).movedItems = [demoTok 1, demoTok 2] := by
  simp [Derivation.movedItems, demoTok]

example : (Derivation.mk (demoTok 0) [Step.emL (demoTok 1)]).length = 1 := rfl

end Minimalist
