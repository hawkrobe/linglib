/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Replace

/-!
# Derivation steps on the `SO` carrier

P4-pre-b of the single-carrier program: the ordered **derivation** layer on the `SO`
carrier — the sequence of Merge/Move operations producing a syntactic object — replacing
the legacy `FreeCommMagma`-based `Step`/`Derivation`.

**The derivation's Merge *is* the workspace Merge by construction.** Each step applies a
canonical MCB Merge operator (`Workspace.lean`): External Merge is `SO.merge` (Lemma
1.4.1), Internal Merge is `SO.intMerge` (Prop 1.4.2's `M_{T/β,β}`) on the deletion
remainder `SO.deleteAccessible mover current` (= `T/mover`). So `Step.apply` *unfolds*
to the coproduct operators (`SO.Step.apply_emL`/`apply_im`); the Δ^ρ-coproduct identity
is `SO.merge_toForest`/`SO.intMerge_toForest` — nothing is independently stipulated then
bridged.

**Index-free traces (D2):** Internal Merge leaves the bare `SO.traceLeaf`; chain identity
is **workspace-level** (`Workspace`, `chainMultiplicity`, #795, MCB Def 1.2.1), not a
per-step `Nat`. The deletion remainder is realized by `SO.replace` (#804): for a
uniquely-accessible mover this is exactly the Δ^ρ cut remainder `SO.intMerge_toForest`
extracts, and `replace`-all is its total extension to the multi-occurrence (chain) case.

Because `SO.node` is noncomputable, so are `Step.apply`/`Derivation.final` — concrete
trees are reasoned about structurally, not by `decide`. The **computable, `decide`-able
surface order** (externalization replay + the Π bridge, the Cinque-style word-order
readout) lives in `Linearization/Replay.lean`; it replays the linear choices on an
ordered planar accumulator, since `final` (a `Nonplanar` quotient) is unordered.
-/

namespace Minimalist

open RootedTree

/-! ### Steps -/

/-- A single derivation step on the `SO` carrier. **Index-free** (D2): `im` records
    only the mover; the trace it leaves is the bare `SO.traceLeaf`, and the mover ↔ trace
    chain lives at the workspace level (#795), not in a per-step index. -/
inductive SO.Step where
  /-- External Merge, new item as the left daughter. -/
  | emL (item : SO)
  /-- External Merge, new item as the right daughter. -/
  | emR (item : SO)
  /-- Internal Merge: raise `mover`, leaving the bare trace in its place. -/
  | im (mover : SO)

/-- **Internal-Merge deletion remainder** `T/mover` ([marcolli-chomsky-berwick-2025]
    Def 1.2.7, the ρ-form): the syntactic object left when the moved constituent's
    accessible occurrence is cut, with the bare `SO.traceLeaf` in its place. For a
    uniquely-accessible `mover` this is the Δ^ρ deletion remainder `p0.2` that
    `SO.intMerge_toForest` extracts from `cutSummandsN`; `SO.replace` (replace-all) is
    its total extension to the multi-occurrence case (the chain is then read at the
    workspace level, Def 1.2.1). -/
noncomputable def SO.deleteAccessible (mover current : SO) : SO :=
  current.replace mover SO.traceLeaf

@[simp] theorem SO.deleteAccessible_val (mover current : SO) :
    (SO.deleteAccessible mover current).val
      = replaceN mover.val SO.traceLeaf.val current.val := rfl

/-- Apply a derivation step to the current tree. **The derivation Merge *is* the
    workspace Merge by construction:** External Merge is `SO.merge` (Lemma 1.4.1),
    Internal Merge is `SO.intMerge` (Prop 1.4.2's `M_{T/β,β}`) applied to the deletion
    remainder `SO.deleteAccessible mover current` (= `T/mover`). The coproduct identity
    of each is `SO.merge_toForest`/`SO.intMerge_toForest`. Since `SO.merge` is commutative
    (`SO.mul_comm`), `emL`/`emR` and the mover-left/remainder-left orders give the *same*
    `SO` (`apply_emL_eq_emR`); the left/right distinction matters only for the surface
    (PF) order, recovered downstream by the externalization replay. -/
noncomputable def SO.Step.apply (step : SO.Step) (current : SO) : SO :=
  match step with
  | .emL item  => SO.merge item current
  | .emR item  => SO.merge current item
  | .im mover  => SO.intMerge mover (SO.deleteAccessible mover current)

/-- External Merge unfolds to the canonical workspace EM `SO.merge` (Lemma 1.4.1). -/
theorem SO.Step.apply_emL (item current : SO) :
    (SO.Step.emL item).apply current = SO.merge item current := rfl

/-- External Merge unfolds to the canonical workspace EM `SO.merge` (Lemma 1.4.1). -/
theorem SO.Step.apply_emR (item current : SO) :
    (SO.Step.emR item).apply current = SO.merge current item := rfl

/-- **Internal Merge unfolds to the coproduct operator by construction.** The `im` step
    *is* the canonical workspace IM `SO.intMerge` (MCB Prop 1.4.2) on the deletion
    remainder — definitionally, not via a bridge. Composing with `SO.intMerge_toForest`
    gives the Δ^ρ-coproduct identity on the workspace. -/
theorem SO.Step.apply_im (mover current : SO) :
    (SO.Step.im mover).apply current = SO.intMerge mover (SO.deleteAccessible mover current) :=
  rfl

/-- External Merge is side-indifferent on the unordered carrier: `emL` and `emR` build
    the same syntactic object (they diverge only at externalization). -/
theorem SO.Step.apply_emL_eq_emR (item current : SO) :
    (SO.Step.emL item).apply current = (SO.Step.emR item).apply current :=
  mul_comm item current

/-! ### Derivations -/

/-- An ordered derivation: an initial `SO` together with a sequence of steps. -/
structure SO.Derivation where
  /-- The initial syntactic object (a lexical item, in canonical derivations). -/
  initial : SO
  /-- The ordered sequence of Merge/Move steps. -/
  steps : List SO.Step

namespace SO.Derivation

/-- The final tree produced by applying every step in order. -/
noncomputable def final (d : SO.Derivation) : SO :=
  d.steps.foldl (fun so step => step.apply so) d.initial

/-- The intermediate tree after the first `n` steps. -/
noncomputable def stageAt (d : SO.Derivation) (n : Nat) : SO :=
  (d.steps.take n).foldl (fun so step => step.apply so) d.initial

/-- The number of derivation steps. -/
def length (d : SO.Derivation) : Nat := d.steps.length

/-- The movers — the subtrees that underwent Internal Merge. -/
def movedItems (d : SO.Derivation) : List SO :=
  d.steps.filterMap fun
    | .im mover => some mover
    | _ => none

/-- Stage `0` is the initial tree (no steps applied). -/
@[simp] theorem stageAt_zero (d : SO.Derivation) : d.stageAt 0 = d.initial := by
  simp [stageAt]

/-- The stage at full length is the final tree. -/
theorem stageAt_length (d : SO.Derivation) : d.stageAt d.steps.length = d.final := by
  simp [stageAt, final, List.take_length]

end SO.Derivation

/-! ### Worked example

The movers of a small derivation are read directly off the steps (a `filterMap`, so
this is `decide`-able even though `final` is not): a derivation that internally merges
two objects records exactly those two as moved. -/

private def demoTok (i : Nat) : SO := SO.lexLeaf ⟨.simple .N [], i⟩

example :
    (SO.Derivation.mk (demoTok 0)
      [SO.Step.emL (demoTok 1), SO.Step.im (demoTok 1), SO.Step.emR (demoTok 2),
       SO.Step.im (demoTok 2)]).movedItems
      = [demoTok 1, demoTok 2] := by
  simp [SO.Derivation.movedItems, demoTok]

example :
    (SO.Derivation.mk (demoTok 0) [SO.Step.emL (demoTok 1)]).length = 1 := rfl

end Minimalist
