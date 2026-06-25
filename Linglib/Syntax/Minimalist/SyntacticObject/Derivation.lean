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

This is the *transformational* view (External/Internal Merge as tree operations), which
the paper-anchored study files are written in. **Index-free traces (D2):** Internal Merge
leaves the bare `SO.traceLeaf`; chain identity is **workspace-level** (`Workspace`,
`chainMultiplicity`, #795, MCB Def 1.2.1), not a per-step `Nat`. The canonical MCB
Internal Merge stays the workspace coproduct composition (`SO.intMerge`, #795); `Step.im`
is the derived transformational realization, built on `SO.replace` (#804) + `SO.node`.

Because `SO.node` is noncomputable, so are `Step.apply`/`Derivation.final` — concrete
trees are reasoned about structurally, not by `decide`. The **computable, `decide`-able
surface order** (externalization replay + the Π bridge, the Cinque-style word-order
readout) is the separate research-grade follow-up; it replays the linear choices on an
ordered planar accumulator, since `final` (a `Nonplanar` quotient) is unordered.
-/

namespace Minimalist

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

/-- Apply a derivation step to the current tree. External Merge adjoins `item`;
    Internal Merge extracts `mover` (replacing it by `SO.traceLeaf`, #804) and re-merges
    it. Since `SO.node` is commutative (the carrier is unordered), `emL` and `emR` give
    the *same* `SO` (`apply_emL_eq_emR`); the left/right distinction matters only for the
    surface (PF) order, recovered downstream by the externalization replay. -/
noncomputable def SO.Step.apply (step : SO.Step) (current : SO) : SO :=
  match step with
  | .emL item  => SO.node item current
  | .emR item  => SO.node current item
  | .im mover  => SO.node mover (current.replace mover SO.traceLeaf)

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
