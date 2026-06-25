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

/-! ## Derivation-grounded externalization (computable PF order)

[marcolli-chomsky-berwick-2025] §1.12. `final` is an unordered `Nonplanar` quotient, so
the surface left-to-right order is not recoverable from it. But a `Derivation` *records*
the planarization choices: `emL`/`im` place material on the LEFT edge, `emR` on the
right — exactly MCB's externalization section `σ_L`, here fixed by the derivation ("the
language `L`") rather than a noncanonical `Quot.out`. The fold below replays the steps on
an **ordered `Planar SOLabel` accumulator**, giving a fully **computable** PF: it never
calls the noncomputable `SO.node`/`SO.replace` (it uses planar tree surgery + a
`Nonplanar.mk` equality test), so surface orders `decide`. Index-free traces are sound
here: traces are unpronounced, dropped by `planarYield`.

The formal Π-bridge faithfulness theorem (`Nonplanar.mk externalizeP? = final`) is a
planned follow-up; the `decide` demos below validate the replay reproduces the attested
orders. -/

/-- Planar form of a leaf/trace `SO` (the only items merged in canonical derivations);
    `none` for a complex `SO` (no recorded internal order). -/
def SO.toPlanarLeaf? (s : SO) : Option (Planar SOLabel) :=
  match s.getLIToken with
  | some tok => some (SO.leafP tok)
  | none     => if s = SO.traceLeaf then some SO.traceP else none

/-- Plain left-to-right token yield of an *already-ordered* planar tree; traces
    (`Sum.inr ()`) are unpronounced and contribute nothing. -/
def planarYield : Planar SOLabel → List LIToken
  | .node (.inl tok) _   => [tok]
  | .node (.inr ()) []   => []
  | .node (.inr ()) [l, r] => planarYield l ++ planarYield r
  | .node (.inr ()) _    => []

/-- "Projects to `target`": a planar subtree whose nonplanar projection is the `SO`
    `target` — the predicate the `im` replay uses to locate a mover. Computable
    (`DecidableEq (Nonplanar …)`), so it `decide`s. -/
def projEqP (target : SO) (s : Planar SOLabel) : Bool := decide (Nonplanar.mk s = target.val)

/-- Leftmost (root-first) subtree satisfying `p`. -/
def planarFindP? (p : Planar SOLabel → Bool) : Planar SOLabel → Option (Planar SOLabel)
  | t@(.node _ [])     => if p t then some t else none
  | t@(.node _ [l, r]) => if p t then some t else (planarFindP? p l).or (planarFindP? p r)
  | t@(.node _ _)      => if p t then some t else none

/-- Replace every subtree satisfying `p` by `rep`. -/
def planarReplaceWhereP (p : Planar SOLabel → Bool) (rep : Planar SOLabel) :
    Planar SOLabel → Planar SOLabel
  | t@(.node _ [])     => if p t then rep else t
  | t@(.node a [l, r]) =>
      if p t then rep
      else .node a [planarReplaceWhereP p rep l, planarReplaceWhereP p rep r]
  | t@(.node _ _)      => if p t then rep else t

/-- Internal Merge on the ordered accumulator: raise the leftmost subtree projecting to
    `mover` to the LEFT edge, leaving the bare trace `SO.traceP`. `none` if absent. -/
def moveLeftPlanarP (acc : Planar SOLabel) (mover : SO) : Option (Planar SOLabel) :=
  (planarFindP? (projEqP mover) acc).map fun s =>
    SO.nodeP s (planarReplaceWhereP (projEqP mover) SO.traceP acc)

/-- One externalization step on the ordered accumulator (mirrors `SO.Step.apply`). -/
def externStepP (acc? : Option (Planar SOLabel)) (step : SO.Step) : Option (Planar SOLabel) :=
  acc?.bind fun acc => match step with
    | .emL item  => item.toPlanarLeaf?.map (fun p => SO.nodeP p acc)
    | .emR item  => item.toPlanarLeaf?.map (fun p => SO.nodeP acc p)
    | .im mover  => moveLeftPlanarP acc mover

namespace SO.Derivation

/-- The derivation's ordered planar representative (MCB `σ_L` for this derivation),
    or `none` if a merged item is complex / a mover is missing. -/
def externalizeP? (d : SO.Derivation) : Option (Planar SOLabel) :=
  d.initial.toPlanarLeaf?.bind fun init => d.steps.foldl externStepP (some init)

/-- Surface (pronounced) tokens, left-to-right; traces dropped. Empty if
    externalization fails. -/
def surfaceTokens (d : SO.Derivation) : List LIToken :=
  (d.externalizeP?.map planarYield).getD []

/-- Surface category sequence — the readout used by word-order studies. -/
def surfaceCats (d : SO.Derivation) : List Cat := d.surfaceTokens.map (·.item.outerCat)

/-- Surface phonological string: pronounced forms left-to-right (empty forms dropped). -/
def surfacePhon (d : SO.Derivation) : List String :=
  d.surfaceTokens.filterMap fun t => let p := t.phonForm; if p.isEmpty then none else some p

end SO.Derivation

/-! ### Verification: the [cinque-2005] pied-piping contrast

Phrasal pied-piping preserves the moved constituent's internal order, so deriving
Dem-N-A-Num (raise N around A, then pied-pipe `[N A]` around Num) is distinct from
Dem-A-N-Num (pied-pipe `[A N]` around Num). Movers are built with the computable DSL so
the surface orders `decide`. (`.D` stands in for the demonstrative.) -/

private def xN : SO := SO.mkLeaf .N [] 1
private def xA : SO := SO.mkLeaf .A [] 2
private def xNum : SO := SO.mkLeaf .Num [] 3
private def xD : SO := SO.mkLeaf .D [] 4
/-- The pied-piped `[N [A t]]` mover (built planar-first, so it is computable). -/
private def xNAt : SO :=
  SO.ofPlanar (SO.nodeP (SO.leafP ⟨.simple .N [], 1⟩)
    (SO.nodeP (SO.leafP ⟨.simple .A [], 2⟩) SO.traceP))
/-- The pied-piped `[A N]` mover. -/
private def xAN : SO :=
  SO.ofPlanar (SO.nodeP (SO.leafP ⟨.simple .A [], 2⟩) (SO.leafP ⟨.simple .N [], 1⟩))

/-- No movement: `Dem Num A N`. -/
private def xDerivBase : SO.Derivation :=
  ⟨xN, [.emL xA, .emL xNum, .emL xD]⟩
/-- Raise N around A, pied-pipe `[N A]` around Num: `Dem N A Num`. -/
private def xDerivO : SO.Derivation :=
  ⟨xN, [.emL xA, .im xN, .emL xNum, .im xNAt, .emL xD]⟩
/-- Pied-pipe `[A N]` around Num, no sub-raise: `Dem A N Num`. -/
private def xDerivN : SO.Derivation :=
  ⟨xN, [.emL xA, .emL xNum, .im xAN, .emL xD]⟩

example : xDerivBase.surfaceCats = [.D, .Num, .A, .N] := by decide
example : xDerivO.surfaceCats = [.D, .N, .A, .Num] := by decide
example : xDerivN.surfaceCats = [.D, .A, .N, .Num] := by decide
/-- Pied-piping preserves internal order: `o` and `n` diverge. -/
example : xDerivO.surfaceCats ≠ xDerivN.surfaceCats := by decide

end Minimalist
