/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Construction DSL and accessors for syntactic objects

[marcolli-chomsky-berwick-2025] §1.1. The computable construction layer and the
read-back accessors for the `SyntacticObject` carrier, completing P2's API parity with the legacy
`FreeCommMagma (LIToken ⊕ Nat)` surface. Imports only the carrier skeleton.

## Construction discipline

The Merge operator (`SyntacticObject.node`/`SyntacticObject.merge`) is `noncomputable` (the smart
`Nonplanar.node` round-trips through `Quotient.out`). So concrete syntactic objects
— the ones studies `decide` over — are built **planar-first** and quotiented once:
`SyntacticObject.ofPlanar (SyntacticObject.nodeP (SyntacticObject.leafP tok₁) (SyntacticObject.leafP
tok₂))`. `SyntacticObject.node_mk` (skeleton)
relates such a build to `SyntacticObject.node`, so theorems stated over `node`/`*` still apply.

## Index-free traces

A trace is a bare `Sum.inr ()` leaf with **no index** (MCB Def 1.2.1: chain identity
is workspace-level), so there is exactly **one** trace leaf — `SyntacticObject.isTrace` is just
`· = SyntacticObject.traceLeaf`.
-/

namespace Minimalist

open RootedTree SyntacticObject

namespace SyntacticObject

/-! ### Computable planar construction DSL -/

/-- Planar builder: a lexical leaf. -/
abbrev leafP (tok : LIToken) : RoseTree SOLabel := .node (Sum.inl tok) []
/-- Planar builder: the bare trace leaf. -/
abbrev traceP : RoseTree SOLabel := .node (Sum.inr ()) []
/-- Planar builder: a bare binary node. -/
abbrev nodeP (l r : RoseTree SOLabel) : RoseTree SOLabel := .node (Sum.inr ()) [l, r]

/-- Build a syntactic object from a planar tree, discharging well-formedness by
    `decide` (concrete trees) — the computable entry point for `decide`-based studies. -/
def ofPlanar (p : RoseTree SOLabel) (h : isSOPlanar p = true :=
  by first | rfl | decide) : SyntacticObject :=
  ⟨Nonplanar.mk p, h⟩

@[simp] theorem ofPlanar_leafP (tok : LIToken) : ofPlanar (leafP tok) = lexLeaf tok := rfl

@[simp] theorem ofPlanar_traceP : ofPlanar traceP = traceLeaf := rfl

/-- Default syntactic object: the bare trace leaf. Lets structures with an `SyntacticObject`
    field be `Inhabited`/`deriving Repr`-free of bespoke witnesses. -/
instance : Inhabited SyntacticObject := ⟨traceLeaf⟩

/-! ### Merge as multiplication -/

/-- `*` is (External) Merge: the bare binary node. Noncomputable — build concrete
    trees with the planar DSL above, not `*`. -/
noncomputable instance : Mul SyntacticObject := ⟨node⟩

@[simp] theorem mul_def (l r : SyntacticObject) : l * r = node l r := rfl

theorem mul_comm (l r : SyntacticObject) : l * r = r * l := by
  apply Subtype.ext
  rw [mul_def, mul_def, node_val, node_val, Multiset.pair_comm]

/-! ### The canonical Merge operators (carrier primitives)

`SyntacticObject.merge` / `SyntacticObject.intMerge` are the carrier-level Merge operators
([marcolli-chomsky-berwick-2025] Lemma 1.4.1 / Prop 1.4.2): they need only the bare
binary node, so they live here. Their **coproduct identity** on the workspace Hopf
algebra (`SyntacticObject.merge_toForest` / `SyntacticObject.intMerge_toForest`) lives in
`Workspace.lean`, which
imports the Merge algebra; this file stays algebra-free so `decide`-based consumers
(e.g. the externalization replay in `SyntacticObject/Derivation.lean`) keep the
computable `DecidableEq (Nonplanar …)` (#792) in scope. -/

/-- **External Merge on the carrier** ([marcolli-chomsky-berwick-2025] Lemma 1.4.1): the
    bare binary node `SyntacticObject.node` *is* External Merge (for distinct workspace items) and
    the
    re-merge stage of Internal Merge. Noncomputable; build concrete results with the
    planar DSL + `decide`. -/
noncomputable def merge (S S' : SyntacticObject) : SyntacticObject := node S S'

@[simp] theorem merge_val (S S' : SyntacticObject) :
    (merge S S').val = Nonplanar.node (Sum.inr ()) {S.val, S'.val} := rfl

/-- **Internal Merge on the carrier** ([marcolli-chomsky-berwick-2025] Prop 1.4.2):
    re-Merge the `mover` with the **deletion remainder** `remainder = T/mover` (the
    `M_{T/β, β}` order: remainder left, mover right). IM is *not* a new structural
    primitive — it is `SyntacticObject.merge` of the remainder and the mover. The mover ↔ trace
    correspondence (the chain) is read at the workspace level (`Workspace.chainMultiplicity`),
    not from an index. -/
noncomputable def intMerge (mover remainder : SyntacticObject) : SyntacticObject :=
  merge remainder mover

@[simp] theorem intMerge_val (mover remainder : SyntacticObject) :
    (intMerge mover remainder).val = Nonplanar.node (Sum.inr ()) {remainder.val, mover.val} := rfl

/-! ### Lexical-leaf construction (the legacy `mkLeaf` API) -/

/-- A lexical leaf from a category and selectional stack. -/
def mkLeaf (cat : Cat) (sel : SelStack) (id : Nat) : SyntacticObject :=
  lexLeaf ⟨.simple cat sel, id⟩

/-- A lexical leaf with a phonological form. -/
def mkLeafPhon (cat : Cat) (sel : SelStack) (phon : String) (id : Nat) : SyntacticObject :=
  lexLeaf ⟨.simple cat sel (phonForm := phon), id⟩

/-! ### Accessors -/

/-- The lexical token at the root, if the root is a lexical leaf. -/
def getLIToken (s : SyntacticObject) : Option LIToken :=
  match Nonplanar.rootValue s.val with
  | .inl tok => some tok
  | .inr () => none

@[simp] theorem getLIToken_lexLeaf (tok : LIToken) : (lexLeaf tok).getLIToken = some tok := rfl

@[simp] theorem getLIToken_traceLeaf : traceLeaf.getLIToken = none := rfl

@[simp] theorem getLIToken_node (l r : SyntacticObject) : (node l r).getLIToken = none := by
  rw [getLIToken, node_val, Nonplanar.rootValue_node]

/-- A trace is the unique bare trace leaf (chain identity is workspace-level). -/
def isTrace (s : SyntacticObject) : Prop := s = traceLeaf

instance (s : SyntacticObject) : Decidable (isTrace s) :=
  inferInstanceAs (Decidable (_ = _))

@[simp] theorem isTrace_traceLeaf : isTrace traceLeaf := rfl

/-- Leaf count (number of leaves + traces). -/
def leafCount (s : SyntacticObject) : Nat := Nonplanar.numLeaves s.val

/-- Is `s` a leaf (lexical or trace)? A leaf has a single vertex; a bare binary node
    has ≥ 2 leaves. -/
def isLeaf (s : SyntacticObject) : Bool := s.leafCount == 1

/-- Is `s` a (bare binary) internal node? The complement of `SyntacticObject.isLeaf`. -/
def isNode (s : SyntacticObject) : Bool := !s.isLeaf

@[simp] theorem isLeaf_lexLeaf (tok : LIToken) : (lexLeaf tok).isLeaf = true := rfl
@[simp] theorem isLeaf_traceLeaf : traceLeaf.isLeaf = true := rfl
@[simp] theorem isNode_lexLeaf (tok : LIToken) : (lexLeaf tok).isNode = false := rfl

/-- A lightweight `Repr` so structures with an `SyntacticObject` field can `deriving Repr`. The full
    tree is a `Nonplanar` quotient (no faithful structural readout without `Quot.out`);
    for debugging surface order use `SyntacticObject.linearize`. -/
instance : Repr SyntacticObject where
  reprPrec s _ := match s.getLIToken with
    | some tok => f!"SyntacticObject.lexLeaf {repr tok}"
    | none =>
      if s.isLeaf then f!"SyntacticObject.traceLeaf"
      else f!"⟨SyntacticObject node, {s.leafCount} leaves⟩"

/-- Internal-node count = leaf count − 1 (full binary tree). -/
def nodeCount (s : SyntacticObject) : Nat := Nonplanar.numLeaves s.val - 1

@[simp] theorem leafCount_lexLeaf (tok : LIToken) : (lexLeaf tok).leafCount = 1 := rfl
@[simp] theorem leafCount_traceLeaf : traceLeaf.leafCount = 1 := rfl

end SyntacticObject

/-! ### `decide` demonstrations -/

private def demoVP : SyntacticObject :=
  ofPlanar (nodeP (leafP (mkTraceToken 0)) (leafP (mkTraceToken 1)))

/-- The DSL-built tree is a genuine syntactic object. -/
example : IsSO demoVP.val := by decide
/-- Its head token reads back via `getLIToken` of the left leaf. -/
example : (lexLeaf (mkTraceToken 0)).getLIToken = some (mkTraceToken 0) := by decide
/-- It has two leaves and one internal node. -/
example : demoVP.leafCount = 2 ∧ demoVP.nodeCount = 1 := by decide
/-- The trace leaf is recognized; a lexical leaf is not a trace. -/
example : isTrace traceLeaf ∧ ¬ isTrace (lexLeaf (mkTraceToken 0)) := by decide

end Minimalist
