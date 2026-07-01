/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Construction DSL and accessors for syntactic objects

[marcolli-chomsky-berwick-2025] §1.1. The computable construction layer and the
read-back accessors for the `SO` carrier, completing P2's API parity with the legacy
`FreeCommMagma (LIToken ⊕ Nat)` surface. Imports only the carrier skeleton.

## Construction discipline

The Merge operator (`SO.node`/`SO.merge`) is `noncomputable` (the smart
`Nonplanar.node` round-trips through `Quotient.out`). So concrete syntactic objects
— the ones studies `decide` over — are built **planar-first** and quotiented once:
`SO.ofPlanar (SO.nodeP (SO.leafP tok₁) (SO.leafP tok₂))`. `SO.node_mk` (skeleton)
relates such a build to `SO.node`, so theorems stated over `node`/`*` still apply.

## Index-free traces

A trace is a bare `Sum.inr ()` leaf with **no index** (MCB Def 1.2.1: chain identity
is workspace-level), so there is exactly **one** trace leaf — `SO.isTrace` is just
`· = SO.traceLeaf`.
-/

namespace Minimalist

open RootedTree

/-! ### Computable planar construction DSL -/

/-- Planar builder: a lexical leaf. -/
abbrev SO.leafP (tok : LIToken) : Tree SOLabel := .node (Sum.inl tok) []
/-- Planar builder: the bare trace leaf. -/
abbrev SO.traceP : Tree SOLabel := .node (Sum.inr ()) []
/-- Planar builder: a bare binary node. -/
abbrev SO.nodeP (l r : Tree SOLabel) : Tree SOLabel := .node (Sum.inr ()) [l, r]

/-- Build a syntactic object from a planar tree, discharging well-formedness by
    `decide` (concrete trees) — the computable entry point for `decide`-based studies. -/
def SO.ofPlanar (p : Tree SOLabel) (h : isSOPlanar p = true := by first | rfl | decide) : SO :=
  ⟨Nonplanar.mk p, h⟩

@[simp] theorem SO.ofPlanar_leafP (tok : LIToken) :
    SO.ofPlanar (SO.leafP tok) = SO.lexLeaf tok := rfl

@[simp] theorem SO.ofPlanar_traceP : SO.ofPlanar SO.traceP = SO.traceLeaf := rfl

/-- Default syntactic object: the bare trace leaf. Lets structures with an `SO`
    field be `Inhabited`/`deriving Repr`-free of bespoke witnesses. -/
instance : Inhabited SO := ⟨SO.traceLeaf⟩

/-! ### Merge as multiplication -/

/-- `*` is (External) Merge: the bare binary node. Noncomputable — build concrete
    trees with the planar DSL above, not `*`. -/
noncomputable instance : Mul SO := ⟨SO.node⟩

@[simp] theorem SO.mul_def (l r : SO) : l * r = SO.node l r := rfl

theorem SO.mul_comm (l r : SO) : l * r = r * l := by
  apply Subtype.ext
  rw [SO.mul_def, SO.mul_def, SO.node_val, SO.node_val, Multiset.pair_comm]

/-! ### The canonical Merge operators (carrier primitives)

`SO.merge` / `SO.intMerge` are the carrier-level Merge operators
([marcolli-chomsky-berwick-2025] Lemma 1.4.1 / Prop 1.4.2): they need only the bare
binary node, so they live here. Their **coproduct identity** on the workspace Hopf
algebra (`SO.merge_toForest` / `SO.intMerge_toForest`) lives in `Workspace.lean`, which
imports the Merge algebra; this file stays algebra-free so `decide`-based consumers
(e.g. the externalization replay in `SyntacticObject/Derivation.lean`) keep the
computable `DecidableEq (Nonplanar …)` (#792) in scope. -/

/-- **External Merge on the carrier** ([marcolli-chomsky-berwick-2025] Lemma 1.4.1): the
    bare binary node `SO.node` *is* External Merge (for distinct workspace items) and the
    re-merge stage of Internal Merge. Noncomputable; build concrete results with the
    planar DSL + `decide`. -/
noncomputable def SO.merge (S S' : SO) : SO := SO.node S S'

@[simp] theorem SO.merge_val (S S' : SO) :
    (SO.merge S S').val = Nonplanar.node (Sum.inr ()) {S.val, S'.val} := rfl

/-- **Internal Merge on the carrier** ([marcolli-chomsky-berwick-2025] Prop 1.4.2):
    re-Merge the `mover` with the **deletion remainder** `remainder = T/mover` (the
    `M_{T/β, β}` order: remainder left, mover right). IM is *not* a new structural
    primitive — it is `SO.merge` of the remainder and the mover. The mover ↔ trace
    correspondence (the chain) is read at the workspace level (`Workspace.chainMultiplicity`),
    not from an index. -/
noncomputable def SO.intMerge (mover remainder : SO) : SO := SO.merge remainder mover

@[simp] theorem SO.intMerge_val (mover remainder : SO) :
    (SO.intMerge mover remainder).val
      = Nonplanar.node (Sum.inr ()) {remainder.val, mover.val} := rfl

/-! ### Lexical-leaf construction (the legacy `mkLeaf` API) -/

/-- A lexical leaf from a category and selectional stack. -/
def SO.mkLeaf (cat : Cat) (sel : SelStack) (id : Nat) : SO :=
  SO.lexLeaf ⟨.simple cat sel, id⟩

/-- A lexical leaf with a phonological form. -/
def SO.mkLeafPhon (cat : Cat) (sel : SelStack) (phon : String) (id : Nat) : SO :=
  SO.lexLeaf ⟨.simple cat sel (phonForm := phon), id⟩

/-! ### Accessors -/

/-- The lexical token at the root, if the root is a lexical leaf. -/
def SO.getLIToken (s : SO) : Option LIToken :=
  match Nonplanar.rootValue s.val with
  | .inl tok => some tok
  | .inr () => none

@[simp] theorem SO.getLIToken_lexLeaf (tok : LIToken) :
    (SO.lexLeaf tok).getLIToken = some tok := rfl

@[simp] theorem SO.getLIToken_traceLeaf : SO.traceLeaf.getLIToken = none := rfl

@[simp] theorem SO.getLIToken_node (l r : SO) : (SO.node l r).getLIToken = none := by
  rw [SO.getLIToken, SO.node_val, Nonplanar.rootValue_node]

/-- A trace is the unique bare trace leaf (chain identity is workspace-level). -/
def SO.isTrace (s : SO) : Prop := s = SO.traceLeaf

instance (s : SO) : Decidable (SO.isTrace s) := inferInstanceAs (Decidable (_ = _))

@[simp] theorem SO.isTrace_traceLeaf : SO.isTrace SO.traceLeaf := rfl

/-- Leaf count (number of leaves + traces). -/
def SO.leafCount (s : SO) : Nat := Nonplanar.numLeaves s.val

/-- Is `s` a leaf (lexical or trace)? A leaf has a single vertex; a bare binary node
    has ≥ 2 leaves. -/
def SO.isLeaf (s : SO) : Bool := s.leafCount == 1

/-- Is `s` a (bare binary) internal node? The complement of `SO.isLeaf`. -/
def SO.isNode (s : SO) : Bool := !s.isLeaf

@[simp] theorem SO.isLeaf_lexLeaf (tok : LIToken) : (SO.lexLeaf tok).isLeaf = true := rfl
@[simp] theorem SO.isLeaf_traceLeaf : SO.traceLeaf.isLeaf = true := rfl
@[simp] theorem SO.isNode_lexLeaf (tok : LIToken) : (SO.lexLeaf tok).isNode = false := rfl

/-- A lightweight `Repr` so structures with an `SO` field can `deriving Repr`. The full
    tree is a `Nonplanar` quotient (no faithful structural readout without `Quot.out`);
    for debugging surface order use `SO.linearize`. -/
instance : Repr SO where
  reprPrec s _ := match s.getLIToken with
    | some tok => f!"SO.lexLeaf {repr tok}"
    | none => if s.isLeaf then f!"SO.traceLeaf" else f!"⟨SO node, {s.leafCount} leaves⟩"

/-- Internal-node count = leaf count − 1 (full binary tree). -/
def SO.nodeCount (s : SO) : Nat := Nonplanar.numLeaves s.val - 1

@[simp] theorem SO.leafCount_lexLeaf (tok : LIToken) : (SO.lexLeaf tok).leafCount = 1 := rfl
@[simp] theorem SO.leafCount_traceLeaf : SO.traceLeaf.leafCount = 1 := rfl

/-! ### `decide` demonstrations -/

private def demoVP : SO :=
  SO.ofPlanar (SO.nodeP (SO.leafP (mkTraceToken 0)) (SO.leafP (mkTraceToken 1)))

/-- The DSL-built tree is a genuine syntactic object. -/
example : IsSO demoVP.val := by decide
/-- Its head token reads back via `getLIToken` of the left leaf. -/
example : (SO.lexLeaf (mkTraceToken 0)).getLIToken = some (mkTraceToken 0) := by decide
/-- It has two leaves and one internal node. -/
example : demoVP.leafCount = 2 ∧ demoVP.nodeCount = 1 := by decide
/-- The trace leaf is recognized; a lexical leaf is not a trace. -/
example : SO.isTrace SO.traceLeaf ∧ ¬ SO.isTrace (SO.lexLeaf (mkTraceToken 0)) := by decide

end Minimalist
