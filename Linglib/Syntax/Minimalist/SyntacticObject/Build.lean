/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Building and reading syntactic objects

The node constructor is noncomputable, so concrete syntactic objects are built planar-first with
`Planar.leaf`, `Planar.trace`, and `Planar.merge` and quotiented once by `ofPlanar`, whose
well-formedness obligation is discharged by `decide`; `SyntacticObject.node_mk` relates such a build
to `node`, so theorems stated over `node` apply to it. Merge on the carrier is the node itself,
written `*`: External Merge of two objects, and the re-merge of a mover with the remainder in
Internal Merge. The accessors read the root token, leaf and node counts, and the trace predicate;
since `isTrace` recognizes the trace leaves, bare or indexed.

## Main definitions

* `Minimalist.SyntacticObject.ofPlanar`, `Planar.leaf`, `Planar.trace`, `Planar.merge`: planar
construction.
* `Minimalist.SyntacticObject.mkLeaf`, `mkLeafPhon`: lexical leaves from features.
* `Minimalist.SyntacticObject.getLIToken`, `isTrace`, `leafCount`, `nodeCount`, `IsLeaf`.
-/

namespace Minimalist

open RoseTree RoseTree.Nonplanar SyntacticObject

namespace SyntacticObject

/-! ### Computable planar construction DSL -/

/-- The syntactic object of a well-formed planar tree; on a concrete tree the obligation is
    discharged by `decide`. -/
def ofPlanar (p : Planar) (h : Planar.isSyntacticObject p = true :=
  by first | rfl | decide) : SyntacticObject :=
  ⟨Nonplanar.mk p, h⟩

@[simp] theorem ofPlanar_leafP (tok : LIToken) : ofPlanar (Planar.leaf tok) = lexLeaf tok := rfl

@[simp] theorem ofPlanar_traceP : ofPlanar Planar.trace = traceLeaf := rfl

/-- The default syntactic object is the trace leaf. -/
instance : Inhabited SyntacticObject := ⟨traceLeaf⟩

/-! ### Merge as multiplication -/

/-- `l * r = node l r`: Merge on the carrier. -/
noncomputable instance : Mul SyntacticObject := ⟨node⟩

@[simp] theorem mul_def (l r : SyntacticObject) : l * r = node l r := rfl

theorem mul_comm (l r : SyntacticObject) : l * r = r * l := by
  apply Subtype.ext
  rw [mul_def, mul_def, node_val, node_val, Multiset.pair_comm]

/-! ### Lexical leaves from features -/

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
  | .inr _ => none

@[simp] theorem getLIToken_lexLeaf (tok : LIToken) : (lexLeaf tok).getLIToken = some tok := rfl

@[simp] theorem getLIToken_traceLeaf : traceLeaf.getLIToken = none := rfl

@[simp] theorem getLIToken_traceOf (tok : LIToken) : (traceOf tok).getLIToken = none := rfl

theorem traceOf_ne_traceLeaf (tok : LIToken) : traceOf tok ≠ traceLeaf := by
  intro h
  have h' : (Sum.inr (some tok) : Vertex) = Sum.inr none :=
    congrArg (fun s : SyntacticObject => Nonplanar.rootValue s.val) h
  simp at h'

@[simp] theorem getLIToken_node (l r : SyntacticObject) : (node l r).getLIToken = none := by
  rw [getLIToken, node_val, Nonplanar.rootValue_node]

/-- A trace leaf, bare or indexed. -/
def isTrace (s : SyntacticObject) : Prop :=
  (Nonplanar.rootValue s.val).isRight = true ∧ Nonplanar.numNodes s.val = 1

instance (s : SyntacticObject) : Decidable (isTrace s) := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem isTrace_traceOf (tok : LIToken) : isTrace (traceOf tok) := ⟨rfl, rfl⟩

@[simp] theorem not_isTrace_lexLeaf (tok : LIToken) : ¬ isTrace (lexLeaf tok) := fun h =>
  Bool.false_ne_true h.1

@[simp] theorem isTrace_traceLeaf : isTrace traceLeaf := ⟨rfl, rfl⟩

/-- The number of leaves, traces included. -/
def leafCount (s : SyntacticObject) : Nat := Nonplanar.numLeaves s.val

/-- `IsLeaf s ↔ s.leafCount = 1`: a lexical or trace leaf. -/
def IsLeaf (s : SyntacticObject) : Prop := s.leafCount = 1

instance : DecidablePred IsLeaf := fun _ => inferInstanceAs (Decidable (_ = _))

@[simp] theorem isLeaf_lexLeaf (tok : LIToken) : IsLeaf (lexLeaf tok) := rfl
@[simp] theorem isLeaf_traceLeaf : IsLeaf traceLeaf := rfl

/-- A shape summary; the full tree is a quotient with no faithful readout. -/
instance : Repr SyntacticObject where
  reprPrec s _ := match s.getLIToken with
    | some tok => f!"SyntacticObject.lexLeaf {repr tok}"
    | none =>
      if s.IsLeaf then f!"SyntacticObject.traceLeaf"
      else f!"⟨SyntacticObject node, {s.leafCount} leaves⟩"

/-- `nodeCount s = leafCount s - 1`, the number of internal vertices of a full binary tree. -/
def nodeCount (s : SyntacticObject) : Nat := Nonplanar.numLeaves s.val - 1

@[simp] theorem leafCount_lexLeaf (tok : LIToken) : (lexLeaf tok).leafCount = 1 := rfl
@[simp] theorem leafCount_traceLeaf : traceLeaf.leafCount = 1 := rfl

end SyntacticObject

/-! ### Carrier tests -/

private def demoVP : SyntacticObject :=
  ofPlanar (Planar.merge (Planar.leaf (mkTraceToken 0)) (Planar.leaf (mkTraceToken 1)))

/-- The DSL-built tree is a genuine syntactic object. -/
example : IsSyntacticObject demoVP.val := by decide
/-- Its head token reads back via `getLIToken` of the left leaf. -/
example : (lexLeaf (mkTraceToken 0)).getLIToken = some (mkTraceToken 0) := by decide
/-- It has two leaves and one internal node. -/
example : demoVP.leafCount = 2 ∧ demoVP.nodeCount = 1 := by decide
/-- The trace leaf is recognized; a lexical leaf is not a trace. -/
example : isTrace traceLeaf ∧ ¬ isTrace (lexLeaf (mkTraceToken 0)) := by decide
/-- A bare binary node over a lexical leaf and a bare trace, the shape of an Internal-Merge
    result, is a syntactic object. -/
example :
    IsSyntacticObject (Nonplanar.mk (.node (Sum.inr none)
      [.leaf (Sum.inl (mkTraceToken 0)), .leaf (Sum.inr none)])) := by decide
/-- A lexical item with children is rejected: lexical items are leaves. -/
example :
    ¬ IsSyntacticObject (Nonplanar.mk (.node (Sum.inl (mkTraceToken 0)) [.leaf
      (Sum.inr none)])) := by decide
/-- A ternary bare node is rejected: syntactic objects are binary. -/
example :
    ¬ IsSyntacticObject (Nonplanar.mk (.node (Sum.inr none)
      [.leaf (Sum.inr none), .leaf (Sum.inr none), .leaf (Sum.inr none)])) := by decide

end Minimalist
