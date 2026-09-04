/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Building and reading syntactic objects

Merge on the carrier is written `*`: External Merge of two objects, and the re-merge of a mover
with the remainder in Internal Merge. Concrete objects are built ordered, as
`PlanarSyntacticObject`s, and forgotten to the carrier by `toSyntacticObject`. The accessors read
the root token, the leaf and node counts, and the trace predicate, which recognizes the trace
leaves, bare or indexed.

## Main definitions

* `Minimalist.SyntacticObject.mkLeaf`, `mkLeafPhon`: lexical leaves from features.
* `Minimalist.SyntacticObject.getLIToken`, `isTrace`, `leafCount`, `nodeCount`, `IsLeaf`.
-/

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

namespace SyntacticObject

/-- The default syntactic object is the bare trace. -/
instance : Inhabited SyntacticObject := ⟨trace⟩

/-! ### Merge as multiplication -/

/-- `l * r = merge l r`: Merge on the carrier. -/
noncomputable instance : Mul SyntacticObject := ⟨merge⟩

@[simp] theorem mul_def (l r : SyntacticObject) : l * r = merge l r := rfl

theorem mul_comm (l r : SyntacticObject) : l * r = r * l := merge_comm l r

/-- A lexical item is a leaf. -/
instance : Coe LIToken SyntacticObject := ⟨leaf⟩

end SyntacticObject

namespace PlanarSyntacticObject

/-- `l * r = merge l r`: Merge on the ordered carrier, in the given order. -/
instance : Mul PlanarSyntacticObject := ⟨merge⟩

@[simp] theorem mul_def (l r : PlanarSyntacticObject) : l * r = merge l r := rfl

/-- A lexical item is a leaf. -/
instance : Coe LIToken PlanarSyntacticObject := ⟨leaf⟩

/-- An ordered object is an object. -/
instance : Coe PlanarSyntacticObject SyntacticObject := ⟨toSyntacticObject⟩

/-- Forgetting the order is a homomorphism of magmas. -/
def toSyntacticObjectHom : PlanarSyntacticObject →ₙ* SyntacticObject :=
  ⟨toSyntacticObject, toSyntacticObject_merge⟩

@[simp] theorem toSyntacticObjectHom_apply (p : PlanarSyntacticObject) :
    toSyntacticObjectHom p = p.toSyntacticObject := rfl

@[simp] theorem toSyntacticObject_mul (l r : PlanarSyntacticObject) :
    (l * r).toSyntacticObject = l.toSyntacticObject * r.toSyntacticObject :=
  toSyntacticObject_merge l r

end PlanarSyntacticObject

namespace SyntacticObject

/-! ### Lexical leaves from features -/

/-- A lexical leaf from a category and selectional stack. -/
def mkLeaf (cat : Cat) (sel : SelStack) (id : Nat) : SyntacticObject :=
  SyntacticObject.leaf ⟨.simple cat sel, id⟩

/-- A lexical leaf with a phonological form. -/
def mkLeafPhon (cat : Cat) (sel : SelStack) (phon : String) (id : Nat) : SyntacticObject :=
  SyntacticObject.leaf ⟨.simple cat sel (phonForm := phon), id⟩

/-! ### Accessors -/

/-- The lexical token at the root, if the root is a lexical leaf. -/
def getLIToken (s : SyntacticObject) : Option LIToken :=
  match UnorderedTree.rootValue s.val with
  | .inl tok => some tok
  | .inr _ => none

@[simp] theorem getLIToken_leaf (tok : LIToken) : (SyntacticObject.leaf tok).getLIToken
    = some tok := rfl

@[simp] theorem getLIToken_trace : trace.getLIToken = none := rfl

@[simp] theorem getLIToken_traceOf (tok : LIToken) : (traceOf tok).getLIToken = none := rfl

theorem traceOf_ne_trace (tok : LIToken) : traceOf tok ≠ trace := by
  intro h
  have h' : (Sum.inr (some tok) : Vertex) = Sum.inr none :=
    congrArg (fun s : SyntacticObject => UnorderedTree.rootValue s.val) h
  simp at h'

@[simp] theorem getLIToken_merge (l r : SyntacticObject) : (merge l r).getLIToken = none := by
  rw [getLIToken, merge_val, UnorderedTree.rootValue_node]

/-- A trace leaf, bare or indexed. -/
def isTrace (s : SyntacticObject) : Prop :=
  (UnorderedTree.rootValue s.val).isRight = true ∧ UnorderedTree.numNodes s.val = 1

instance (s : SyntacticObject) : Decidable (isTrace s) := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem isTrace_traceOf (tok : LIToken) : isTrace (traceOf tok) := ⟨rfl, rfl⟩

@[simp] theorem not_isTrace_leaf (tok : LIToken) : ¬ isTrace (SyntacticObject.leaf tok) := fun h =>
  Bool.false_ne_true h.1

@[simp] theorem isTrace_trace : isTrace trace := ⟨rfl, rfl⟩

/-- The number of leaves, traces included. -/
def leafCount (s : SyntacticObject) : Nat := UnorderedTree.numLeaves s.val

/-- `IsLeaf s ↔ s.leafCount = 1`: a lexical or trace leaf. -/
def IsLeaf (s : SyntacticObject) : Prop := s.leafCount = 1

instance : DecidablePred IsLeaf := fun _ => inferInstanceAs (Decidable (_ = _))

@[simp] theorem isLeaf_leaf (tok : LIToken) : IsLeaf (SyntacticObject.leaf tok) := rfl
@[simp] theorem isLeaf_trace : IsLeaf trace := rfl

/-- A shape summary; the full tree is a quotient with no faithful readout. -/
instance : Repr SyntacticObject where
  reprPrec s _ := match s.getLIToken with
    | some tok => f!"SyntacticObject.leaf {repr tok}"
    | none =>
      if s.IsLeaf then f!"SyntacticObject.trace"
      else f!"⟨SyntacticObject merge, {s.leafCount} leaves⟩"

/-- `nodeCount s = leafCount s - 1`, the number of internal vertices of a full binary tree. -/
def nodeCount (s : SyntacticObject) : Nat := UnorderedTree.numLeaves s.val - 1

@[simp] theorem leafCount_leaf (tok : LIToken) : (SyntacticObject.leaf tok).leafCount = 1 := rfl
@[simp] theorem leafCount_trace : trace.leafCount = 1 := rfl

end SyntacticObject

/-! ### Carrier tests -/

private def demoVP : SyntacticObject :=
  (PlanarSyntacticObject.merge (PlanarSyntacticObject.leaf (mkTraceToken 0))
    (PlanarSyntacticObject.leaf (mkTraceToken 1))).toSyntacticObject

/-- The DSL-built tree is a genuine syntactic object. -/
example : IsSyntacticObject demoVP.val := by decide
/-- Its head token reads back via `getLIToken` of the left leaf. -/
example : (SyntacticObject.leaf (mkTraceToken 0)).getLIToken = some (mkTraceToken 0) := by decide
/-- It has two leaves and one internal node. -/
example : demoVP.leafCount = 2 ∧ demoVP.nodeCount = 1 := by decide
/-- The trace leaf is recognized; a lexical leaf is not a trace. -/
example : isTrace SyntacticObject.trace ∧ ¬ isTrace (SyntacticObject.leaf
    (mkTraceToken 0)) := by decide
/-- A bare binary node over a lexical leaf and a bare trace, the shape of an Internal-Merge
    result, is a syntactic object. -/
example :
    IsSyntacticObject (UnorderedTree.mk (.node (Sum.inr none)
      [.leaf (Sum.inl (mkTraceToken 0)), .leaf (Sum.inr none)])) := by decide
/-- A lexical item with children is rejected: lexical items are leaves. -/
example :
    ¬ IsSyntacticObject (UnorderedTree.mk (.node (Sum.inl (mkTraceToken 0)) [.leaf
      (Sum.inr none)])) := by decide
/-- A ternary bare node is rejected: syntactic objects are binary. -/
example :
    ¬ IsSyntacticObject (UnorderedTree.mk (.node (Sum.inr none)
      [.leaf (Sum.inr none), .leaf (Sum.inr none), .leaf (Sum.inr none)])) := by decide

end Minimalist
