/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Building and reading syntactic objects

Merge on the carrier is written `*`: External Merge of two objects, and the re-merge of a mover
with the remainder in Internal Merge. Concrete objects are built ordered, as
`PlanarSyntacticObject`s, and forgotten to the carrier by `toSyntacticObject`. The accessors read
the root token, the leaf and node counts, and the trace predicate, which recognizes the trace
leaves, bare or indexed.

## Main definitions

* `Minimalist.SyntacticObject.mkLeaf`, `mkLeafPhon`: lexical leaves from features.
* `Minimalist.SyntacticObject.token?`, `isTrace`, `leafCount`, `nodeCount`, `IsLeaf`.
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

namespace SyntacticObject

/-- The default syntactic object is the bare trace. -/
instance : Inhabited SyntacticObject := ⟨trace⟩

/-! ### Merge as multiplication -/

/-- Merge on the carrier is written `l * r`. -/
noncomputable instance : Mul SyntacticObject := ⟨merge⟩

@[simp] theorem mul_def (l r : SyntacticObject) : l * r = merge l r := rfl

theorem mul_comm (l r : SyntacticObject) : l * r = r * l := merge_comm l r

/-- A lexical item is a leaf. -/
instance : Coe LexicalItem.Token SyntacticObject := ⟨leaf⟩

/-- Merge in braces, as [marcolli-chomsky-berwick-2025] writes it: `{l, r} = merge l r`, with
    `{s} = s`. -/
noncomputable instance : Insert SyntacticObject SyntacticObject := ⟨merge⟩

instance : Singleton SyntacticObject SyntacticObject := ⟨id⟩

@[simp] theorem insert_def (l r : SyntacticObject) : ({l, r} : SyntacticObject) = merge l r := rfl

end SyntacticObject

namespace PlanarSyntacticObject

/-- Merge on the ordered carrier, in the given order, is written `l * r`. -/
instance : Mul PlanarSyntacticObject := ⟨merge⟩

@[simp] theorem mul_def (l r : PlanarSyntacticObject) : l * r = merge l r := rfl

/-- A lexical item is a leaf. -/
instance : Coe LexicalItem.Token PlanarSyntacticObject := ⟨leaf⟩

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

/-! ### Merge in braces

[marcolli-chomsky-berwick-2025] writes Merge as set formation, `{α, β}`. Lean's `{a, b}` is
`insert a {b}`, so with `{p} = p` the object `{T, {V, PossP}}` is `T * (V * PossP)`, in the given
order; its elements are objects, a head entering as its leaf. -/

instance : Singleton PlanarSyntacticObject PlanarSyntacticObject := ⟨id⟩

instance : Insert PlanarSyntacticObject PlanarSyntacticObject := ⟨merge⟩

@[simp] theorem singleton_def (p : PlanarSyntacticObject) : ({p} : PlanarSyntacticObject) = p := rfl

@[simp] theorem insert_def (l r : PlanarSyntacticObject) :
    ({l, r} : PlanarSyntacticObject) = merge l r := rfl

end PlanarSyntacticObject

namespace SyntacticObject

/-! ### Lexical leaves from features -/

/-- A lexical leaf from a category and selectional stack. -/
def mkLeaf (cat : Cat) (sel : SelStack) (id : Nat) : SyntacticObject :=
  SyntacticObject.leaf ⟨.of cat sel, id⟩

/-- A lexical leaf with a phonological form. -/
def mkLeafPhon (cat : Cat) (sel : SelStack) (phon : String) (id : Nat) : SyntacticObject :=
  SyntacticObject.leaf ⟨.of cat sel (phonForm := phon), id⟩

/-! ### Accessors -/

/-- The lexical token at the root, if the root is a lexical leaf. -/
def token? (s : SyntacticObject) : Option LexicalItem.Token :=
  match UnorderedTree.value s.val with
  | .inl o => o
  | .inr _ => none

@[simp] theorem token?_leaf (tok : LexicalItem.Token) : (SyntacticObject.leaf tok).token?
    = some tok := rfl

@[simp] theorem token?_trace : trace.token? = none := rfl

@[simp] theorem token?_traceOf (tok : LexicalItem.Token) : (traceOf tok).token? = none := rfl

/-- `s` is a lexical leaf whose item's category is `c`. -/
def isLeafOf (c : Cat) (s : SyntacticObject) : Prop :=
  s.token?.map (·.item.cat) = some c

instance (c : Cat) : DecidablePred (isLeafOf c) := λ _ => inferInstanceAs (Decidable (_ = _))

@[simp] theorem isLeafOf_leaf (c : Cat) (tok : LexicalItem.Token) :
    isLeafOf c (SyntacticObject.leaf tok) ↔ tok.item.cat = c := by
  simp [isLeafOf]

@[simp] theorem not_isLeafOf_trace (c : Cat) : ¬ isLeafOf c trace := by simp [isLeafOf]

theorem traceOf_ne_trace (tok : LexicalItem.Token) : traceOf tok ≠ trace := by
  intro h
  have h' : (Sum.inr (some tok) : Vertex) = Sum.inr none :=
    congrArg (fun s : SyntacticObject => UnorderedTree.value s.val) h
  simp at h'

@[simp] theorem token?_merge (l r : SyntacticObject) : (merge l r).token? = none := by
  rw [token?, merge_val, UnorderedTree.value_node]

/-- A trace leaf, bare or indexed. -/
def isTrace (s : SyntacticObject) : Prop :=
  (UnorderedTree.value s.val).isRight = true ∧ UnorderedTree.numNodes s.val = 1

instance (s : SyntacticObject) : Decidable (isTrace s) := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem isTrace_traceOf (tok : LexicalItem.Token) : isTrace (traceOf tok) := ⟨rfl, rfl⟩

@[simp] theorem not_isTrace_leaf (tok : LexicalItem.Token) :
    ¬ isTrace (SyntacticObject.leaf tok) := fun h =>
  Bool.false_ne_true h.1

@[simp] theorem isTrace_trace : isTrace trace := ⟨rfl, rfl⟩

/-- The number of leaves, traces included. -/
def leafCount (s : SyntacticObject) : Nat := UnorderedTree.numLeaves s.val

/-- An object is a lexical or trace leaf exactly when its leaf count is one. -/
def IsLeaf (s : SyntacticObject) : Prop := s.leafCount = 1

instance : DecidablePred IsLeaf := fun _ => inferInstanceAs (Decidable (_ = _))

@[simp] theorem isLeaf_leaf (tok : LexicalItem.Token) : IsLeaf (SyntacticObject.leaf tok) := rfl
@[simp] theorem isLeaf_trace : IsLeaf trace := rfl

/-- A shape summary; the full tree is a quotient with no faithful readout. -/
instance : Repr SyntacticObject where
  reprPrec s _ := match s.token? with
    | some tok => f!"SyntacticObject.leaf {repr tok}"
    | none =>
      if s.IsLeaf then f!"SyntacticObject.trace"
      else f!"⟨SyntacticObject merge, {s.leafCount} leaves⟩"

/-- `nodeCount s = leafCount s - 1`, the number of internal vertices of a full binary tree. -/
def nodeCount (s : SyntacticObject) : Nat := UnorderedTree.numLeaves s.val - 1

@[simp] theorem leafCount_leaf (tok : LexicalItem.Token) :
    (SyntacticObject.leaf tok).leafCount = 1 := rfl
@[simp] theorem leafCount_trace : trace.leafCount = 1 := rfl

end SyntacticObject

/-! ### Carrier tests -/

private def demoTok (i : ℕ) : LexicalItem.Token := ⟨.of .N [], i⟩

private def demoVP : SyntacticObject :=
  (PlanarSyntacticObject.merge (PlanarSyntacticObject.leaf (demoTok 0))
    (PlanarSyntacticObject.leaf (demoTok 1))).toSyntacticObject

/-- The DSL-built tree is a genuine syntactic object. -/
example : IsSyntacticObject demoVP.val := by decide
/-- Its head token reads back via `token?` of the left leaf. -/
example : (SyntacticObject.leaf (demoTok 0)).token? = some (demoTok 0) := by decide
/-- It has two leaves and one internal node. -/
example : demoVP.leafCount = 2 ∧ demoVP.nodeCount = 1 := by decide
/-- The trace leaf is recognized; a lexical leaf is not a trace. -/
example : isTrace SyntacticObject.trace ∧ ¬ isTrace (SyntacticObject.leaf
    (demoTok 0)) := by decide
/-- A bare binary node over a lexical leaf and a bare trace, the shape of an Internal-Merge
    result, is a syntactic object. -/
example :
    IsSyntacticObject (UnorderedTree.mk (.node Vertex.bare
      [.leaf (Vertex.lex (demoTok 0)), .leaf Vertex.trace])) := by decide
/-- A lexical item with children is rejected: lexical items are leaves. -/
example :
    ¬ IsSyntacticObject (UnorderedTree.mk (.node (Vertex.lex (demoTok 0)) [.leaf
      Vertex.trace])) := by decide
/-- A ternary bare node is rejected: syntactic objects are binary. -/
example :
    ¬ IsSyntacticObject (UnorderedTree.mk (.node Vertex.bare
      [.leaf Vertex.trace, .leaf Vertex.trace, .leaf Vertex.trace])) := by decide

end Minimalist
