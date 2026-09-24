module

public import Mathlib.Basic.Rel
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Form Copy

Two inscriptions of a syntactic object are structurally identical when they coincide once the
identity of their tokens is forgotten. By default structurally identical inscriptions are
repetitions, each interpreted on its own, as the two inscriptions of *many people* in *many
people praised many people*. Form Copy assigns the copy relation to such a pair when one
c-commands the other, and copies are interpreted as one element, as in the passive *many people
were praised*. Form Copy builds no structure: it is a relation on the inscriptions of an object.

Internal Merge leaves a copy in this sense, one object at two positions. Obligatory control is
Form Copy between an inscription merged into the controlling verb's theta position and a
repetition merged independently as the embedded subject, so that at Transfer control and raising
present the same configuration. Marcolli, Chomsky and Berwick model Form Copy as the restriction
of the operad action of Merge to a diagonal, the inputs at the identified positions being one
object, so that the coproduct extracts identified copies only together.

## Main definitions

* `SyntacticObject.erase`: the tree of lexical items an object inscribes, forgetting its tokens
* `SyntacticObject.StructurallyIdentical`: two inscriptions with one erasure
* `SyntacticObject.IsRepetition`: structurally identical inscriptions that are distinct objects
* `SyntacticObject.copyRel`: the copy relation Form Copy assigns in an object

## Main results

* `SyntacticObject.StructurallyIdentical.merge`: structural identity is a congruence for Merge
* `SyntacticObject.mk_mem_copyRel_merge`: Form Copy relates an object merged with a term to every
  structurally identical inscription inside that term
* `SyntacticObject.self_mem_copyRel_merge`: the copy Internal Merge leaves is related to its
  antecedent

## Implementation notes

Syntactic objects are values, so a copy is one object at two vertices and a repetition two
objects with one erasure. Form Copy applies at the phase level, and the Phase Impenetrability
Condition bounds its reach further; that timing is not modelled.

## TODO

The modified coproduct on the diagonal, whose coassociativity Marcolli, Chomsky and Berwick
sketch through a Hopf algebra of graphs, and the deletion of the lower copy at externalization.

## References

* [chomsky-etal-2023]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.SyntacticObject

open UnorderedTree

variable {s t x y l r l' r' : SyntacticObject}

/-! ### Structural identity -/

/-- The tree of lexical items and traces an object inscribes, forgetting which token fills each
leaf. -/
def erase (s : SyntacticObject) : UnorderedTree (LexicalItem ⊕ Option LexicalItem) :=
  s.val.map (Sum.map LIToken.item (Option.map LIToken.item))

@[simp]
theorem erase_leaf (tok : LIToken) : (leaf tok).erase = UnorderedTree.leaf (.inl tok.item) :=
  map_leaf _ _

@[simp]
theorem erase_traceOf (tok : LIToken) :
    (traceOf tok).erase = UnorderedTree.leaf (.inr (some tok.item)) :=
  map_leaf _ _

@[simp]
theorem erase_merge (l r : SyntacticObject) :
    (merge l r).erase = node (.inr none) {l.erase, r.erase} := by
  simp [erase, map_node]

/-- Two inscriptions are structurally identical when they coincide once token identity is
forgotten. -/
def StructurallyIdentical (x y : SyntacticObject) : Prop := x.erase = y.erase

instance : DecidableRel StructurallyIdentical := fun x y ↦
  inferInstanceAs (Decidable (x.erase = y.erase))

theorem structurallyIdentical_equivalence : Equivalence StructurallyIdentical :=
  InvImage.equivalence _ _ eq_equivalence

@[refl]
theorem StructurallyIdentical.refl (x : SyntacticObject) : StructurallyIdentical x x := rfl

theorem StructurallyIdentical.symm (h : StructurallyIdentical x y) : StructurallyIdentical y x :=
  Eq.symm h

theorem StructurallyIdentical.trans (h : StructurallyIdentical x y)
    (h' : StructurallyIdentical y t) : StructurallyIdentical x t :=
  Eq.trans h h'

/-- Structural identity is a congruence for Merge. -/
theorem StructurallyIdentical.merge (hl : StructurallyIdentical l l')
    (hr : StructurallyIdentical r r') : StructurallyIdentical (merge l r) (merge l' r') := by
  simp only [StructurallyIdentical, erase_merge] at *
  rw [hl, hr]

/-- Structurally identical inscriptions have the same size. -/
theorem StructurallyIdentical.numNodes_eq (h : StructurallyIdentical x y) :
    x.val.numNodes = y.val.numNodes := by
  simpa [erase] using congrArg UnorderedTree.numNodes h

/-- Two inscriptions are repetitions when they are structurally identical but distinct objects,
built from different tokens: the default relation between identical inscriptions. -/
def IsRepetition (x y : SyntacticObject) : Prop := StructurallyIdentical x y ∧ x ≠ y

instance : DecidableRel IsRepetition := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-! ### The copy relation -/

/-- The copy relation Form Copy assigns in `s` holds of a pair of structurally identical
inscriptions, the first c-commanding the second. -/
def copyRel (s : SyntacticObject) : SetRel SyntacticObject SyntacticObject :=
  {p | cCommandsIn s p.1 p.2 ∧ StructurallyIdentical p.1 p.2}

@[simp]
theorem mem_copyRel : (x, y) ∈ s.copyRel ↔ cCommandsIn s x y ∧ StructurallyIdentical x y :=
  Iff.rfl

instance (s : SyntacticObject) (p : SyntacticObject × SyntacticObject) :
    Decidable (p ∈ s.copyRel) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- An object merged with a term c-commands everything that term reflexively contains. -/
theorem cCommandsIn_merge (hne : x ≠ t) (h : containsOrEq t y) : cCommandsIn (merge x t) x y :=
  ⟨t, mem_terms.2 (.single (by simp)), ⟨merge x t, self_mem_terms _, by simp, by simp, hne⟩, h⟩

/-- Form Copy relates an object merged with a term to every structurally identical inscription
inside that term: the configuration of control, where the lower inscription is a repetition. -/
theorem mk_mem_copyRel_merge (h : contains t y) (hxy : StructurallyIdentical x y) :
    (x, y) ∈ (merge x t).copyRel := by
  refine ⟨cCommandsIn_merge ?_ (containsOrEq_iff_eq_or_contains.2 (.inr h)), hxy⟩
  rintro rfl
  exact (numNodes_lt_of_contains h).ne hxy.numNodes_eq.symm

/-- The copy Internal Merge leaves is related to its antecedent: an object merged with a term
containing it c-commands its own lower occurrence. -/
theorem self_mem_copyRel_merge (h : contains t x) : (x, x) ∈ (merge x t).copyRel :=
  mk_mem_copyRel_merge h rfl

end Minimalist.SyntacticObject
