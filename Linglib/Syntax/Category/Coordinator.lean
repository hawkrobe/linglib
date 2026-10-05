module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Linglib.Morphology.Morph
public import Linglib.Morphology.Word.Basic

/-!
# Coordinators

A coordinator is a word or clitic that links the coordinands of a coordinate construction:
*and*, *or*, *but*, *nor*. This file defines the lexical record of a coordinator and the Boolean
operation its semantic type denotes: meet for conjunctive and adversative coordinators, join for
disjunctive ones, and the complement of the join for negative ones.

The operation is stated once over an arbitrary Boolean algebra, so the same coordinator conjoins
truth values, predicates and generalized quantifiers. The composition engine applies it to two
sisters of one conjoinable type in `Semantics/Composition/Coordination.lean`. On a complete
Boolean algebra the operation extends to any set of coordinands, `Coordinator.sOp`, of which the
binary operation is the case of a pair. A particle that also builds quantifiers, as Japanese *ka*
and *mo* do, applies it to the alternatives an indeterminate supplies.

## Main definitions

* `Coordinator.Role`: the semantic type of a coordinator.
* `Coordinator.op`: the Boolean operation a semantic type denotes.
* `Coordinator.sOp`: the same operation on a set of coordinands.
* `Coordinator`: the form, gloss, semantic type and attachment of a coordinator, with the other
  uses the same form has.
* `Coordinator.Correlative`: a pair of correlative coordinators with the single coordinator
  of the plain construction.
* `Coordinator.toWord`, `Coordinator.morph`: the coordinator as a word and as a morph.

## Implementation notes

`Coordinator.op` is the truth-conditional content only. The contrast an adversative coordinator
adds to conjunction is a relation between the coordinands in discourse, and `op_adversative`
records that it is invisible here. Analyses that divide the conjunctive coordinators further, such
as the two conjunction heads of [mitrovic-sauerland-2016], classify the entries in their own
studies.

## References

* [haspelmath-2007]
* [partee-rooth-1983]
-/

@[expose] public section

namespace Coordinator

/-- A coordinator's semantic type is the Boolean operation it denotes. -/
inductive Role where
  /-- Conjunction, English *and*. -/
  | conjunctive
  /-- Disjunction, English *or*. -/
  | disjunctive
  /-- Adversative coordination, English *but*. -/
  | adversative
  /-- Negative coordination, English *nor*, Latin *neque*. -/
  | negative
  deriving DecidableEq, Repr

variable {α : Type*} [BooleanAlgebra α]

/-- The Boolean operation a semantic type denotes. -/
def op : Role → α → α → α
  | .conjunctive | .adversative => (· ⊓ ·)
  | .disjunctive => (· ⊔ ·)
  | .negative => fun p q ↦ (p ⊔ q)ᶜ

@[simp] theorem op_conjunctive (p q : α) : op .conjunctive p q = p ⊓ q := rfl

@[simp] theorem op_disjunctive (p q : α) : op .disjunctive p q = p ⊔ q := rfl

@[simp] theorem op_negative (p q : α) : op .negative p q = (p ⊔ q)ᶜ := rfl

/-- An adversative coordinator has the truth conditions of conjunction. -/
@[simp] theorem op_adversative (p q : α) : op .adversative p q = p ⊓ q := rfl

theorem op_comm (r : Role) (p q : α) : op r p q = op r q p := by
  cases r <;> simp [inf_comm, sup_comm]

/-- Coordinating a constituent with itself returns it, except under negative coordination. -/
theorem op_self {r : Role} (hr : r ≠ .negative) (p : α) : op r p p = p := by
  cases r <;> simp_all

/-- Negative coordination is the conjunction of the complements. -/
theorem op_negative_eq_inf_compl (p q : α) : op .negative p q = pᶜ ⊓ qᶜ := compl_sup

section sOp

variable {α : Type*} [CompleteBooleanAlgebra α]

/-- The operation a semantic type denotes on a set of coordinands is the infimum of the set for
conjunction, its supremum for disjunction, and the complement of its supremum for negative
coordination. -/
def sOp : Role → Set α → α
  | .conjunctive | .adversative => sInf
  | .disjunctive => sSup
  | .negative => fun s ↦ (sSup s)ᶜ

@[simp] theorem sOp_conjunctive (s : Set α) : sOp .conjunctive s = sInf s := rfl

@[simp] theorem sOp_disjunctive (s : Set α) : sOp .disjunctive s = sSup s := rfl

@[simp] theorem sOp_negative (s : Set α) : sOp .negative s = (sSup s)ᶜ := rfl

@[simp] theorem sOp_adversative (s : Set α) : sOp .adversative s = sInf s := rfl

/-- Coordinating two constituents is the operation on the pair. -/
@[simp] theorem sOp_pair (r : Role) (p q : α) : sOp r {p, q} = op r p q := by
  cases r <;> simp

theorem sOp_singleton {r : Role} (hr : r ≠ .negative) (p : α) : sOp r {p} = p := by
  cases r <;> simp_all

/-- On functions the operation is computed pointwise. -/
theorem sOp_apply {ι : Type*} (r : Role) (s : Set (ι → α)) (i : ι) :
    sOp r s i = sOp r ((· i) '' s) := by
  cases r <;> simp [sSup_apply, sInf_apply, sSup_image', sInf_image']

end sOp

end Coordinator

/-- A coordinator of a language. Its denotation is not stored, since it is `Coordinator.op` of
`role`. -/
structure Coordinator where
  /-- The surface form. -/
  form : String
  /-- The gloss. -/
  gloss : String
  /-- The semantic type. -/
  role : Coordinator.Role
  /-- Whether the form is a free word or a bound affix or clitic, and on which side of its
  host. -/
  kind : Morphology.Morph.Kind
  /-- The form is also the additive focus particle 'also, too'. -/
  alsoAdditive : Bool := false
  /-- The form also builds quantifiers, as Japanese *mo* and *ka* do on indeterminate
  pronouns. -/
  alsoQuantifier : Bool := false
  deriving DecidableEq, Repr

/-- An emphatic coordination with correlative coordinators, English *both … and*, records the
coordinators of the two coordinands and the single coordinator of the plain construction. -/
structure Coordinator.Correlative where
  /-- The form on the first coordinand. -/
  first : String
  /-- The form on the second coordinand. -/
  second : String
  /-- The coordinator of the plain construction. -/
  single : Coordinator
  deriving DecidableEq, Repr

/-- `c.toWord` is the coordinator as a word, of UD category `CCONJ`. -/
def Coordinator.toWord (c : Coordinator) : Morphology.Word := { form := c.form, cat := .CCONJ }

/-- `c.morph` is the coordinator as a morph, its form with its attachment kind. -/
def Coordinator.morph (c : Coordinator) : Morphology.Morph := ⟨c.kind, c.form⟩
