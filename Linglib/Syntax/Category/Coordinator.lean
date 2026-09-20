import Mathlib.Order.BooleanAlgebra.Basic
import Linglib.Morphology.Morph
import Linglib.Morphology.Word.Basic

/-!
# Coordinators

A coordinator is a word or clitic that links the coordinands of a coordinate construction:
*and*, *or*, *but*, *nor*. This file defines the lexical record of a coordinator and the Boolean
operation its semantic type denotes: meet for conjunctive and adversative coordinators, join for
disjunctive ones, and the complement of the join for negative ones.

The operation is stated once over an arbitrary Boolean algebra, so the same coordinator conjoins
truth values, predicates and generalized quantifiers. The composition engine applies it to two
sisters of one conjoinable type in `Semantics/Composition/Coordination.lean`.

## Main definitions

* `Coordinator.Role`: the semantic type of a coordinator.
* `Coordinator.op`: the Boolean operation a semantic type denotes.
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

namespace Coordinator

/-- The semantic type of a coordinator. -/
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

end Coordinator

/-- A coordinator of a language. Its denotation is not stored: it is `Coordinator.op` of
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

/-- An emphatic coordination with correlative coordinators, English *both … and*: the
coordinators of the two coordinands and the single coordinator of the plain construction. -/
structure Coordinator.Correlative where
  /-- The form on the first coordinand. -/
  first : String
  /-- The form on the second coordinand. -/
  second : String
  /-- The coordinator of the plain construction. -/
  single : Coordinator
  deriving DecidableEq, Repr

/-- The coordinator as a word, UD category `CCONJ`. -/
def Coordinator.toWord (c : Coordinator) : Morphology.Word := { form := c.form, cat := .CCONJ }

/-- The coordinator as a morph, its form with its attachment kind. -/
def Coordinator.morph (c : Coordinator) : Morphology.Morph := ⟨c.kind, c.form⟩
