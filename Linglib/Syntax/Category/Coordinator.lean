module

public import Linglib.Morphology.Morph
public import Linglib.Morphology.Word.Basic

/-!
# Coordinators

A coordinator is a word or clitic that links the coordinands of a coordinate construction, such
as *and*, *or*, *but* and *nor*. This file defines its lexical record, with the form, the gloss,
the semantic type and the attachment of the coordinator and the other uses its form has. What a
coordinator denotes, an operation on the set of coordinands that its semantic type fixes, is
`Coordinator.denote` in `Semantics/Composition/Coordinator.lean`.

## Main definitions

* `Coordinator.Role`: the semantic type of a coordinator.
* `Coordinator`: the form, gloss, semantic type and attachment of a coordinator, with the other
  uses the same form has.
* `Coordinator.Correlative`: a pair of correlative coordinators with the single coordinator
  of the plain construction.
* `Coordinator.toWord`, `Coordinator.morph`: the coordinator as a word and as a morph.

## Implementation notes

Analyses that divide the conjunctive coordinators further, such as the two conjunction heads of
[mitrovic-sauerland-2016], classify the entries in their own studies.

## References

* [haspelmath-2007]
* [mitrovic-sauerland-2016]
-/

@[expose] public section

namespace Coordinator

/-- A coordinator's semantic type is conjunction, disjunction, adversative or negative
coordination. -/
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

end Coordinator

/-- A coordinator of a language. Its denotation is not stored, since its semantic type fixes it,
`Coordinator.denote`. -/
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
