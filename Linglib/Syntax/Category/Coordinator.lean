module

public import Linglib.Syntax.Category.Adposition.Basic

/-!
# Coordinators

A coordinator is a word or clitic that links the coordinands of a coordinate construction, such
as *and*, *or*, *but* and *nor*. This file defines its lexical record: the morph, which says
whether the coordinator is a free word or a bound clitic or affix, the gloss, the semantic type,
and the other uses its form has. What a coordinator denotes, an operation on the set of
coordinands that its semantic type fixes, is `Coordinator.denote` in
`Semantics/Composition/Coordinator.lean`.

## Main definitions

* `Coordinator.Role`: the semantic type of a coordinator.
* `Coordinator`: the morph, gloss and semantic type of a coordinator, with the other uses the
  same form has.
* `Coordinator.Correlative`: a pair of correlative coordinators with the single coordinator
  of the plain construction.
* `Coordinator.IsAlsoComitative`: the coordinator's form is a comitative adposition, 'and' is
  'with'.

## Implementation notes

* A comitative use is a relation to an `Adposition` entry, not a field. Comitative case markers,
  as in Korean and Classical Tibetan, have no entries to relate to and are noted in the
  coordinator's docstring. The additive and quantifier uses are flags until the library has
  entries for additive particles and for the quantifiers a particle builds.
* Analyses that divide the conjunctive coordinators further, such as the two conjunction heads
  of [mitrovic-sauerland-2016], classify the entries in their own studies.

## References

* [haspelmath-2007]
* [mitrovic-sauerland-2016]
* [stassen-2000]
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
  /-- The form, a free word or a clitic or affix bound on one side of its host. -/
  morph : Morphology.Morph
  /-- The gloss. -/
  gloss : String
  /-- The semantic type. -/
  role : Coordinator.Role
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
  first : List Morphology.Morph
  /-- The form on the second coordinand. -/
  second : List Morphology.Morph
  /-- The coordinator of the plain construction. -/
  single : Coordinator
  deriving DecidableEq, Repr

namespace Coordinator

variable (c : Coordinator) (p : Adposition)

/-- `c.toWord` is the coordinator as a word, of UD category `CCONJ`, its form in boundary
notation. -/
def toWord : Morphology.Word := { form := toString c.morph, cat := .CCONJ }

/-- `c.IsAlsoComitative p`: the coordinator's form is the comitative adposition `p`, so that 'and'
is 'with', [stassen-2000]'s lexical identity of the coordinator with the comitative marker. -/
def IsAlsoComitative : Prop := p.morphs = [c.morph] ∧ .com ∈ p.functions

instance : Decidable (c.IsAlsoComitative p) := inferInstanceAs (Decidable (_ ∧ _))

end Coordinator
