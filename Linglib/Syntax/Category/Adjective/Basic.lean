import Linglib.Features.ScalarDimension
import Linglib.Morphology.DegreeContainment

/-!
# Adjective

The syntactic core of the adjective as a grammatical object, modeled on
`Syntax/Category/Pronoun/`: surface form, the scalar `dimension` **key** it measures + the
lexicalized pole, comparison morphology, and lexical antonymy. The dimension is
carried as a key (cf. `Pronoun` importing `Person`/`Number`), not interpreted here.

Gradability is **not** a type split — it is the derived predicate `IsGradable`
(`dimension.isSome`); a non-gradable adjective (*wooden*, *former*, *medical*) is the
same type with `dimension = none`.

The **degree-semantic** layer lives one layer up, in `Semantics/Gradability`, where the
scale's boundedness, positive standard, and Kennedy class *become relevant*: the
`GradableAdjective` refinement there `extends Adjective` with the `standardOverride`
and derives `scaleType`/`standard`/`adjectiveClass` from the (shape, pole, override).
This file deliberately does not depend on the Degree/Kennedy semantics.

## Deferred (earn their consumers, cf. `Pronoun`'s deferred capability tower)

* Agreement φ-features + `toWord` realization — added when an agreeing-language fragment
  sets them (φ with no setter would be dead fields).
* Dixon `PCClass` view (`ScalarDimension.pcClass`) — waits on a lightweight `PCClass` home
  (it currently sits in the heavy `Morphology/RootTypology.lean`).
* The `Modifier`/`Gradable` capability classes — built at the second-carrier trigger
  (an `Adverb`/degree-word struct), exactly as `Pronoun` deferred `Proform`.

This is the adjectival realization of a property concept; when a verb- or
noun-strategy fragment lands, factor a `PropertyConcept` superclass.
-/

open Features (ScalarDimension)
open Morphology.DegreeContainment (DegreePattern)

set_option autoImplicit false

/-! ### Comparison morphology -/

/-- How a comparative/superlative grade is formed. -/
inductive Adjective.ComparisonStrategy
  | synthetic | periphrastic | suppletive
  deriving DecidableEq, Repr, BEq

/-- Grade-level comparison morphology: the cross-linguistic structure (per-grade
    formation strategy + the suppletion pattern, whose *ABA constraint lives in
    `Morphology/DegreeContainment`, [bobaljik-2012]) plus the surface comparative and
    superlative forms. -/
structure Adjective.ComparisonFacet where
  formComp  : Option String := none
  formSuper : Option String := none
  comparativeStrategy : Adjective.ComparisonStrategy := .synthetic
  superlativeStrategy : Adjective.ComparisonStrategy := .synthetic
  suppletion : DegreePattern := ⟨0, 0, 0⟩
  /-- Equative strategy, if the language marks it morphologically (not under the
      comparative/superlative containment). -/
  equative : Option Adjective.ComparisonStrategy := none
  deriving DecidableEq, Repr, BEq

/-- No comparison marking (the default). -/
def Adjective.ComparisonFacet.regular : Adjective.ComparisonFacet := {}

/-! ### The adjective object -/

/-- The adjective lexeme: the syntactic core every adjective shares — surface form,
    the scalar `dimension` key + lexicalized pole, comparison morphology, and lexical
    antonymy. Carries no denotation of its own (cf. `Pronoun`); the degree-semantic
    interpretation of `dimension`/pole is derived one layer up, on `GradableAdjective`
    in `Semantics/Gradability`.

    Gradability is **not** a type split: it is the derived predicate `IsGradable`
    (`dimension.isSome`); a non-gradable adjective is the same type with
    `dimension = none`. Coexists with `namespace Adjective` (a type and a namespace may
    share a name). -/
structure Adjective where
  /-- Surface form (citation/positive-grade). -/
  form : String
  /-- Native script form, when distinct. -/
  script : Option String := none
  /-- The scalar dimension measured, as a `Features.ScalarDimension` key.
      `none` for classifying/relational adjectives (*wooden*, *former*, *medical*)
      and other non-gradables. -/
  dimension : Option ScalarDimension := none
  /-- Which pole of the scale the adjective lexicalizes (*short*, *empty*, *wet*):
      the only thing distinguishing polar scale-mates that share one `dimension`. -/
  isLowerEndpoint : Bool := false
  /-- Comparative/superlative morphology. -/
  comparison : Adjective.ComparisonFacet := .regular
  /-- Lexical antonym's surface form, when it has a stable one. -/
  antonymForm : Option String := none
  deriving Repr, DecidableEq, BEq

namespace Adjective

/-- Gradable iff it carries a scalar dimension — derived (cf. `Pronoun.category`). -/
def IsGradable (a : Adjective) : Prop := a.dimension.isSome = true

instance (a : Adjective) : Decidable a.IsGradable := by unfold IsGradable; infer_instance

/-- The suppletion pattern of the comparison paradigm — a convenience read of
    `comparison.suppletion` (the field consumers most often want). -/
def suppletion (a : Adjective) : DegreePattern := a.comparison.suppletion

end Adjective
