module

public import Linglib.Semantics.Degree.Antonymy
public import Linglib.Semantics.Degree.Scale
public import Linglib.Morphology.Paradigm.Contiguity

/-!
# Adjective

The syntactic core of the adjective as a grammatical object, modeled on
`Syntax/Category/Pronoun/`: surface form, the scalar `dimension` **key** it measures + the
lexicalized pole, comparison morphology, and lexical antonymy. The dimension is
carried as a key (cf. `Pronoun` importing `Person`/`Number`), not interpreted here.

Gradability is **not** a type split — it is the derived predicate `IsGradable`
(`dimension.isSome`); a non-gradable adjective (*wooden*, *former*, *medical*) is the
same type with `dimension = none`.

The **degree-semantic** layer lives one layer up, in `Semantics/Degree/Adjective.lean`, where the
scale's boundedness, positive standard, and Kennedy class *become relevant*: the
`GradableAdjective` refinement there `extends Adjective` with the `lexicalStandard`
and derives `boundedness`/`standard`/`adjectiveClass` from the (shape, pole, override).
This file deliberately does not depend on the Degree/Kennedy semantics.

## Deferred (earn their consumers, cf. `Pronoun`'s deferred capability tower)

* Agreement φ-features + `toWord` realization — added when an agreeing-language fragment
  sets them (φ with no setter would be dead fields).
* Dixon's property-concept classes (`ScalarDimension.pcClass`) — waits on wiring to
  `Semantics.PropertyConcept.Class` (in `Semantics/Root/PropertyConcept.lean`).
* The `Modifier`/`Gradable` capability classes — built at the second-carrier trigger
  (an `Adverb`/degree-word struct), exactly as `Pronoun` defers its deictic axis.

This is the adjectival realization of a property concept; when a verb- or
noun-strategy fragment lands, factor a `PropertyConcept` superclass.
-/

@[expose] public section

open Degree (ScalarDimension)

/-! ### Comparison morphology -/

/-- A comparative or superlative grade is formed by affixation or by a degree word. Suppletion is
orthogonal, recorded by the root pattern `suppletion`; *better* is synthetic and
suppletive. -/
inductive Adjective.ComparisonStrategy
  | synthetic | periphrastic
  deriving DecidableEq, Repr, BEq

/-- The comparison paradigm of an adjective records the comparative and superlative forms, how
    each grade is formed, and the root pattern over the three grades, whose *ABA constraint lives
    in `Morphology/Paradigm/Contiguity.lean` ([bobaljik-2012]). -/
structure Adjective.Comparison where
  formComp  : Option String := none
  formSuper : Option String := none
  comparativeStrategy : Adjective.ComparisonStrategy := .synthetic
  superlativeStrategy : Adjective.ComparisonStrategy := .synthetic
  suppletion : Morphology.Paradigm 3 ℕ := Morphology.Paradigm.aaa
  /-- Equative strategy, if the language marks it morphologically (not under the
      comparative/superlative containment). -/
  equative : Option Adjective.ComparisonStrategy := none
  deriving DecidableEq, Repr, BEq

namespace Adjective.Comparison

/-- No comparison forms recorded (the default). -/
def regular : Adjective.Comparison := {}

/-- Synthetic comparison forms a comparative and a superlative on one root. -/
def synthetic (comparative superlative : String) : Adjective.Comparison :=
  { formComp := comparative, formSuper := superlative }

/-- Periphrastic comparison forms *more X* and *most X*. -/
def periphrastic (comparative superlative : String) : Adjective.Comparison :=
  { formComp := comparative, formSuper := superlative
  , comparativeStrategy := .periphrastic, superlativeStrategy := .periphrastic }

/-- Suppletive comparison forms the grades on another root, in the given root pattern, as in
*good – better – best*. -/
def suppletive (comparative superlative : String)
    (pattern : Morphology.Paradigm 3 ℕ := Morphology.Paradigm.abb) : Adjective.Comparison :=
  { formComp := comparative, formSuper := superlative, suppletion := pattern }

end Adjective.Comparison

/-! ### The adjective object -/

/-- An adjective lexeme records the syntactic core every adjective shares, its surface form, its
    scalar dimension and pole, its comparison morphology and its lexical antonym. It carries no
    denotation of its own; the degree semantics is `GradableAdjective` in
    `Semantics/Degree/Adjective.lean`. Gradability is the derived predicate `IsGradable`, and a
    non-gradable adjective has no dimension. -/
structure Adjective where
  /-- Surface form (citation/positive-grade). -/
  form : String
  /-- Native script form, when distinct. -/
  script : Option String := none
  /-- The scalar dimension measured, as a `Degree.ScalarDimension` key.
      `none` for classifying/relational adjectives (*wooden*, *former*, *medical*)
      and other non-gradables. -/
  dimension : Option ScalarDimension := none
  /-- The direction of the ordering the adjective imposes on its `dimension`. Antonyms share a
      dimension and reverse the ordering (*tall* positive, *short* negative), so the negative
      member measures on the dual scale. -/
  polarity : Polarity := .positive
  /-- Comparative/superlative morphology. -/
  comparison : Adjective.Comparison := .regular
  /-- Lexical antonym's surface form, when it has a stable one. -/
  antonymForm : Option String := none
  deriving Repr, DecidableEq, BEq

namespace Adjective

/-- Gradable iff it carries a scalar dimension — derived (cf. `Pronoun.category`). -/
def IsGradable (a : Adjective) : Prop := a.dimension.isSome = true

instance (a : Adjective) : Decidable a.IsGradable := by unfold IsGradable; infer_instance

end Adjective
