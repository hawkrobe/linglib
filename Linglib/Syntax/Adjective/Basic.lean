import Linglib.Semantics.Gradability.Dimension
import Linglib.Semantics.Degree.Defs
import Linglib.Semantics.Degree.Kennedy
import Linglib.Morphology.DegreeContainment

/-!
# Adjective

Lexical core for the adjective as a grammatical object, modeled on `Syntax/Pronoun/`:
the general `Adjective` structure (the lexical core every adjective shares) and the
`GradableAdjective` specialization (which `extends Adjective` with the degree-semantic
lexical fields). The general concept gets the plain name; specializations `extends` it.

The scale an adjective measures is the `Semantics.Gradability.Dimension` **key**
(imported as a field, cf. `Pronoun` importing `Person`/`Number`); its boundedness,
comparison-class dependence, and telicity are *derived views* of that key, not stored.
The degree **denotation** (`DirectedMeasure`) lives downstream in `Semantics/Gradability`.

## The `scaleType` decomposition

The old `GradableAdjEntry.scaleType : Boundedness` conflated three independent facts and
contradicted `Dimension.boundedness` (`wet`/`dry` share one closed `.wetness` scale, yet
stored `.lowerBounded`/`.upperBounded`). They are separated here:

* **shape** — `dimension.boundedness` (derived);
* **pole** — `isLowerEndpoint` (the *only* thing distinguishing `wet` from `dry`);
* **standard** — `GradableAdjective.standard`, derived from (shape, pole) with an
  `Option PositiveStandard` override for the `good`/MPA residual ([kennedy-2007],
  [kennedy-mcnally-2005]).

## Deferred (earn their consumers, cf. `Pronoun`'s deferred capability tower)

* Agreement φ-features + `toWord` realization — added when an agreeing-language fragment
  sets them (φ with no setter would be dead fields).
* Dixon `PCClass` view (`Dimension.pcClass`) — waits on a lightweight `PCClass` home
  (it currently sits in the heavy `Morphology/RootTypology.lean`).
* `MultidimAdjective` (Sassoon multidimensionality) and the gradable facets
  (`evaluativeValence`/`spatialConfigType`/`informationalStrength`/subjectivity).
* The `Modifier`/`Gradable` capability classes — built at the second-carrier trigger
  (an `Adverb`/degree-word struct), exactly as `Pronoun` deferred `Proform`.

This is the adjectival realization of a property concept; when a verb- or
noun-strategy fragment lands, factor a `PropertyConcept` superclass.
-/

open Semantics.Gradability (Dimension)
open Semantics.Degree (PositiveStandard AdjectiveClass interpretiveEconomy)
open Core.Order (Boundedness)
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

/-! ### The general adjective object -/

/-- The general adjective object: the lexical core every adjective shares — surface
    form, the scalar `dimension` key + lexicalized pole, comparison morphology, and
    lexical antonymy. Carries no denotation of its own (cf. `Pronoun`); the degree
    meaning is derived in `Semantics/Gradability`. Specializations `extends` it.
    Coexists with `namespace Adjective` (a type and a namespace may share a name). -/
structure Adjective where
  /-- Surface form (citation/positive-grade). -/
  form : String
  /-- Native script form, when distinct. -/
  script : Option String := none
  /-- The scalar dimension measured, as a `Semantics.Gradability.Dimension` key.
      `none` for classifying/relational adjectives (*wooden*, *former*, *medical*)
      and other non-gradables. -/
  dimension : Option Dimension := none
  /-- Which pole of the scale the adjective lexicalizes (*short*, *empty*, *wet*):
      the only thing distinguishing polar scale-mates that share one `dimension`. -/
  isLowerEndpoint : Bool := false
  /-- Comparative/superlative morphology. -/
  comparison : Adjective.ComparisonFacet := .regular
  /-- Lexical antonym's surface form, when it has a stable one. -/
  antonymForm : Option String := none
  deriving Repr, DecidableEq, BEq

/-- A gradable adjective: `Adjective` plus the degree-semantic lexical fields
    (Kennedy). Its well-formedness requires a `dimension`. -/
structure GradableAdjective extends Adjective where
  /-- Override the Kennedy default standard (the `good`/MPA residual: an open-shape
      scale that nonetheless takes a functional/contextual standard, [beltrama-2025]).
      `none` = take the derived default. -/
  standardOverride : Option PositiveStandard := none
  deriving Repr, BEq

namespace Adjective

/-- Gradable iff it carries a scalar dimension — derived (cf. `Pronoun.category`). -/
def IsGradable (a : Adjective) : Prop := a.dimension.isSome = true

instance (a : Adjective) : Decidable a.IsGradable := by unfold IsGradable; infer_instance

/-- The suppletion pattern of the comparison paradigm — a convenience read of
    `comparison.suppletion` (the field consumers most often want). -/
def suppletion (a : Adjective) : DegreePattern := a.comparison.suppletion

end Adjective

namespace GradableAdjective

/-- The scale's intrinsic shape — read off the `dimension` key, not stored. -/
def scaleType (g : GradableAdjective) : Boundedness :=
  (g.dimension.map Dimension.boundedness).getD .open_

/-- The effective positive standard: the default from (scale shape, pole),
    overridable by `standardOverride`. This is the quantity the old `scaleType` field
    conflated — it separates `wet` (closed + lower ⇒ min) from `dry` (closed + upper ⇒
    max), and lets `good` (open shape) take a contextual standard rather than a bogus
    bound. ([kennedy-2007]'s Interpretive Economy on the open/singly-bounded cases.) -/
def standard (g : GradableAdjective) : PositiveStandard :=
  g.standardOverride.getD <|
    match g.dimension.map Dimension.boundedness, g.isLowerEndpoint with
    | some .closed, true  => .minEndpoint
    | some .closed, false => .maxEndpoint
    | some b,       _     => interpretiveEconomy b
    | none,         _     => .contextual

/-- Kennedy's adjective class — derived from `standard`, not stored
    ([kennedy-2007], [kennedy-mcnally-2005]). -/
def adjectiveClass (g : GradableAdjective) : AdjectiveClass :=
  match g.dimension with
  | none => .nonGradable
  | some _ =>
    match g.standard with
    | .contextual  => .relativeGradable
    | .minEndpoint => .absoluteMinimum
    | .maxEndpoint => .absoluteMaximum
    | .functional  => .mildlyPositive

/-- Comparison-class dependence — the relative/absolute distinction, derived. -/
def IsRelative (g : GradableAdjective) : Prop := g.adjectiveClass.IsRelative

instance (g : GradableAdjective) : Decidable g.IsRelative := by
  unfold IsRelative; infer_instance

end GradableAdjective
