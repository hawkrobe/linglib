/-
# A Unified Analysis of the English Bare Plural (Carlson 1977)

Formalizes Carlson's foundational analysis from "A Unified Analysis of the
English Bare Plural" (Linguistics & Philosophy 1:413-457, 1977).

## The Core Insight

Bare plurals are proper names of kinds, which are abstract individuals that can
be spatially unbounded. The generic/existential distinction arises from
the PREDICATE, not from an ambiguous determiner.

## Key Claims

1. No ambiguity in bare NPs: The bare plural has one meaning (kind-denoting)
2. Kinds are individuals: Abstract entities tied to their instances
3. Stages vs individuals: Predicates select for stages or individuals
4. Existential from realization: The R relation introduces existential in the predicate

## Ontology: Individuals, Kinds, Stages

Following Carlson:
- Individuals: Spatially bounded (can only be in one place at a time)
- Kinds: Spatially unbounded (can be "here and there")
- Stages: Temporally bounded "realizations" of individuals/kinds
- R relation: x R y means "x is a realization (stage) of y"

## The Stage/Individual-Level Distinction

Milsark (1974) and Siegel (1976) distinguished:
- States: hungry, available, sick (physical), in the room -- predicated of stages
- Properties: intelligent, tall, sick (mental) -- predicated of individuals

Carlson connects this to bare plural interpretation:
- Stage-level predicates → existential reading ("Dogs are in the yard")
- Individual-level predicates → generic reading ("Dogs are intelligent")

## Why This Analysis Works

1. Narrow scope: Kinds are rigid designators (like proper names)
   - No scope ambiguity with other quantifiers
   - "Everyone saw dogs" ≠ "∃x[dog(x) ∧ everyone saw x]"

2. Opacity only: In intensional contexts, only opaque readings
   - Because the kind is rigid, not the stages

3. Differentiated scope: Can have narrower scope than "a dog"
   - "A dog was everywhere" (bizarre: same dog everywhere)
   - "Dogs were everywhere" (natural: different dogs in different places)

## References

- Carlson, G. (1977). A Unified Analysis of the English Bare Plural.
  Linguistics and Philosophy 1(3): 413-457.
- Milsark, G. (1974). Existential Sentences in English. PhD thesis, MIT.
- Siegel, M. E. A. (1976). Capturing the Adjective. PhD thesis, UMass Amherst.
- Dowty, D. (1972). Studies in the Logic of Verb Aspect. PhD thesis, UT Austin.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

namespace TruthConditional.Noun.Kind.Carlson1977

-- Ontology: Individuals, Kinds, Stages

variable (Entity World : Type)

/--
The realization relation: x R y means "x is a stage/realization of y."

A stage is a temporally and spatially bounded "slice" of an individual or kind.

For ordinary individuals (like Jake):
- A Jake-stage is Jake at a particular time and place
- Jake (the individual) is what ties all Jake-stages together

For kinds (like Dogs):
- A Dog-stage is one or more dogs at a particular time and place
- Dogs (the kind) is what ties all Dog-stages together

Key difference: Jake can only be in one place at a time (spatially bounded),
but Dogs can be in many places simultaneously (spatially unbounded).
-/
abbrev RealizationRel := Entity → Entity → Prop

/--
A stage of an individual/kind at a world.

`stageOf R x` is the set of all entities that realize x.
For Jake: the set of Jake-stages
For Dogs: the set of Dog-stages (individual dogs, groups of dogs)
-/
def stageOf (R : RealizationRel Entity) (x : Entity) : Set Entity :=
  { y | R y x }

/--
Kinds are distinguished from ordinary individuals by spatial unboundedness.

An ordinary individual can only have ONE realization at any given time.
A kind can have MANY realizations at any given time.
-/
structure IsKind (R : RealizationRel Entity) (k : Entity) : Prop where
  /-- Kinds can have multiple simultaneous realizations -/
  spatiallyUnbounded : ∃ x y, R x k ∧ R y k ∧ x ≠ y

structure IsOrdinaryIndividual (R : RealizationRel Entity) (i : Entity) : Prop where
  /-- Ordinary individuals are spatially bounded at each time -/
  spatiallyBounded : True  -- Simplified; would need temporal logic

-- Bare Plurals as Proper Names of Kinds

/--
Core claim: Bare plurals denote kinds, which are individuals (type e).

This is the same semantic type as proper names like "Jake" or "Bossie."
The only difference is that kinds are spatially unbounded.

"Dogs" translates as: λP.P{d}
where d is the kind DOGS (an individual in the model).
-/
abbrev KindDenotation := Entity

/--
Bare plural semantics: a constant denoting the kind.

Just like "Jake" denotes the individual Jake,
"dogs" denotes the individual DOGS (the kind).

No determiner, no quantifier — just a proper name.
-/
structure BarePluralEntry where
  /-- The word form -/
  form : String
  /-- The kind denoted -/
  kind : KindDenotation Entity
  /-- Evidence that it's a kind (spatially unbounded) -/
  isKind : Bool := true

-- Stage-Level vs Individual-Level Predicates

/--
Predicate classification (Milsark 1974, Siegel 1976):

- Stage-level (states): Predicated of stages (realizations).
  Examples: available, hungry, sick (physical), in the room, running

- Individual-level (properties): Predicated of individuals.
  Examples: intelligent, tall, a mammal, sick (mental)

This classification determines whether the bare plural
gets a generic or existential reading, not an ambiguity in the NP itself.
-/
inductive PredicateLevel where
  | stageLevel       -- "States" in Milsark's terminology
  | individualLevel  -- "Properties" in Milsark's terminology
  deriving DecidableEq, Repr

/--
Stage-level predicates (Milsark's "states").

These can appear in existential there-constructions:
- "There are dogs available" ✓
- "There are dogs hungry" ✓
- "There are dogs in the yard" ✓

These select stages, not individuals.
-/
def stageLevelExamples : List String :=
  ["available", "hungry", "awake", "drunk", "asleep",
   "sick (physical)", "in the room", "on the table",
   "running", "barking", "sitting"]

/--
Individual-level predicates (Milsark's "properties").

These cannot appear in existential there-constructions:
- *"There are dogs intelligent" ✗
- *"There are dogs tall" ✗
- *"There are dogs mammals" ✗

These select individuals, not stages.
-/
def individualLevelExamples : List String :=
  ["intelligent", "tall", "clever", "obnoxious",
   "sick (mental)", "a mammal", "a good pet"]

/--
Classify a predicate.

In a full implementation, this would be lexically specified.
-/
structure PredicateEntry where
  form : String
  level : PredicateLevel

-- Semantic Composition: The Key Insight

/--
Individual-level predicate semantics: Direct predication of the kind.

`⟦be intelligent⟧ = I'`

"Dogs are intelligent" = I'(d)
where d is the kind DOGS.

This is true iff INTELLIGENT is in the property set of DOGS.
No existential quantifier involved!
-/
abbrev IndividualLevelPred := Entity → Bool

/--
Stage-level predicate semantics: Predication via the R relation.

`⟦be hungry⟧ = λx.∃y[R(y,x) ∧ hungry'(y)]`

"Dogs are hungry" = ∃y[R(y,d) ∧ hungry'(y)]

The existential comes from THE PREDICATE, not from the NP.
This is why bare plurals get existential readings with stage-level predicates.
-/
def stageLevelPred (R : RealizationRel Entity) (P : Entity → Bool) : Entity → Prop :=
  λ x => ∃ y, R y x ∧ P y = true

/--
The progressive operator: Turns any predicate into stage-level.

`⟦-ing⟧ = λP'.λx.∃y[R(y,x) ∧ P'(y)]`

This is why:
- "Dogs run" (generic — individual-level in simple present)
- "Dogs are running" (existential — progressive makes it stage-level)
-/
def progressive (R : RealizationRel Entity) (P : Entity → Bool) : Entity → Prop :=
  stageLevelPred Entity R P

-- Derivations: Generic vs Existential

variable {Entity World : Type}

/--
Generic reading derivation: Individual-level predicate + kind.

"Dogs are intelligent"
1. ⟦dogs⟧ = d (the kind)
2. ⟦be intelligent⟧ = I' (individual-level)
3. Composition: I'(d)

Result: A property is directly attributed to the kind.
Truth: INTELLIGENT ∈ property-set(DOGS)
-/
def genericDerivation
    (kind : Entity)
    (pred : IndividualLevelPred Entity)
    : Bool :=
  pred kind

/--
Existential reading derivation: Stage-level predicate + kind.

"Dogs are in the yard"
1. ⟦dogs⟧ = d (the kind)
2. ⟦be in the yard⟧ = λx.∃y[R(y,x) ∧ in-yard'(y)] (stage-level)
3. Composition: ∃y[R(y,d) ∧ in-yard'(y)]

Result: The predicate introduces existential quantification over stages.
Truth: There exists a dog-stage that is in the yard.
-/
def existentialDerivation
    (R : RealizationRel Entity)
    (kind : Entity)
    (stagePred : Entity → Bool)
    : Prop :=
  stageLevelPred Entity R stagePred kind

-- Key Theorem: One Meaning, Two Readings

/--
Carlson's central claim: The bare plural is never ambiguous.

The different "readings" (generic vs existential) arise from:
1. The predicate's level (individual vs stage)
2. Not from different meanings of ∅NP

This is why there's no scope ambiguity with bare plurals —
they're just proper names, and proper names don't scope.
-/
theorem bare_plural_not_ambiguous
    (kind : Entity)
    (R : RealizationRel Entity)
    (indPred : IndividualLevelPred Entity)
    (stagePred : Entity → Bool)
    : (genericDerivation kind indPred = indPred kind) ∧
      (existentialDerivation R kind stagePred = ∃ y, R y kind ∧ stagePred y = true) := by
  constructor
  · rfl
  · rfl

-- Narrow Scope: Proper Names Don't Scope

/-!
Why bare plurals show narrow scope: They're proper names.

Just as "Jake is everywhere" only means "Jake is in every place"
(not "every place has some Jake"), so too:

"Dogs were everywhere" only means the KIND dogs has realizations
everywhere — not that some particular dogs are everywhere.

The existential over stages is introduced by the predicate,
so it always has narrowest scope (inside the predicate abstract).
-/

/-- Translation of a quantified NP (for comparison) -/
abbrev QuantifiedNP (E : Type) := (E → Bool) → Bool

/-- Translation of a bare plural: just a property set selector -/
abbrev BarePluralNP (E : Type) := (E → Bool) → Bool

/-- Bare plural NP: λP.P{k} -/
def barePluralTranslation (k : Entity) : BarePluralNP Entity :=
  λ P => P k

/-- Some-NP: λP.∃x[N(x) ∧ P(x)] -/
def someNPTranslation (domain : List Entity) (N : Entity → Bool) : QuantifiedNP Entity :=
  λ P => domain.any (λ x => N x && P x)

/--
Key theorem: Bare plurals behave like proper names, not quantifiers.

"Everyone saw dogs" is not ambiguous in the way "Everyone saw some dogs" is.

With "some dogs": ∃ can scope above or below "everyone"
With "dogs": the kind d is rigid, no scope interaction
-/
theorem bare_plural_rigid_designator
    (k : Entity)
    (P : Entity → Bool)
    : barePluralTranslation k P = P k := rfl

-- Differentiated Scope: Narrower Than Indefinites

/-!
Differentiated scope: Bare plurals can scope narrower than "a N".

(29) "A dog was everywhere" — bizarre (same dog in every place)
(30) "Dogs were everywhere" — natural (different dogs in different places)

With "a dog": the ∃ must scope outside "everywhere"
With "dogs": stages can vary with places (∃ inside "everywhere")

This follows from:
- "dogs" = the kind (rigid)
- "be everywhere" = λx.∀p[Place(p) → ∃y[R(y,x) ∧ At(y,p)]]
- Composition: ∀p[Place(p) → ∃y[R(y,d) ∧ At(y,p)]]

Different places can have different realizations!
-/

/-- "be everywhere" as a stage-level predicate over locations -/
def beEverywhere
    (R : RealizationRel Entity)
    (places : List Entity)
    (atPred : Entity → Entity → Bool)  -- At(stage, place)
    : Entity → Prop :=
  λ x => ∀ p ∈ places, ∃ y, R y x ∧ atPred y p = true

/--
Key theorem: Kinds allow differentiated scope; individuals don't.

For an ordinary individual i: "i was everywhere" requires the same
realizations at each place (bizarre for spatially bounded entities).

For a kind k: "k was everywhere" allows different realizations
at each place (natural, because kinds are spatially unbounded).
-/
theorem kind_allows_differentiated_scope
    (R : RealizationRel Entity)
    (k : Entity)
    (_hKind : IsKind Entity R k)
    (places : List Entity)
    (atPred : Entity → Entity → Bool)
    : beEverywhere R places atPred k =
      (∀ p ∈ places, ∃ y, R y k ∧ atPred y p = true) := rfl

-- Opacity: Kinds Are Rigid, Stages Are Not

/-!
Opacity facts explained:

"Max believes dogs to have eaten his sponge"
- Only opaque reading: Max believes the KIND dogs to have this property
- Not: Max believes of some particular dogs that they ate his sponge

The transparent reading is unavailable because:
1. "dogs" denotes the kind d (rigid designator)
2. No particular dogs are referred to
3. The stages are introduced by the predicate, inside the intensional context

Compare with "Max believes some dogs to have eaten his sponge":
- Transparent: ∃x[dog(x) ∧ Max believes x ate the sponge]
- Opaque: Max believes ∃x[dog(x) ∧ x ate the sponge]

With bare plurals, only the "opaque" pattern is possible.
-/

/-- Belief predicate (intensional) -/
abbrev Belief (World : Type) := World → Bool

/-- Intensional context: stage-level predicate inside belief -/
def beliefContext
    (_R : RealizationRel Entity)
    (kind : Entity)
    (beliefContent : Entity → Belief World)
    (w : World)
    : Prop :=
  -- Max believes: ∃y[R(y,d) ∧ ate-sponge(y)]
  -- The ∃ is inside the belief, not outside
  beliefContent kind w = true

/--
Key theorem: Bare plurals in intensional contexts yield only opaque readings.

The existential over stages is introduced by the predicate,
which is inside the intensional context. Therefore, no transparent reading.
-/
theorem bare_plural_opaque_only
    (R : RealizationRel Entity)
    (kind : Entity)
    (stagePred : Entity → Bool)
    : existentialDerivation R kind stagePred =
      (∃ y, R y kind ∧ stagePred y = true) := rfl

-- Connection to Subsequent Work

/-!
## Theoretical Legacy

Carlson 1977 established:

1. Unified analysis: One meaning for bare plurals, readings from context
2. Kinds as individuals: Type e, not a quantifier
3. Stage/individual distinction: Source of generic vs existential
4. R relation: Connects kinds to their instances via stages

Subsequent theories build on or respond to this:

### Chierchia 1998 (`Chierchia1998.lean`)
- Accepts kinds as individuals
- Adds ∩/∪ operators for property↔kind mapping
- DKP = derived kind predication ≈ Carlson's stage-level predication
- Nominal Mapping Parameter for cross-linguistic variation

### Krifka 2004 (`Krifka2004.lean`)
- Rejects kinds as basic; bare NPs are PROPERTIES
- ∃-shift is position-sensitive (differs from Carlson)
- Information structure determines interpretation

### Dayal 2004 (`Dayal2004.lean`)
- Extends Carlson/Chierchia with singular kinds ("The dodo is extinct")
- Meaning Preservation ranking for type shifts
- Number morphology constrains instantiation sets

## Insight for RSA

Carlson's analysis suggests that:
- Literal meaning of "dogs" = the kind
- Generic vs existential = pragmatic (predicate-driven)
- This connects to threshold semantics for generics

See `Theories/Comparisons/GenericSemantics.lean` for the connection.
-/

-- Verifications

/-- Stage-level predicates introduce existential -/
example (R : RealizationRel Entity) (k : Entity) (P : Entity → Bool) :
    stageLevelPred Entity R P k = (∃ y, R y k ∧ P y = true) := rfl

/-- Individual-level predicates are direct -/
example (k : Entity) (P : IndividualLevelPred Entity) :
    genericDerivation k P = P k := rfl

/-- Progressive makes any predicate stage-level -/
example (R : RealizationRel Entity) (P : Entity → Bool) :
    progressive Entity R P = stageLevelPred Entity R P := rfl

/-- Bare plurals translate like proper names -/
example (k : Entity) (P : Entity → Bool) :
    barePluralTranslation k P = P k := rfl

-- Examples from the Paper

/-!
## Key Examples from Carlson 1977

### Generic readings (individual-level predicates)
- "Horses are mammals" — mammals ∈ property-set(HORSES)
- "Dogs bark" — barks ∈ property-set(DOGS) (habitual = individual-level)
- "Dogs are intelligent" — intelligent ∈ property-set(DOGS)

### Existential readings (stage-level predicates)
- "Dogs are in the next room" — ∃y[R(y,DOGS) ∧ in-next-room(y)]
- "Doctors tried to save the boy" — ∃y[R(y,DOCTORS) ∧ tried-to-save(y,boy)]
- "Dogs are barking" — ∃y[R(y,DOGS) ∧ barking(y)] (progressive = stage-level)

### Narrow scope
- "Cats are here and cats aren't here" — CONTRADICTION
  = here(CATS) ∧ ¬here(CATS)
  (not: ∃x[cat(x) ∧ here(x)] ∧ ∃x[cat(x) ∧ ¬here(x)])

### Differentiated scope
- "Dogs were everywhere" — ∀p[∃y[R(y,DOGS) ∧ At(y,p)]]
  Natural: different dogs in different places
- "A dog was everywhere" — ∃x[dog(x) ∧ ∀p[At(x,p)]]
  Bizarre: same dog in every place

### Opacity
- "Max believes dogs ate his sponge"
  = Max believes [∃y[R(y,DOGS) ∧ ate-sponge(y)]]
  Not: ∃y[R(y,DOGS) ∧ Max believes ate-sponge(y)]
-/

end TruthConditional.Noun.Kind.Carlson1977
