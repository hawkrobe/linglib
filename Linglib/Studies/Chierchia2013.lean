import Linglib.Logic.Natural.Basic

/-!
# Chierchia 2013: disjunction, ignorance, and the distribution of *any*

This file formalizes two threads of *Logic in Grammar* ([chierchia-2013]). First, the positional
asymmetry of disjunction: the same *or* is preferentially exclusive in an upward-entailing
position and inclusive in a downward-entailing one, because Maximize Strength computes the
not-both implicature only where it strengthens. `predictReading` derives the preferred reading
from the polarity a position determines, and the six positions of Ch.1 instantiate it. The
ignorance side of disjunction — *Harry is in Antwerp or Brussels* conveying that the speaker
knows neither disjunct, unlike the scalar implicature of *some* — is recorded in the section
prose.

Second, *any* as an existential whose domain alternatives are obligatorily active: it is
ungrammatical exactly where no reading survives exhaustification, namely the positive episodic
context, where exhaustification is contradictory; in a downward-entailing or question context
exhaustification is vacuous and *any* is a plain existential, and a modal or generic rescues it
into free choice.

## Main definitions

* `DisjunctionReading`, `DisjunctionPosition`, `positionPolarity`, `predictReading` — the
  positional asymmetry, derived from polarity
* `UFCIContext`, `ufciGrammatical`, `ufciReading` — the distribution and readings of *any*
* `FCIFlavor` — the existential/universal free-choice dimension later studies consume

## Main results

* `predictions_match_examples` — at each of the six positions, the recorded polarity and the
  preferred reading are the derived ones
* `ufciGrammatical_iff_reading` — grammaticality and reading are one prediction
* `anyExamples_match_prediction` — the recorded *any* judgments match it in every sampled context

## References

* [chierchia-2013]
* [gazdar-1979]
* [geurts-2010]
-/

namespace Chierchia2013


/-! The ignorance data — *Harry is in Antwerp or Brussels* implicating that the speaker knows
neither disjunct ([geurts-2010]), its contrast with the scalar *some*, longer disjunctions
carrying ignorance about every disjunct, the readings blocked by explicit speaker knowledge, and
the scope interactions with *every* — are described in the section prose of Ch.1; the derivable
part, the positional asymmetry, follows. -/

/-!
## Positional Asymmetry in Disjunction Interpretation

[chierchia-2013] "Logic in Grammar" Ch.1 observes that the same lexical
material yields different preferred readings based on structural position:

| Position | Polarity | Preferred Reading |
|----------|----------|-------------------|
| Consequent of conditional | UE | Exclusive |
| Antecedent of conditional | DE | Inclusive |
| Scope of "every" | UE | Exclusive |
| Restrictor of "every" | DE | Inclusive |
| Positive sentence | UE | Exclusive |
| Negative sentence | DE | Inclusive |

### The Core Pattern

UE contexts: exclusive reading preferred
- "If everything goes well, we'll hire Mary or Sue"
- Default: we'll hire exactly one of them

DE contexts: inclusive reading preferred
- "If we hire Mary or Sue, everything will go well"
- Default: hiring either or both leads to success

### Explanation via Maximize Strength

The asymmetry follows from the Maximize Strength principle:
- In UE: adding "not both" strengthens → compute SI
- In DE: adding "not both" would weaken → don't compute SI

When the exclusive SI is not computed, the inclusive reading emerges.

-/

/--
Type of disjunction interpretation.
-/
inductive DisjunctionReading where
  | inclusive   -- p ∨ q (possibly both)
  | exclusive   -- (p ∨ q) ∧ ¬(p ∧ q) (not both)
  deriving DecidableEq, Repr

/--
Structural position of the disjunction.
-/
inductive DisjunctionPosition where
  | matrix            -- Main clause
  | conditional_cons  -- Consequent of conditional (UE)
  | conditionalAntecedent   -- Antecedent of conditional (DE)
  | every_scope       -- Scope of "every" (UE)
  | every_restrictor  -- Restrictor of "every" (DE)
  | negation_scope    -- Under negation (DE)
  deriving DecidableEq, Repr

open NaturalLogic (ContextPolarity)

/--
Determine context polarity from position.
-/
def positionPolarity : DisjunctionPosition → ContextPolarity
  | .matrix => .upward
  | .conditional_cons => .upward
  | .conditionalAntecedent => .downward
  | .every_scope => .upward
  | .every_restrictor => .downward
  | .negation_scope => .downward

/--
Predict preferred reading from polarity.
UE → exclusive (SI computed), DE → inclusive (SI not computed).
NM → inclusive (no clear strength ordering, so no exclusive SI).
-/
def predictReading : ContextPolarity → DisjunctionReading
  | .upward => .exclusive
  | .downward => .inclusive
  | .nonMonotonic => .inclusive

/--
Example showing exclusive/inclusive asymmetry.
-/
structure ExclusiveInclusiveExample where
  /-- The sentence -/
  sentence : String
  /-- Position of disjunction -/
  position : DisjunctionPosition
  /-- Polarity of that position -/
  polarity : ContextPolarity
  /-- Preferred reading -/
  preferredReading : DisjunctionReading
  /-- Can the other reading be forced with context? -/
  canForceOther : Bool
  /-- Source -/
  source : String
  deriving Repr

-- [chierchia-2013] examples (1a,b)
def hiring_consequent : ExclusiveInclusiveExample :=
  { sentence := "If everything goes well, we'll hire Mary or Sue"
  , position := .conditional_cons
  , polarity := .upward
  , preferredReading := .exclusive
  , canForceOther := true
  , source := "Chierchia (2013) p.2 (1a)"
  }

def hiring_antecedent : ExclusiveInclusiveExample :=
  { sentence := "If we hire Mary or Sue, everything will go well"
  , position := .conditionalAntecedent
  , polarity := .downward
  , preferredReading := .inclusive
  , canForceOther := true
  , source := "Chierchia (2013) p.2 (1b)"
  }

-- Matrix clause example
def matrix_exclusive : ExclusiveInclusiveExample :=
  { sentence := "We'll hire Mary or Sue"
  , position := .matrix
  , polarity := .upward
  , preferredReading := .exclusive
  , canForceOther := true
  , source := "Standard observation"
  }

-- Universal restrictor vs scope
def every_scope : ExclusiveInclusiveExample :=
  { sentence := "Everyone likes Mary or Sue"
  , position := .every_scope
  , polarity := .upward
  , preferredReading := .exclusive
  , canForceOther := true
  , source := "Chierchia (2013) discussion"
  }

def every_restrictor : ExclusiveInclusiveExample :=
  { sentence := "Everyone who likes Mary or Sue will be happy"
  , position := .every_restrictor
  , polarity := .downward
  , preferredReading := .inclusive
  , canForceOther := true
  , source := "Chierchia (2013) discussion"
  }

-- Negation scope
def negation_scope : ExclusiveInclusiveExample :=
  { sentence := "We won't hire Mary or Sue"
  , position := .negation_scope
  , polarity := .downward
  , preferredReading := .inclusive
  , canForceOther := true
  , source := "De Morgan reading: ¬M ∧ ¬S"
  }

/--
All exclusive/inclusive examples.
-/
def exclusiveInclusiveExamples : List ExclusiveInclusiveExample :=
  [ hiring_consequent, hiring_antecedent
  , matrix_exclusive
  , every_scope, every_restrictor
  , negation_scope
  ]

/-- At each of the six positions, the recorded polarity is the one the position determines, and
the preferred reading is the one Maximize Strength predicts from it. -/
theorem predictions_match_examples :
    ∀ ex ∈ exclusiveInclusiveExamples,
      positionPolarity ex.position = ex.polarity ∧
        predictReading ex.polarity = ex.preferredReading := by
  intro ex hex
  simp only [exclusiveInclusiveExamples, List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-!
## Forcing Non-Preferred Readings

While polarity determines the default reading, context can force the
non-preferred interpretation:

### Forcing Inclusive in UE (harder)
"If everything goes well, we'll hire Mary or Sue, or both."
- Explicit "or both" forces inclusive

### Forcing Exclusive in DE (harder)
"If we hire Mary or Sue but not both, everything will go well."
- Explicit "but not both" forces exclusive

The observation: forcing requires explicit marking.
The unmarked reading follows from Maximize Strength.
-/

/--
Example of forcing a non-preferred reading.
-/
structure ForcedReadingExample where
  /-- The base sentence -/
  baseSentence : String
  /-- Position (determines default) -/
  position : DisjunctionPosition
  /-- Default reading -/
  defaultReading : DisjunctionReading
  /-- Forcing phrase -/
  forcingPhrase : String
  /-- Resulting reading -/
  forcedReading : DisjunctionReading
  /-- Notes -/
  notes : String
  deriving Repr

def force_inclusive_ue : ForcedReadingExample :=
  { baseSentence := "If everything goes well, we'll hire Mary or Sue"
  , position := .conditional_cons
  , defaultReading := .exclusive
  , forcingPhrase := "or both"
  , forcedReading := .inclusive
  , notes := "Adding 'or both' explicitly licenses inclusive reading"
  }

def force_exclusive_de : ForcedReadingExample :=
  { baseSentence := "If we hire Mary or Sue, everything will go well"
  , position := .conditionalAntecedent
  , defaultReading := .inclusive
  , forcingPhrase := "but not both"
  , forcedReading := .exclusive
  , notes := "Adding 'but not both' explicitly restricts to exclusive"
  }

/--
All forced reading examples.
-/
def forcedReadingExamples : List ForcedReadingExample :=
  [force_inclusive_ue, force_exclusive_de]


/-!
## Universal Free Choice Items

Universal FCIs like English "any" and Italian "qualunque" contrast with
existential FCIs (irgendein, yek-i, vreun):

| FCI Type | Base Force | Examples | Morphological Hints |
|----------|------------|----------|---------------------|
| Existential | ∃ | irgendein, yek-i, vreun | Often contains "one" |
| Universal | ∀ | any, qualunque, whatever | Often wh-based |

### Chierchia's analysis

Both FCI types have the same underlying existential semantics.
The universal force of "any" emerges from obligatory exhaustification
of domain alternatives.

- "any" = ∃ + obligatory domain alternatives (always active)
- "some" = ∃ + optional domain alternatives (relevance-gated)

### The "any" Distribution

1. NPI use (DE contexts): "I didn't see any students"
   - In DE, exhaustification is vacuous (domain alts are entailed)
   - Result: plain existential reading

2. FC use (modal contexts): "You may read any book"
   - Under modal, domain alts yield free choice
   - Result: universal-like permission

3. Generic use: "Any owl hunts mice" (subtrigging)
   - Generic contexts license FC reading
   - Result: universal generalization

### Why "any" Fails in Positive Episodic Contexts

"*There are any cookies"

Exhaustifying domain alternatives in UE episodic contexts yields
contradiction:
- ∃d∈D. P(d) (assertion)
- ∀d∈D. ¬[P(d) ∧ ∀y≠d.¬P(y)] (domain alt negation)

With two witnesses d₁, d₂: the second clause requires that for any d
satisfying P, some other y also satisfies P. Combined with the first
clause, this leads to infinite regress/contradiction for finite domains.

### Contrast with "some"

"Some" has the same alternatives as "any", but they are optional.
When not activated (low relevance), "some" = plain existential.
"Any" must activate alternatives, hence the restricted distribution.
-/

/--
Context type for determining Universal FCI distribution.
-/
inductive UFCIContext where
  | positiveEpisodic   -- *There are any cookies (ungrammatical)
  | negation           -- I didn't see any students (NPI)
  | conditionalAntecedent    -- If you see any students, ... (NPI)
  | deonticModal       -- You may read any book (FC)
  | epistemicModal     -- There might be any solution (FC)
  | generic            -- Any owl hunts mice (subtrigging)
  | question           -- Did you see any students? (NPI)
  deriving DecidableEq, Repr

/--
Surface reading available to a Universal FCI.

Subset of the broader EFCI reading taxonomy: UFCIs only ever yield
plain existential (NPI use, no exhaustification effect) or free choice
(via modal/generic rescue). Uniqueness, modal variation, and epistemic
ignorance are existential-FCI-specific readings.
-/
inductive UFCIReading where
  /-- Plain existential (NPI use in DE contexts) -/
  | plainExistential
  /-- Free choice (modal/generic rescue) -/
  | freeChoice
  deriving DecidableEq, Repr

/--
FCI flavor: existential vs universal force.

Note: "Universal" FCIs (English *any*, Italian *qualunque*) have existential
base meaning but universal surface force due to obligatory exhaustification.
Existential FCIs (German *irgendein*, Farsi *yek-i*, Romanian *vreun*)
retain narrow existential force. The flavor is a Chierchia-tradition
typological dimension consumed by paper-specific studies (e.g.,
[chierchia-2006]).
-/
inductive FCIFlavor where
  /-- Existential FCIs: *irgendein*, *yek-i*, *vreun* -/
  | existential
  /-- Universal FCIs: *any*, *qualunque*, *whatever* -/
  | universal
  deriving DecidableEq, Repr

/--
Universal FCI grammaticality prediction.

Ungrammatical only in positive episodic (UE without rescue).
-/
def ufciGrammatical (ctx : UFCIContext) : Bool :=
  match ctx with
  | .positiveEpisodic => false  -- Exhaustification contradicts
  | .negation => true           -- DE: vacuous exhaustification
  | .conditionalAntecedent => true    -- DE: vacuous exhaustification
  | .deonticModal => true       -- Modal rescues
  | .epistemicModal => true     -- Modal rescues
  | .generic => true            -- Generic/subtrigging rescues
  | .question => true           -- Non-monotonic: safe

/--
Reading obtained by Universal FCI in context.
-/
def ufciReading (ctx : UFCIContext) : Option UFCIReading :=
  match ctx with
  | .positiveEpisodic => none           -- Ungrammatical
  | .negation => some .plainExistential -- NPI: ¬∃ = ∀¬
  | .conditionalAntecedent => some .plainExistential
  | .deonticModal => some .freeChoice   -- FC: ◇∀
  | .epistemicModal => some .freeChoice
  | .generic => some .freeChoice        -- Generic universal
  | .question => some .plainExistential

/-- Grammaticality and reading are one prediction: *any* is out exactly where no reading
survives exhaustification — the positive episodic context, where exhaustifying the domain
alternatives is contradictory. Where it survives, it is a plain existential in the
downward-entailing and question contexts, exhaustification being vacuous there, and free choice
under the rescuing modal or generic. -/
theorem ufciGrammatical_iff_reading (ctx : UFCIContext) :
    ufciGrammatical ctx = (ufciReading ctx).isSome := by cases ctx <;> rfl

-- 7.5: Empirical Data

/--
An "any" distribution example.
-/
structure AnyExample where
  sentence : String
  context : UFCIContext
  grammatical : Bool
  reading : Option String
  notes : String
  deriving Repr

def any_positive_bad : AnyExample :=
  { sentence := "*There are any cookies"
  , context := .positiveEpisodic
  , grammatical := false
  , reading := none
  , notes := "Exhaustification yields G-contradiction" }

def any_negation_ok : AnyExample :=
  { sentence := "I didn't see any students"
  , context := .negation
  , grammatical := true
  , reading := some "NPI: ¬∃x.student(x) ∧ saw(I,x)"
  , notes := "DE context: exhaustification vacuous" }

def any_deontic_ok : AnyExample :=
  { sentence := "You may read any book"
  , context := .deonticModal
  , grammatical := true
  , reading := some "FC: ∀x.book(x) → ◇read(you,x)"
  , notes := "Modal rescues via widening" }

def any_generic_ok : AnyExample :=
  { sentence := "Any owl hunts mice"
  , context := .generic
  , grammatical := true
  , reading := some "Generic: GEN x[owl(x)] hunts(x,mice)"
  , notes := "Subtrigging: generic rescues like modal" }

def any_question_ok : AnyExample :=
  { sentence := "Did you see any students?"
  , context := .question
  , grammatical := true
  , reading := some "NPI: ?∃x.student(x) ∧ saw(you,x)"
  , notes := "Questions non-monotonic: safe for any" }

def any_conditional_ok : AnyExample :=
  { sentence := "If you see any students, tell me"
  , context := .conditionalAntecedent
  , grammatical := true
  , reading := some "NPI: ∃x.student(x) ∧ saw(you,x) → tell(you,me)"
  , notes := "Antecedent is DE" }

def anyExamples : List AnyExample :=
  [ any_positive_bad, any_negation_ok, any_deontic_ok
  , any_generic_ok, any_question_ok, any_conditional_ok ]

/-- The recorded *any* judgments match the prediction in every context sampled. -/
theorem anyExamples_match_prediction :
    anyExamples.all (fun ex => ex.grammatical == ufciGrammatical ex.context) = true := by decide

end Chierchia2013
