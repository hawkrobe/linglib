import Linglib.Core.Logic.NaturalLogic

/-!
# Disjunction Ignorance @cite{chierchia-2013}

Empirical patterns for ignorance inferences from disjunction, organized
around @cite{chierchia-2013}'s positional-asymmetry account.

"Harry is in Antwerp or Brussels" implicates:
1. Speaker doesn't know Harry is in Antwerp
2. Speaker doesn't know Harry is in Brussels

This is different from scalar implicature:
- Scalar: "some" → speaker knows not all
- Ignorance: "A or B" → speaker doesn't know which

The file provides a `predictReading` function over `ContextPolarity`
(from `Core.NaturalLogic`) that derives the preferred inclusive/exclusive
reading from structural position.
-/

namespace Phenomena.Polarity.Studies.Chierchia2013


/--
Empirical pattern: Disjunction and speaker ignorance.

"Harry is in Antwerp or Brussels" implicates:
1. Speaker doesn't know Harry is in Antwerp
2. Speaker doesn't know Harry is in Brussels

Source: @cite{gazdar-1979}, @cite{geurts-2010} Ch. 3.3
-/
structure DisjunctionIgnoranceDatum where
  /-- The disjunctive statement -/
  disjunction : String
  /-- First disjunct -/
  disjunctA : String
  /-- Second disjunct -/
  disjunctB : String
  /-- Ignorance inference about A -/
  inferenceA : String
  /-- Ignorance inference about B -/
  inferenceB : String
  deriving Repr

/--
Classic example: Harry's location.
Source: @cite{geurts-2010} p.61
-/
def harryLocation : DisjunctionIgnoranceDatum :=
  { disjunction := "Harry is in Antwerp or Brussels"
  , disjunctA := "Harry is in Antwerp"
  , disjunctB := "Harry is in Brussels"
  , inferenceA := "Speaker doesn't know Harry is in Antwerp"
  , inferenceB := "Speaker doesn't know Harry is in Brussels"
  }

/--
Location example with Mary.
-/
def maryLocation : DisjunctionIgnoranceDatum :=
  { disjunction := "Mary went to Paris or London"
  , disjunctA := "Mary went to Paris"
  , disjunctB := "Mary went to London"
  , inferenceA := "Speaker doesn't know Mary went to Paris"
  , inferenceB := "Speaker doesn't know Mary went to London"
  }

/--
Activity example.
-/
def johnActivity : DisjunctionIgnoranceDatum :=
  { disjunction := "John is reading or sleeping"
  , disjunctA := "John is reading"
  , disjunctB := "John is sleeping"
  , inferenceA := "Speaker doesn't know John is reading"
  , inferenceB := "Speaker doesn't know John is sleeping"
  }

/--
All basic ignorance examples.
-/
def disjunctionIgnoranceExamples : List DisjunctionIgnoranceDatum :=
  [harryLocation, maryLocation, johnActivity]


/--
Comparison between ignorance and scalar implicatures.

Scalar implicatures and ignorance inferences differ:
- Scalar: speaker knows the stronger alternative is false
- Ignorance: speaker doesn't know which disjunct is true
-/
structure IgnoranceVsScalarDatum where
  /-- The utterance -/
  utterance : String
  /-- Type of inference -/
  inferenceType : String
  /-- The inference -/
  inference : String
  /-- Is speaker claiming knowledge? -/
  speakerClaimsKnowledge : Bool
  deriving Repr

/--
"Some" triggers scalar implicature (speaker knows).
-/
def someScalar : IgnoranceVsScalarDatum :=
  { utterance := "Some students passed"
  , inferenceType := "scalar"
  , inference := "Speaker believes not all students passed"
  , speakerClaimsKnowledge := true  -- Speaker knows not all
  }

/--
"Or" triggers ignorance (speaker doesn't know).
-/
def orIgnorance : IgnoranceVsScalarDatum :=
  { utterance := "John passed or Mary passed"
  , inferenceType := "ignorance"
  , inference := "Speaker doesn't know which one passed"
  , speakerClaimsKnowledge := false  -- Speaker doesn't know
  }

/--
All comparison examples.
-/
def comparisonExamples : List IgnoranceVsScalarDatum :=
  [someScalar, orIgnorance]


/--
Ignorance extends to long disjunctions (n > 2).

For "A or B or C", we get ignorance about each disjunct:
- Speaker doesn't know A
- Speaker doesn't know B
- Speaker doesn't know C

Source: @cite{geurts-2010} p.61-64
-/
structure LongDisjunctionIgnoranceDatum where
  /-- The disjunctive statement -/
  disjunction : String
  /-- List of disjuncts -/
  disjuncts : List String
  /-- Ignorance inferences (one per disjunct) -/
  ignoranceInferences : List String
  deriving Repr

/--
Three-way disjunction example.
Source: @cite{geurts-2010} p.61
-/
def threeWayLocation : LongDisjunctionIgnoranceDatum :=
  { disjunction := "Harry is in Antwerp, Brussels, or Copenhagen"
  , disjuncts := ["Antwerp", "Brussels", "Copenhagen"]
  , ignoranceInferences :=
      [ "Speaker doesn't know Harry is in Antwerp"
      , "Speaker doesn't know Harry is in Brussels"
      , "Speaker doesn't know Harry is in Copenhagen"
      ]
  }

/--
Four-way disjunction example.
-/
def fourWayActivity : LongDisjunctionIgnoranceDatum :=
  { disjunction := "John is reading, writing, sleeping, or eating"
  , disjuncts := ["reading", "writing", "sleeping", "eating"]
  , ignoranceInferences :=
      [ "Speaker doesn't know John is reading"
      , "Speaker doesn't know John is writing"
      , "Speaker doesn't know John is sleeping"
      , "Speaker doesn't know John is eating"
      ]
  }

/--
All long disjunction examples.
-/
def longDisjunctionExamples : List LongDisjunctionIgnoranceDatum :=
  [threeWayLocation, fourWayActivity]


/--
Cases where ignorance inference is blocked or cancelled.
-/
structure IgnoranceBlockingDatum where
  /-- The context or construction -/
  context : String
  /-- Example sentence -/
  sentence : String
  /-- Is ignorance blocked? -/
  ignoranceBlocked : Bool
  /-- Explanation -/
  explanation : String
  deriving Repr

/--
Explicit knowledge blocks ignorance.
-/
def explicitKnowledge : IgnoranceBlockingDatum :=
  { context := "Speaker has explicit knowledge"
  , sentence := "Harry is in Antwerp or Brussels — I know it's Antwerp"
  , ignoranceBlocked := true
  , explanation := "Explicit assertion of knowledge cancels ignorance inference"
  }

/--
Rhetorical questions don't trigger ignorance.
-/
def rhetoricalQuestion : IgnoranceBlockingDatum :=
  { context := "Rhetorical/exam question"
  , sentence := "Is the capital of France Paris or London?"
  , ignoranceBlocked := true
  , explanation := "Speaker (examiner) knows the answer; no genuine ignorance"
  }

/--
Embedded disjunction under belief.
-/
def embeddedBelief : IgnoranceBlockingDatum :=
  { context := "Embedded under belief verb"
  , sentence := "John believes Harry is in Antwerp or Brussels"
  , ignoranceBlocked := true
  , explanation := "Ignorance is about John's epistemic state, not speaker's"
  }

/--
All blocking examples.
-/
def blockingExamples : List IgnoranceBlockingDatum :=
  [explicitKnowledge, rhetoricalQuestion, embeddedBelief]


/--
Interaction between disjunction ignorance and quantifiers.
-/
structure QuantifiedIgnoranceDatum where
  /-- The sentence -/
  sentence : String
  /-- Quantifier scope -/
  quantifierScope : String
  /-- Ignorance inference -/
  inference : String
  /-- Notes on the reading -/
  notes : String
  deriving Repr

/--
Disjunction in scope of universal.
-/
def universalScopeDisj : QuantifiedIgnoranceDatum :=
  { sentence := "Every student read Moby Dick or Huckleberry Finn"
  , quantifierScope := "∀ > ∨"
  , inference := "Speaker doesn't know which book each student read"
  , notes := "Ignorance is about the distribution, not existence"
  }

/--
Disjunction scoping over universal.
-/
def disjScopeUniversal : QuantifiedIgnoranceDatum :=
  { sentence := "Every student read Moby Dick, or every student read Huckleberry Finn"
  , quantifierScope := "∨ > ∀"
  , inference := "Speaker doesn't know which book all students read"
  , notes := "Global ignorance about which alternative"
  }

/--
All quantified ignorance examples.
-/
def quantifiedIgnoranceExamples : List QuantifiedIgnoranceDatum :=
  [universalScopeDisj, disjScopeUniversal]


/-!
## Positional Asymmetry in Disjunction Interpretation

@cite{chierchia-2013} "Logic in Grammar" Ch.1 observes that the same lexical
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

open Core.NaturalLogic (ContextPolarity)

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

-- @cite{chierchia-2013} examples (1a,b)
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

-- Verify predictions match data
#guard exclusiveInclusiveExamples.all (λ ex =>
  predictReading ex.polarity == ex.preferredReading)


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
existential FCIs (irgendein, yek-i, vreun) handled in
@cite{alonso-ovalle-moghiseh-2025}:

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
Universal FCI: existential with obligatorily active domain alternatives.
-/
structure UniversalFCI where
  /-- Base meaning is existential -/
  baseIsExistential : Bool := true
  /-- Domain alternatives are always active (not relevance-gated) -/
  obligatoryDomainAlts : Bool := true
  /-- Can be rescued via modal insertion -/
  modalRescue : Bool := true
  /-- Can be rescued via generic/subtrigging -/
  genericRescue : Bool := true

/-- English "any" as a Universal FCI -/
def any_FCI : UniversalFCI where
  baseIsExistential := true
  obligatoryDomainAlts := true
  modalRescue := true
  genericRescue := true

/-- Italian "qualunque" as a Universal FCI -/
def qualunque_FCI : UniversalFCI where
  baseIsExistential := true
  obligatoryDomainAlts := true
  modalRescue := true
  genericRescue := true

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

-- 7.1: "Any" in DE Contexts (NPI Use)

/--
In DE contexts, exhaustifying "any"'s alternatives yields entailments,
so the exhaustification is vacuous and "any" = plain existential.

This explains the NPI distribution of "any".
-/
theorem any_in_de_is_existential : ufciReading .negation = some .plainExistential := rfl

/--
"I didn't see any students" ≡ "I didn't see a student"

The "any" contributes no special meaning in DE contexts.
-/
theorem any_negation_plain : ufciReading .negation = some .plainExistential := rfl

-- 7.2: "Any" in Modal Contexts (FC Use)

/--
Under modals, "any" yields free choice via exhaustification.

"You may read any book" = For each book x, you may read x
-/
theorem any_modal_fc : ufciReading .deonticModal = some .freeChoice := rfl

/--
Modal insertion is the rescue mechanism for Universal FCIs.
-/
theorem any_rescued_by_modal : ufciGrammatical .deonticModal = true := rfl

-- 7.3: "Any" in Positive Episodic (Ungrammatical)

/--
"*There are any cookies" is ungrammatical.

Domain alternative exhaustification in UE episodic context yields contradiction.
-/
theorem any_positive_episodic_bad : ufciGrammatical .positiveEpisodic = false := rfl

/--
The failure mechanism: exhaustification is G-contradictory.
(See Core.Analyticity for G-triviality/L-analyticity)
-/
theorem any_positive_contradiction : ufciReading .positiveEpisodic = none := rfl

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

-- Verify all grammaticality predictions match
example : anyExamples.all (λ ex => ex.grammatical == ufciGrammatical ex.context) := by decide

end Phenomena.Polarity.Studies.Chierchia2013
