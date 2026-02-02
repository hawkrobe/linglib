/-
# Bare Plurals: Generic vs Existential Interpretation

Theory-neutral data about when bare plurals receive generic vs existential readings.

## Key Phenomena (Cohen & Erteschik-Shir 2002)

1. **Topic/Focus effect**: Topic BPs → generic, Focused BPs → existential
2. **I-level vs S-level predicates**: Predicate type affects available readings
3. **Stage topics**: Spatiotemporal locations license existential S-level BPs
4. **Presuppositional verbs**: Some verbs block existential BP readings
5. **Semantic incorporation**: Existential BPs are "incorporated" into predicates

## Core Generalization

The existential reading of a BP requires:
1. The BP to be **focused** (not topical), AND
2. Either (a) the predicate has a **locative argument** (not adjunct), OR
       (b) the subject position is a **stage topic** (spatiotemporal location)

## References

- Cohen, A. & Erteschik-Shir, N. (2002). Topic, Focus, and the Interpretation
  of Bare Plurals. Natural Language Semantics 10:125-165.
- Carlson, G.N. (1977). Reference to Kinds in English. PhD dissertation.
- Kratzer, A. (1995). Stage-Level and Individual-Level Predicates.
- Diesing, M. (1992). Indefinites. MIT Press.
-/

namespace Phenomena.BarePlurals

-- ============================================================================
-- Predicate Classification
-- ============================================================================

/-- Classification of predicates by Carlson's stage/individual level distinction -/
inductive PredicateLevel where
  | individual  -- I-level: permanent, characterizing properties (brave, tall, intelligent)
  | stage       -- S-level: temporary, episodic properties (hungry, present, available)
  deriving Repr, DecidableEq, BEq

/-- Whether a predicate has a locative as argument vs adjunct -/
inductive LocativeStatus where
  | argument   -- Location is syntactically selected (be present, be located, arrive)
  | adjunct    -- Location is an optional modifier (be hungry in the kitchen)
  | none       -- No locative
  deriving Repr, DecidableEq, BEq

/-- Whether a verb is presuppositional (requires familiarity with object) -/
inductive Presuppositionality where
  | presuppositional     -- hate, recognize, notice (presuppose object exists/is known)
  | nonPresuppositional  -- know, own, see (compatible with first introduction)
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Basic Data Structure
-- ============================================================================

/-- A bare plural interpretation datum -/
structure BarePluralDatum where
  /-- The sentence -/
  sentence : String
  /-- Predicate level -/
  predicateLevel : PredicateLevel
  /-- Whether generic reading is available -/
  genericOK : Bool
  /-- Whether existential reading is available -/
  existentialOK : Bool
  /-- Source and notes -/
  notes : String

-- ============================================================================
-- I-Level Predicates (§2.1)
-- ============================================================================

/-!
## Individual-Level Predicates

I-level predicates characterize individuals as a whole, not stages.
With BP subjects, they ONLY allow generic readings.

"Boys are brave" can only mean: In general, boys have the property of being brave.
It cannot mean: There exist some boys (in some location) who are brave.
-/

/-- "Boys are brave" - I-level predicate, generic only -/
def boysAreBrave : BarePluralDatum :=
  { sentence := "Boys are brave"
  , predicateLevel := .individual
  , genericOK := true
  , existentialOK := false
  , notes := "I-level predicate forces generic. Cohen & Erteschik-Shir 2002 §2.1"
  }

/-- "Italians are good-looking" -/
def italiansGoodLooking : BarePluralDatum :=
  { sentence := "Italians are good-looking"
  , predicateLevel := .individual
  , genericOK := true
  , existentialOK := false
  , notes := "I-level predicate. No existential: *There are good-looking Italians here"
  }

/-- "Lawyers are intelligent" -/
def lawyersIntelligent : BarePluralDatum :=
  { sentence := "Lawyers are intelligent"
  , predicateLevel := .individual
  , genericOK := true
  , existentialOK := false
  , notes := "I-level predicate forces generic"
  }

-- ============================================================================
-- S-Level Predicates with Locative Arguments (§2.2)
-- ============================================================================

/-!
## S-Level Predicates with Locative Arguments

When an S-level predicate has a locative as a SYNTACTIC ARGUMENT (not adjunct),
the BP can get an existential reading.

"Boys are present" = There exist boys (here/now)
"Firemen are available" = There exist firemen (for the task)

The key is that the location provides a "stage topic" - a spatiotemporal
anchor for the existential claim.
-/

/-- Data for S-level predicates with locative status -/
structure SLevelDatum extends BarePluralDatum where
  /-- Is the locative an argument or adjunct? -/
  locativeStatus : LocativeStatus

/-- "Boys are present" - locative argument licenses existential -/
def boysArePresent : SLevelDatum :=
  { sentence := "Boys are present"
  , predicateLevel := .stage
  , genericOK := true
  , existentialOK := true  -- "There are boys here"
  , notes := "S-level with locative ARGUMENT. Cohen & Erteschik-Shir 2002 §2.2"
  , locativeStatus := .argument
  }

/-- "Firemen are available" - implicit locative argument -/
def firemenAvailable : SLevelDatum :=
  { sentence := "Firemen are available"
  , predicateLevel := .stage
  , genericOK := true
  , existentialOK := true
  , notes := "S-level with implicit locative argument (for some task/location)"
  , locativeStatus := .argument
  }

/-- "Soldiers arrived" - locative goal argument -/
def soldiersArrived : SLevelDatum :=
  { sentence := "Soldiers arrived"
  , predicateLevel := .stage
  , genericOK := true
  , existentialOK := true  -- "Some soldiers arrived (here)"
  , notes := "Motion verb with implicit goal argument"
  , locativeStatus := .argument
  }

-- ============================================================================
-- S-Level Predicates with Locative Adjuncts (§2.3)
-- ============================================================================

/-!
## S-Level Predicates WITHOUT Locative Arguments

When the locative is merely an ADJUNCT (optional modifier), the existential
reading is NOT available, even with S-level predicates.

"Boys are hungry" (no existential: *"There are hungry boys")
"Boys are hungry in the classroom" (still no existential!)

The location in "in the classroom" modifies the state, but doesn't provide
a stage topic for existential closure.
-/

/-- "Boys are hungry" - S-level but locative is adjunct -/
def boysAreHungry : SLevelDatum :=
  { sentence := "Boys are hungry"
  , predicateLevel := .stage
  , genericOK := true
  , existentialOK := false  -- No existential despite S-level!
  , notes := "S-level but no locative argument. Cohen & Erteschik-Shir 2002 §2.3"
  , locativeStatus := .adjunct
  }

/-- "Boys are hungry in the classroom" - adjunct doesn't help -/
def boysHungryInClassroom : SLevelDatum :=
  { sentence := "Boys are hungry in the classroom"
  , predicateLevel := .stage
  , genericOK := true
  , existentialOK := false
  , notes := "Even with explicit locative, still adjunct - no existential"
  , locativeStatus := .adjunct
  }

/-- "Students are tired" -/
def studentsAreTired : SLevelDatum :=
  { sentence := "Students are tired"
  , predicateLevel := .stage
  , genericOK := true
  , existentialOK := false
  , notes := "S-level but locative would be adjunct"
  , locativeStatus := .adjunct
  }

-- ============================================================================
-- Presuppositional Verbs (§3)
-- ============================================================================

/-!
## Presuppositional Verbs Block Existential Readings

Some verbs presuppose that the speaker has prior familiarity with the object.
These verbs BLOCK existential readings of BP objects.

"John hates lawyers" - generic only (lawyers as a kind)
"John recognizes lawyers" - generic only (*not "some lawyers he just met")

Contrast with non-presuppositional verbs:
"John knows lawyers" - existential OK ("John is acquainted with some lawyers")
-/

/-- Data for verb presuppositionality effects -/
structure PresuppositionalDatum where
  sentence : String
  verbType : Presuppositionality
  genericOK : Bool
  existentialOK : Bool
  notes : String

/-- "John hates lawyers" - presuppositional blocks existential -/
def johnHatesLawyers : PresuppositionalDatum :=
  { sentence := "John hates lawyers"
  , verbType := .presuppositional
  , genericOK := true
  , existentialOK := false
  , notes := "Presuppositional verb. Cohen & Erteschik-Shir 2002 §3"
  }

/-- "John recognizes lawyers" -/
def johnRecognizesLawyers : PresuppositionalDatum :=
  { sentence := "John recognizes lawyers"
  , verbType := .presuppositional
  , genericOK := true
  , existentialOK := false
  , notes := "Presuppositional - requires prior acquaintance"
  }

/-- "John noticed lawyers (at the party)" -/
def johnNoticedLawyers : PresuppositionalDatum :=
  { sentence := "John noticed lawyers at the party"
  , verbType := .presuppositional
  , genericOK := true
  , existentialOK := false
  , notes := "Presuppositional - notice presupposes object in visual field"
  }

/-- "John knows lawyers" - non-presuppositional allows existential -/
def johnKnowsLawyers : PresuppositionalDatum :=
  { sentence := "John knows lawyers"
  , verbType := .nonPresuppositional
  , genericOK := true
  , existentialOK := true  -- "John is acquainted with some lawyers"
  , notes := "Non-presuppositional. Cohen & Erteschik-Shir 2002 §3"
  }

/-- "John owns horses" -/
def johnOwnsHorses : PresuppositionalDatum :=
  { sentence := "John owns horses"
  , verbType := .nonPresuppositional
  , genericOK := true
  , existentialOK := true  -- "John owns some horses"
  , notes := "Non-presuppositional - allows first introduction"
  }

-- ============================================================================
-- Topic-Focus Effects (§4)
-- ============================================================================

/-!
## Topic vs Focus Determines Interpretation

The information-structural status of the BP determines its interpretation:

- **Topic BP** → GENERIC reading (characterizing statement about the kind)
- **Focus BP** → EXISTENTIAL reading (if other conditions met)

Test: "As for X, ..." (topicalization) vs "It is X that ..." (focus)

"As for dogs, John likes them" → generic (dogs in general)
"What John likes is dogs" → could be existential (specific dogs)
-/

/-- Information structure effect on interpretation -/
inductive InformationStatus where
  | topic  -- The BP is the topic of the sentence
  | focus  -- The BP is focused (new information)
  deriving Repr, DecidableEq, BEq

structure TopicFocusDatum where
  sentence : String
  bpStatus : InformationStatus
  genericOK : Bool
  existentialOK : Bool
  notes : String

/-- "As for lawyers, John hates them" - topicalized = generic -/
def asForLawyers : TopicFocusDatum :=
  { sentence := "As for lawyers, John hates them"
  , bpStatus := .topic
  , genericOK := true
  , existentialOK := false
  , notes := "Topic position forces generic. Cohen & Erteschik-Shir 2002 §4"
  }

/-- Default subject position is topic-like -/
def lawyersDefaultSubject : TopicFocusDatum :=
  { sentence := "Lawyers are greedy"
  , bpStatus := .topic  -- Subject is default topic
  , genericOK := true
  , existentialOK := false
  , notes := "Unmarked subject = topic = generic"
  }

-- ============================================================================
-- Semantic Incorporation (§5)
-- ============================================================================

/-!
## Semantic Incorporation

Existential bare plurals are semantically INCORPORATED into the predicate.
They do not introduce a discourse referent.

Evidence: Cannot be antecedent for pronouns across sentences.

"John owns horses. *They are in the barn." (horses = incorporated, no referent)
"John owns some horses. They are in the barn." (some = referent introduced)

This explains why existential BPs are restricted: they are part of the
predicate meaning, not independent referring expressions.
-/

/-- Incorporation test: can the BP antecede a pronoun? -/
structure IncorporationDatum where
  sentence1 : String
  sentence2 : String  -- Continuation with pronoun
  /-- Is the BP reading existential or generic? -/
  bpReading : String
  /-- Is anaphora acceptable? -/
  anaphoraOK : Bool
  notes : String

/-- "John owns horses. *They are in the barn." -/
def horsesIncorporated : IncorporationDatum :=
  { sentence1 := "John owns horses"
  , sentence2 := "They are in the barn"
  , bpReading := "existential"
  , anaphoraOK := false
  , notes := "Existential BP is incorporated - no discourse referent"
  }

/-- "John owns some horses. They are in the barn." -/
def someHorsesReferent : IncorporationDatum :=
  { sentence1 := "John owns some horses"
  , sentence2 := "They are in the barn"
  , bpReading := "existential"
  , anaphoraOK := true
  , notes := "Explicit indefinite introduces discourse referent"
  }

/-- "Dogs are mammals. They nurse their young." - kind anaphora OK -/
def dogsKindAnaphora : IncorporationDatum :=
  { sentence1 := "Dogs are mammals"
  , sentence2 := "They nurse their young"
  , bpReading := "generic/kind"
  , anaphoraOK := true
  , notes := "Kind-referring BP can antecede kind-level pronoun"
  }

-- ============================================================================
-- Summary: The Core Generalization
-- ============================================================================

/-!
## Cohen & Erteschik-Shir's Core Generalization

**Existential readings of BPs require:**

1. The BP must be **focused** (not the sentence topic)

2. AND one of:
   - (a) The predicate selects a **locative argument** (be present, arrive)
   - (b) There is a **stage topic** (spatiotemporal anchor for the event)

3. AND the verb must be **non-presuppositional**

**Otherwise:** The BP receives a **generic** reading.

This explains the classic puzzle: Why can "Boys are present" have an existential
reading but not "Boys are hungry"?

- "present" selects a locative argument (here/there/at this place)
- "hungry" takes locatives only as adjuncts

The locative argument provides the "stage topic" that licenses existential closure.

## Theoretical Implications

For **Local RSA + covert operator elimination**:

1. The generic/existential choice is NOT a matter of covert GEN/∃ insertion
2. It follows from **information structure** (topic/focus) + **predicate class**
3. Local RSA can model this as: prior over interpretations is conditioned on
   predicate type and information structure
4. This supports treating GEN as pragmatic epiphenomenon, not covert syntax

## Connection to Tessler & Goodman (2019)

T&G's threshold semantics gives the DENOTATION for the generic reading.
Cohen & Erteschik-Shir explain WHEN each reading is available.

Together: Local RSA selects between readings based on:
- Information structure (topic/focus from sentence position)
- Predicate class (I-level/S-level, locative argument status)
- Verb semantics (presuppositional or not)

The prior P(generic | predicate_class, info_structure) captures these effects.
-/

-- ============================================================================
-- Aggregate Data for Testing
-- ============================================================================

/-- All I-level predicate examples -/
def iLevelData : List BarePluralDatum :=
  [boysAreBrave, italiansGoodLooking, lawyersIntelligent]

/-- All S-level with locative argument examples -/
def sLevelArgumentData : List SLevelDatum :=
  [boysArePresent, firemenAvailable, soldiersArrived]

/-- All S-level with locative adjunct examples -/
def sLevelAdjunctData : List SLevelDatum :=
  [boysAreHungry, boysHungryInClassroom, studentsAreTired]

/-- All presuppositional verb examples -/
def presuppositionalData : List PresuppositionalDatum :=
  [johnHatesLawyers, johnRecognizesLawyers, johnNoticedLawyers,
   johnKnowsLawyers, johnOwnsHorses]

-- ============================================================================
-- Empirical Tests
-- ============================================================================

-- All I-level predicates should block existential
#guard iLevelData.all (fun d => !d.existentialOK)

-- All I-level predicates should allow generic
#guard iLevelData.all (fun d => d.genericOK)

-- S-level with locative arguments should allow existential
#guard sLevelArgumentData.all (fun d => d.existentialOK)

-- S-level with locative adjuncts should block existential
#guard sLevelAdjunctData.all (fun d => !d.existentialOK)

-- Presuppositional verbs block existential
#guard presuppositionalData.filter (fun d => d.verbType == .presuppositional)
      |>.all (fun d => !d.existentialOK)

-- Non-presuppositional verbs allow existential
#guard presuppositionalData.filter (fun d => d.verbType == .nonPresuppositional)
      |>.all (fun d => d.existentialOK)

end Phenomena.BarePlurals
