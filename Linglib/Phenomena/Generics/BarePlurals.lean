/-
# Bare Plurals: Generic vs Existential Interpretation

Theory-neutral data on when bare plurals receive generic vs existential readings, focusing on information structure effects.

## Main definitions

`PredicateLevel`, `LocativeStatus`, `Presuppositionality`, `BarePluralDatum`, `SLevelDatum`, `PresuppositionalDatum`, `InformationStatus`, `TopicFocusDatum`, `IncorporationDatum`

## References

- Cohen & Erteschik-Shir (2002), Carlson (1977), Kratzer (1995), Diesing (1992)
-/

namespace Phenomena.BarePlurals

-- Predicate Classification

/-- Stage vs individual level predicates. -/
inductive PredicateLevel where
  | individual
  | stage
  deriving Repr, DecidableEq, BEq

/-- Locative argument vs adjunct status. -/
inductive LocativeStatus where
  | argument
  | adjunct
  | none
  deriving Repr, DecidableEq, BEq

/-- Presuppositional vs non-presuppositional verbs. -/
inductive Presuppositionality where
  | presuppositional
  | nonPresuppositional
  deriving Repr, DecidableEq, BEq

-- Basic Data Structure

/-- Bare plural interpretation datum. -/
structure BarePluralDatum where
  sentence : String
  predicateLevel : PredicateLevel
  genericOK : Bool
  existentialOK : Bool
  notes : String

-- I-Level Predicates (§2.1)

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

-- S-Level Predicates with Locative Arguments (§2.2)

/-- S-level predicate with locative status. -/
structure SLevelDatum extends BarePluralDatum where
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

-- S-Level Predicates with Locative Adjuncts (§2.3)

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

-- Presuppositional Verbs (§3)

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

-- Topic-Focus Effects (§4)

/-- Information structure: topic vs focus. -/
inductive InformationStatus where
  | topic
  | focus
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

-- Semantic Incorporation (§5)

/-- Incorporation test datum. -/
structure IncorporationDatum where
  sentence1 : String
  sentence2 : String
  bpReading : String
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


/-- All I-level predicate examples. -/
def iLevelData : List BarePluralDatum :=
  [boysAreBrave, italiansGoodLooking, lawyersIntelligent]

def sLevelArgumentData : List SLevelDatum :=
  [boysArePresent, firemenAvailable, soldiersArrived]

def sLevelAdjunctData : List SLevelDatum :=
  [boysAreHungry, boysHungryInClassroom, studentsAreTired]

def presuppositionalData : List PresuppositionalDatum :=
  [johnHatesLawyers, johnRecognizesLawyers, johnNoticedLawyers,
   johnKnowsLawyers, johnOwnsHorses]
#guard iLevelData.all (λ d => !d.existentialOK)
#guard iLevelData.all (λ d => d.genericOK)
#guard sLevelArgumentData.all (λ d => d.existentialOK)
#guard sLevelAdjunctData.all (λ d => !d.existentialOK)
#guard presuppositionalData.filter (λ d => d.verbType == .presuppositional)
      |>.all (λ d => !d.existentialOK)
#guard presuppositionalData.filter (λ d => d.verbType == .nonPresuppositional)
      |>.all (λ d => d.existentialOK)

end Phenomena.BarePlurals
