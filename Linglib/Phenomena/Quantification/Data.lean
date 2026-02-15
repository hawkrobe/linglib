/-
# Quantification Phenomena — Data

Theory-neutral empirical data on quantifier scope and numeral semantics.

## Sections
- `ScopeFreezing`: Configurations where inverse scope becomes unavailable
- `Numerals`: Imprecision patterns in bare numerals
- `ScopeWordOrder`: Word order effects on scope in verb-final constructions

## References
- May (1985). Logical Form.
- Larson (1988). On the double object construction.
- Bruening (2001). QR obeys Superiority.
- Antonyuk (2015). Quantifier scope and scope freezing in Russian.
- Scontras et al. (2014, 2017). Experimental studies on scope ambiguity.
- Krifka (2007). Approximate interpretation.
- Solt (2014, 2018). Imprecise numerals.
- Solt & Waldon (2019). Numerals under negation.
- Solt (2023). Imprecision without homogeneity.
- Bayer (1990, 1996). German scope restrictions.
- Haegeman & van Riemsdijk (1986). West Flemish.
- Steedman (2000). The Syntactic Process, Chapter 6.
- Kayne (1983, 1998). Scope and word order.
-/

namespace Phenomena.Quantification.Data

-- ============================================================================
-- § Scope Freezing
-- ============================================================================

section ScopeFreezing

/-- Available scope readings for a sentence -/
inductive Availability where
  | ambiguous     -- Both surface and inverse available
  | surfaceOnly   -- Only surface scope (inverse frozen)
  | inverseOnly   -- Only inverse scope (rare)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Confidence in the judgment -/
inductive Confidence where
  | clear         -- Native speakers agree (but introspective)
  | gradient      -- Some variation / context-dependent
  | controversial -- Theoretical disagreement
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Source of the judgment -/
inductive DataSource where
  | introspective   -- Linguist intuition (no experimental data)
  | experimental    -- Controlled experiment with ratings
  | corpus          -- Corpus-based evidence
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Types of configurations that induce scope freezing -/
inductive FreezingContext where
  | none              -- No freezing context (baseline ambiguous)
  | possessor         -- "A student's teacher..."
  | doubleObject      -- "gave NP NP" vs "gave NP to NP"
  | passive           -- "was V-ed by NP"
  | heavyNP           -- Complex/heavy NP in subject
  | weakCrossover     -- Bound variable blocks inverse
  | adjunct           -- Adjunct scope interactions
  | attitude          -- Attitude verb complements
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A scope freezing example with empirical judgment -/
structure Example where
  id : String
  sentence : String
  quant1 : String
  quant2 : String
  context : FreezingContext
  observed : Availability
  confidence : Confidence := .clear
  source : DataSource := .introspective
  surfaceGloss : String := ""
  inverseGloss : String := ""
  notes : String := ""
  deriving Repr


-- Possessor Freezing

def possessor_baseline : Example :=
  { id := "poss-1a"
  , sentence := "A student attended every seminar."
  , quant1 := "a student"
  , quant2 := "every seminar"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "There's a student who attended every seminar"
  , inverseGloss := "For every seminar, some student attended it"
  , notes := "Baseline: both readings available" }

def possessor_frozen : Example :=
  { id := "poss-1b"
  , sentence := "A student's teacher attended every seminar."
  , quant1 := "a student's teacher"
  , quant2 := "every seminar"
  , context := .possessor
  , observed := .surfaceOnly
  , confidence := .clear
  , surfaceGloss := "There's a student whose teacher attended every seminar"
  , inverseGloss := "*For every seminar, some student's teacher attended it"
  , notes := "Possessor freezes scope" }

def possessor_variant1 : Example :=
  { id := "poss-2a"
  , sentence := "Someone from every city was present."
  , quant1 := "someone from every city"
  , quant2 := "every city"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "There's someone who is from every city (impossible)"
  , inverseGloss := "For every city, someone from it was present"
  , notes := "Inverse scope is the sensible reading" }

def possessor_variant2 : Example :=
  { id := "poss-2b"
  , sentence := "Someone's friend from every city was present."
  , quant1 := "someone's friend"
  , quant2 := "every city"
  , context := .possessor
  , observed := .surfaceOnly
  , confidence := .gradient
  , notes := "Possessor blocks inverse; sentence is odd" }


-- Double Object Freezing

def dative_baseline : Example :=
  { id := "dat-1a"
  , sentence := "Someone gave a book to every student."
  , quant1 := "someone"
  , quant2 := "every student"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "There's someone who gave a book to every student"
  , inverseGloss := "For every student, someone gave them a book"
  , notes := "PP dative: ambiguous" }

def dative_frozen : Example :=
  { id := "dat-1b"
  , sentence := "Someone gave every student a book."
  , quant1 := "someone"
  , quant2 := "every student"
  , context := .doubleObject
  , observed := .surfaceOnly
  , confidence := .clear
  , surfaceGloss := "There's someone who gave every student a book"
  , inverseGloss := "*For every student, someone gave them a book"
  , notes := "Double object: frozen (Barss & Lasnik 1986)" }

def dative_variant : Example :=
  { id := "dat-2"
  , sentence := "A teacher showed every student a new problem."
  , quant1 := "a teacher"
  , quant2 := "every student"
  , context := .doubleObject
  , observed := .surfaceOnly
  , confidence := .clear
  , notes := "Double object freezes subject-IO scope" }


-- Passive Freezing

def passive_baseline : Example :=
  { id := "pass-1a"
  , sentence := "Every professor saw a student."
  , quant1 := "every professor"
  , quant2 := "a student"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "For every professor, they saw a (possibly different) student"
  , inverseGloss := "There's a student that every professor saw"
  , notes := "Active: ambiguous" }

def passive_frozen : Example :=
  { id := "pass-1b"
  , sentence := "A student was seen by every professor."
  , quant1 := "a student"
  , quant2 := "every professor"
  , context := .passive
  , observed := .surfaceOnly
  , confidence := .gradient
  , surfaceGloss := "There's a student that every professor saw"
  , inverseGloss := "?For every professor, some student was seen by them"
  , notes := "Passive: frozen (but judgments vary)" }

def passive_variant : Example :=
  { id := "pass-2"
  , sentence := "Someone was interviewed by every committee."
  , quant1 := "someone"
  , quant2 := "every committee"
  , context := .passive
  , observed := .surfaceOnly
  , confidence := .gradient
  , notes := "by-phrase scope is limited" }


-- Heavy NP Effects

def heavy_baseline : Example :=
  { id := "heavy-1a"
  , sentence := "A man read every book."
  , quant1 := "a man"
  , quant2 := "every book"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , notes := "Simple subject: ambiguous" }

def heavy_frozen : Example :=
  { id := "heavy-1b"
  , sentence := "A man who was sitting in the corner read every book."
  , quant1 := "a man who was sitting in the corner"
  , quant2 := "every book"
  , context := .heavyNP
  , observed := .surfaceOnly
  , confidence := .gradient
  , notes := "Heavy subject: inverse scope degraded" }


-- Weak Crossover and Scope

def crossover_baseline : Example :=
  { id := "wco-1a"
  , sentence := "Someone loves every city."
  , quant1 := "someone"
  , quant2 := "every city"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , notes := "No bound variable: ambiguous" }

def crossover_frozen : Example :=
  { id := "wco-1b"
  , sentence := "Someone from it loves every city."
  , quant1 := "someone from it"
  , quant2 := "every city"
  , context := .weakCrossover
  , observed := .surfaceOnly
  , confidence := .clear
  , surfaceGloss := "There's someone from some city who loves every city"
  , inverseGloss := "*For every city_i, someone from it_i loves it_i"
  , notes := "Bound pronoun blocks QR (weak crossover)" }


-- Attitude Verb Scope

def attitude_frozen : Example :=
  { id := "att-1"
  , sentence := "Someone believes that every student passed."
  , quant1 := "someone"
  , quant2 := "every student"
  , context := .attitude
  , observed := .surfaceOnly
  , confidence := .gradient
  , surfaceGloss := "Someone believes the proposition 'every student passed'"
  , inverseGloss := "?For every student, someone believes they passed"
  , notes := "Embedded universal can't easily scope over matrix" }

-- Collected Data

def possessorExamples : List Example :=
  [possessor_baseline, possessor_frozen, possessor_variant1, possessor_variant2]

def doubleObjectExamples : List Example :=
  [dative_baseline, dative_frozen, dative_variant]

def passiveExamples : List Example :=
  [passive_baseline, passive_frozen, passive_variant]

def heavyNPExamples : List Example :=
  [heavy_baseline, heavy_frozen]

def crossoverExamples : List Example :=
  [crossover_baseline, crossover_frozen]

def attitudeExamples : List Example :=
  [attitude_frozen]

def allExamples : List Example :=
  possessorExamples ++ doubleObjectExamples ++ passiveExamples ++
  heavyNPExamples ++ crossoverExamples ++ attitudeExamples

/-- Possessor freezing is robust (clear judgments) -/
def possessorFreezingIsClear : Bool :=
  possessor_frozen.confidence == .clear

/-- Double object freezing is robust -/
def doubleObjectFreezingIsClear : Bool :=
  dative_frozen.confidence == .clear

/-- Passive freezing is more gradient -/
def passiveFreezingIsGradient : Bool :=
  passive_frozen.confidence == .gradient

/-- Count frozen examples -/
def frozenCount : Nat :=
  allExamples.filter (·.observed == .surfaceOnly) |>.length

/-- Count ambiguous baselines -/
def ambiguousCount : Nat :=
  allExamples.filter (·.observed == .ambiguous) |>.length

#eval frozenCount      -- 9
#eval ambiguousCount   -- 6

end ScopeFreezing


-- ============================================================================
-- § Numeral Imprecision
-- ============================================================================

section Numerals

/-- Roundness level of a numeral. -/
inductive RoundnessLevel where
  | exact       -- 99, 47, 1003
  | round1      -- 100, 50 (divisible by 10)
  | round2      -- 1000, 500 (divisible by 100)
  | round3      -- 10000 (divisible by 1000)
  deriving Repr, DecidableEq

/-- Classify numeral roundness. -/
def classifyRoundness (n : Nat) : RoundnessLevel :=
  if n % 1000 = 0 then .round3
  else if n % 100 = 0 then .round2
  else if n % 10 = 0 then .round1
  else .exact


/-- Numeral imprecision datum: context-dependent exactness. -/
structure NumeralImprecisionDatum where
  numeral : Nat
  roundness : RoundnessLevel
  sentenceFrame : String
  exactContext : String
  inexactContext : String
  actualValue : Nat
  acceptableExact : Bool
  acceptableInexact : Bool
  deriving Repr

/-- The cars scenario. -/
def carsExact : NumeralImprecisionDatum :=
  { numeral := 100
  , roundness := .round2
  , sentenceFrame := "This guy owns _ cars."
  , exactContext := "Tax rate depends on owning exactly 100+ cars"
  , inexactContext := "Discussing extreme wealth (exact count irrelevant)"
  , actualValue := 98
  , acceptableExact := false   -- misleading about tax status
  , acceptableInexact := true  -- 98 ≈ 100 for wealth signaling
  }

def carsNonRound : NumeralImprecisionDatum :=
  { numeral := 99
  , roundness := .exact
  , sentenceFrame := "This guy owns _ cars."
  , exactContext := "Tax rate depends on owning exactly 100+ cars"
  , inexactContext := "Discussing extreme wealth (exact count irrelevant)"
  , actualValue := 98
  , acceptableExact := false
  , acceptableInexact := false  -- 99 requires exact reading even here
  }


/-- Minimal pair showing round/non-round asymmetry. -/
structure RoundnessAsymmetryDatum where
  roundNumeral : Nat
  nonRoundNumeral : Nat
  context : String
  actualValue : Nat
  roundAcceptable : Bool
  nonRoundAcceptable : Bool
  deriving Repr

def hundredVsNinetyNine : RoundnessAsymmetryDatum :=
  { roundNumeral := 100
  , nonRoundNumeral := 99
  , context := "Casual conversation about someone's car collection"
  , actualValue := 98
  , roundAcceptable := true    -- "100 cars" OK when actual is 98
  , nonRoundAcceptable := false -- "99 cars" requires exactly 99
  }

def fiftyVsFortyNine : RoundnessAsymmetryDatum :=
  { roundNumeral := 50
  , nonRoundNumeral := 49
  , context := "Estimating crowd size at event"
  , actualValue := 47
  , roundAcceptable := true
  , nonRoundAcceptable := false
  }


/-- Numerals under negation require polar questions. -/
structure NegationConstraintDatum where
  positiveSentence : String
  negativeSentence : String
  howManyContext : String
  polarContext : String
  negativeOkHowMany : Bool
  negativeOkPolar : Bool
  deriving Repr

def sheepNegation : NegationConstraintDatum :=
  { positiveSentence := "She has 40 sheep."
  , negativeSentence := "She doesn't have 40 sheep."
  , howManyContext := "A: How many sheep does Lisa have?"
  , polarContext := "A: Does Lisa really have 40 sheep?"
  , negativeOkHowMany := false  -- degraded as answer to how-many
  , negativeOkPolar := true     -- fine as answer to polar question
  }


/-- Game show scenario testing for homogeneity gaps. -/
structure GameShowDatum where
  sentence : String
  scenario : String
  exactReadingTrue : Bool
  inexactReadingTrue : Bool
  acceptable : Bool
  speakersAgree : Bool
  notes : String
  deriving Repr

def gameShowPositive : GameShowDatum :=
  { sentence := "Bei diesem Spiel hat heute jeder 200 Münzen gesammelt."
              -- "In this game, everyone collected 200 coins today."
  , scenario := "Game: collect exactly 200 coins → €250 prize; approximately 200 → €50. All participants collected amounts like 195, 198, 203, 205 (close but not exact). All won €50."
  , exactReadingTrue := false   -- no one got exactly 200
  , inexactReadingTrue := true  -- everyone got approximately 200
  , acceptable := true          -- some speakers accept (inexact reading)
  , speakersAgree := false      -- speakers disagree on judgment
  , notes := "Unlike plurals, speakers don't report 'neither true nor false' - they pick exact or inexact reading"
  }

def gameShowNegative : GameShowDatum :=
  { sentence := "Bei diesem Spiel hat heute niemand 200 Münzen gesammelt."
              -- "In this game, nobody collected 200 coins today."
  , scenario := "Same as above"
  , exactReadingTrue := true    -- no one got exactly 200
  , inexactReadingTrue := false -- everyone got approximately 200
  , acceptable := true          -- some speakers accept (exact reading)
  , speakersAgree := false
  , notes := "Complementary to positive - one is true depending on reading"
  }


/-- "Exactly" removes imprecision. -/
structure ExactlyModifierDatum where
  bareSentence : String
  exactlySentence : String
  context : String
  actualValue : Nat
  bareAcceptable : Bool
  exactlyAcceptable : Bool
  deriving Repr

def exactlyRemovesImprecision : ExactlyModifierDatum :=
  { bareSentence := "Ann owns 100 cars."
  , exactlySentence := "Ann owns exactly 100 cars."
  , context := "Casual conversation about wealth"
  , actualValue := 98
  , bareAcceptable := true     -- imprecise reading available
  , exactlyAcceptable := false -- "exactly" forces precise reading
  }


/-- "Approximately" makes imprecision explicit. -/
structure ApproximatelyDatum where
  bareSentence : String
  approxSentence : String
  roundness : RoundnessLevel
  approxNatural : Bool
  notes : String
  deriving Repr

def approximatelyWithRound : ApproximatelyDatum :=
  { bareSentence := "Ann owns 100 cars."
  , approxSentence := "Ann owns approximately 100 cars."
  , roundness := .round2
  , approxNatural := true
  , notes := "Natural: makes existing imprecision explicit"
  }

def approximatelyWithNonRound : ApproximatelyDatum :=
  { bareSentence := "Ann owns 99 cars."
  , approxSentence := "Ann owns approximately 99 cars."
  , roundness := .exact
  , approxNatural := false  -- or at least marked
  , notes := "Odd/marked: why approximate to a non-round number?"
  }


/-- Time expressions show round/non-round patterns. -/
structure TimeExpressionDatum where
  sentence : String
  timeExpression : String
  round : Bool
  scenario : String
  actualTime : String
  acceptable : Bool
  deriving Repr

def arriveAt3 : TimeExpressionDatum :=
  { sentence := "Anna arrived at 3 o'clock."
  , timeExpression := "3 o'clock"
  , round := true
  , scenario := "Students should arrive at 3; penalties for early/late"
  , actualTime := "2:58"
  , acceptable := true  -- "3 o'clock" permits slight imprecision
  }

def arriveAt258 : TimeExpressionDatum :=
  { sentence := "Anna arrived at 2:58."
  , timeExpression := "2:58"
  , round := false
  , scenario := "Same as above"
  , actualTime := "2:56"
  , acceptable := false  -- non-round requires exact time
  }


/-- Granularity affects which numerals count as "round." -/
structure GranularityDatum where
  numeral : Nat
  coarseScale : String
  roundOnCoarse : Bool
  fineScale : String
  roundOnFine : Bool
  deriving Repr

def granularityExample : GranularityDatum :=
  { numeral := 48
  , coarseScale := "Dozens (12, 24, 36, 48, ...)"
  , roundOnCoarse := true   -- 4 dozen
  , fineScale := "Units (1, 2, 3, ...)"
  , roundOnFine := false    -- not divisible by 10
  }


/-- Core empirical generalizations about numeral imprecision. -/
structure NumeralImprecisionGeneralizations where
  roundPermitsImprecision : Bool
  nonRoundRequiresExact : Bool
  exactlyRemoves : Bool
  negationRequiresPolar : Bool
  noHomogeneityGaps : Bool
  contextSensitive : Bool
  deriving Repr

def mainGeneralizations : NumeralImprecisionGeneralizations :=
  { roundPermitsImprecision := true
  , nonRoundRequiresExact := true
  , exactlyRemoves := true
  , negationRequiresPolar := true
  , noHomogeneityGaps := true  -- disputed, but apparent
  , contextSensitive := true
  }

-- Collections

def carsExamples : List NumeralImprecisionDatum :=
  [carsExact, carsNonRound]

def roundnessAsymmetryExamples : List RoundnessAsymmetryDatum :=
  [hundredVsNinetyNine, fiftyVsFortyNine]

def gameShowExamples : List GameShowDatum :=
  [gameShowPositive, gameShowNegative]

end Numerals


-- ============================================================================
-- § Scope-Word Order Interactions
-- ============================================================================

section ScopeWordOrder

/-- Word order patterns in verb-final constructions. -/
inductive VerbOrder where
  | verbRaising          -- NP ... V_emb V_matrix (object precedes all verbs)
  | verbProjectionRaising -- V_matrix ... NP V_emb (object follows matrix verb)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Whether a word order blocks inverse scope -/
def blocksInverseScope : VerbOrder → Bool
  | .verbRaising => false          -- allows both readings
  | .verbProjectionRaising => true -- blocks inverse scope

/-- Available scope readings for a sentence. -/
inductive ScopeAvailability where
  | surfaceOnly  -- Only ∃>∀ or ∀>¬ (whichever is surface)
  | ambiguous    -- Both readings available
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Convert word order to scope availability -/
def wordOrderToAvailability : VerbOrder → ScopeAvailability
  | .verbRaising => .ambiguous
  | .verbProjectionRaising => .surfaceOnly

/-- German sentence data from Bayer/Kayne. -/
structure GermanScopeExample where
  surface : String
  translation : String
  wordOrder : VerbOrder
  observed : ScopeAvailability
  deriving Repr

def german_96 : GermanScopeExample :=
  { surface := "(Weil) irgendjemand auf jeden gespannt ist"
  , translation := "Since someone is curious about everybody"
  , wordOrder := .verbRaising
  , observed := .ambiguous }

def german_97 : GermanScopeExample :=
  { surface := "(Weil) jemand versucht hat jeden reinzulegen"
  , translation := "Since someone has tried to cheat everyone"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly }

/-- West Flemish data from Haegeman & van Riemsdijk (1986). -/
structure WestFlemishScopeExample where
  surface : String
  translation : String
  wordOrder : VerbOrder
  observed : ScopeAvailability
  deriving Repr

def westFlemish_98a : WestFlemishScopeExample :=
  { surface := "(da) Jan vee boeken hee willen lezen"
  , translation := "that Jan wanted to read many books"
  , wordOrder := .verbRaising
  , observed := .ambiguous }

def westFlemish_98b : WestFlemishScopeExample :=
  { surface := "(da) Jan hee willen vee boeken lezen"
  , translation := "that Jan wanted to read many books"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly }

/-- Dutch equi verb data from Steedman (2000). -/
structure DutchScopeExample where
  surface : String
  translation : String
  wordOrder : VerbOrder
  observed : ScopeAvailability
  quantifiers : List String := []
  deriving Repr

def dutch_99a : DutchScopeExample :=
  { surface := "(omdat) Jan veel liederen probeert te zingen"
  , translation := "because Jan tries to sing many songs"
  , wordOrder := .verbRaising
  , observed := .ambiguous
  , quantifiers := ["veel/many"] }

def dutch_99b : DutchScopeExample :=
  { surface := "(omdat) Jan probeert veel liederen te zingen"
  , translation := "because Jan tries to sing many songs"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly
  , quantifiers := ["veel/many"] }

def dutch_100a : DutchScopeExample :=
  { surface := "(omdat) iemand alle liederen probeert te zingen"
  , translation := "because someone tries to sing every song"
  , wordOrder := .verbRaising
  , observed := .ambiguous
  , quantifiers := ["iemand/someone", "alle/every"] }

def dutch_100b : DutchScopeExample :=
  { surface := "(omdat) iemand probeert alle liederen te zingen"
  , translation := "because someone tries to sing every song"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly
  , quantifiers := ["iemand/someone", "alle/every"] }

-- Collected Data

def allDutchExamples : List DutchScopeExample :=
  [dutch_99a, dutch_99b, dutch_100a, dutch_100b]

def allWestFlemishExamples : List WestFlemishScopeExample :=
  [westFlemish_98a, westFlemish_98b]

def allGermanExamples : List GermanScopeExample :=
  [german_96, german_97]

/-- Word order correctly predicts scope availability -/
theorem wordOrder_predicts_dutch_99a :
    wordOrderToAvailability dutch_99a.wordOrder = dutch_99a.observed := rfl

theorem wordOrder_predicts_dutch_99b :
    wordOrderToAvailability dutch_99b.wordOrder = dutch_99b.observed := rfl

theorem wordOrder_predicts_dutch_100a :
    wordOrderToAvailability dutch_100a.wordOrder = dutch_100a.observed := rfl

theorem wordOrder_predicts_dutch_100b :
    wordOrderToAvailability dutch_100b.wordOrder = dutch_100b.observed := rfl

theorem wordOrder_predicts_german_96 :
    wordOrderToAvailability german_96.wordOrder = german_96.observed := rfl

theorem wordOrder_predicts_german_97 :
    wordOrderToAvailability german_97.wordOrder = german_97.observed := rfl

end ScopeWordOrder

end Phenomena.Quantification.Data
