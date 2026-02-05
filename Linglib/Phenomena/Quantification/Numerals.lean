/-
# Numeral Imprecision

Empirical patterns for imprecision in bare numerals. Round numerals (100, 50) permit imprecision; non-round numerals (99, 47) require exactness.

## Main definitions
- `RoundnessLevel`, `NumeralImprecisionDatum`, `RoundnessAsymmetryDatum`
- `NegationConstraintDatum`, `GameShowDatum`

## References
- Krifka (2007). Approximate interpretation.
- Solt (2014, 2018). Imprecise numerals.
- Solt & Waldon (2019). Numerals under negation.
- Solt (2023). Imprecision without homogeneity.
-/

namespace Phenomena.Quantification.Numerals


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

end Phenomena.Quantification.Numerals
