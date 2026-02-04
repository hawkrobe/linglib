/-
# Numeral Imprecision: Empirical Data

Theory-neutral empirical patterns for imprecision in bare numerals.

## Phenomena Covered

1. **Round vs non-round asymmetry**: 100 permits imprecision, 99 doesn't
2. **Context-sensitivity**: Same numeral, exact vs inexact readings
3. **Negation constraint**: Numerals under negation require polar questions
4. **Lack of homogeneity gaps**: Unlike plurals, numerals don't show clear gaps

## Key Puzzle

Round numerals (100, 50, 1000) permit imprecise readings, but non-round numerals
(99, 47, 1003) require exact readings. This asymmetry is systematic across languages.

## Key References

- Krifka (2007): Approximate interpretation
- Sauerland & Stateva (2007): Scalar alternatives for numerals
- Solt (2014, 2018): Imprecise numerals
- Solt & Waldon (2019): Numerals under negation
- Križ (2015): Numerals and homogeneity
- Solt (2023): Imprecision without homogeneity
-/

namespace Phenomena.Imprecision.Numerals


/--
Roundness level of a numeral.

More round = more potential for imprecision.

Source: Krifka (2007), Sauerland & Stateva (2007)
-/
inductive RoundnessLevel where
  | exact       -- 99, 47, 1003
  | round1      -- 100, 50 (divisible by 10)
  | round2      -- 1000, 500 (divisible by 100)
  | round3      -- 10000 (divisible by 1000)
  deriving Repr, DecidableEq

/--
Classify numeral roundness (simplified).
-/
def classifyRoundness (n : Nat) : RoundnessLevel :=
  if n % 1000 = 0 then .round3
  else if n % 100 = 0 then .round2
  else if n % 10 = 0 then .round1
  else .exact


/--
Numeral imprecision datum: context-dependent exactness.
-/
structure NumeralImprecisionDatum where
  /-- The numeral -/
  numeral : Nat
  /-- Roundness level -/
  roundness : RoundnessLevel
  /-- Sentence frame -/
  sentenceFrame : String
  /-- Context favoring exact reading -/
  exactContext : String
  /-- Context favoring inexact reading -/
  inexactContext : String
  /-- Actual value in scenario -/
  actualValue : Nat
  /-- Acceptable in exact context? -/
  acceptableExact : Bool
  /-- Acceptable in inexact context? -/
  acceptableInexact : Bool
  deriving Repr

/--
The CARS scenario from the dissertation.

Source: dissertation (19), (20)
-/
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


/--
Minimal pair showing round/non-round asymmetry.
-/
structure RoundnessAsymmetryDatum where
  /-- Round numeral -/
  roundNumeral : Nat
  /-- Non-round numeral -/
  nonRoundNumeral : Nat
  /-- Context (same for both) -/
  context : String
  /-- Actual value -/
  actualValue : Nat
  /-- Round numeral acceptable? -/
  roundAcceptable : Bool
  /-- Non-round acceptable? -/
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


/--
Numerals under negation require polar questions.

Source: Solt & Waldon (2019)
-/
structure NegationConstraintDatum where
  /-- Positive sentence -/
  positiveSentence : String
  /-- Negative sentence -/
  negativeSentence : String
  /-- "How many" question context -/
  howManyContext : String
  /-- Polar question context -/
  polarContext : String
  /-- Negative OK in how-many context? -/
  negativeOkHowMany : Bool
  /-- Negative OK in polar context? -/
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


/--
The game show scenario tests for homogeneity gaps.

Context makes both exact and inexact readings relevant.
If numerals had gaps like plurals, neither sentence should be clearly true.

Source: dissertation (164)
-/
structure GameShowDatum where
  /-- The sentence -/
  sentence : String
  /-- Scenario description -/
  scenario : String
  /-- Exact reading true? -/
  exactReadingTrue : Bool
  /-- Inexact reading true? -/
  inexactReadingTrue : Bool
  /-- Judgment: is sentence acceptable? -/
  acceptable : Bool
  /-- Do speakers agree? -/
  speakersAgree : Bool
  /-- Notes -/
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


/--
"Exactly" removes imprecision, parallel to "all" for plurals.

Source: dissertation (4)
-/
structure ExactlyModifierDatum where
  /-- Bare numeral sentence -/
  bareSentence : String
  /-- Modified sentence -/
  exactlySentence : String
  /-- Context -/
  context : String
  /-- Actual value -/
  actualValue : Nat
  /-- Bare acceptable? -/
  bareAcceptable : Bool
  /-- Exactly acceptable? -/
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


/--
"Approximately" explicitly marks imprecision.

Interesting: "approximately" doesn't ADD imprecision to a precise expression;
it makes imprecision explicit on an already-imprecise expression.

Source: dissertation (4)
-/
structure ApproximatelyDatum where
  /-- Bare sentence -/
  bareSentence : String
  /-- Approximately sentence -/
  approxSentence : String
  /-- Roundness of numeral -/
  roundness : RoundnessLevel
  /-- Is approximately acceptable with this numeral? -/
  approxNatural : Bool
  /-- Notes -/
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


/--
Time expressions show similar round/non-round patterns.

Source: dissertation (163), Solt (2023)
-/
structure TimeExpressionDatum where
  /-- The sentence -/
  sentence : String
  /-- Time expression -/
  timeExpression : String
  /-- Is it round? -/
  round : Bool
  /-- Scenario -/
  scenario : String
  /-- Exact arrival time -/
  actualTime : String
  /-- Sentence acceptable? -/
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


/--
Granularity affects which numerals count as "round."

E.g., on a scale of dozens, 48 might be "round" (4 dozen).

Source: Krifka (2007)
-/
structure GranularityDatum where
  /-- The numeral -/
  numeral : Nat
  /-- Coarse scale description -/
  coarseScale : String
  /-- Is numeral round on this scale? -/
  roundOnCoarse : Bool
  /-- Fine scale description -/
  fineScale : String
  /-- Is numeral round on this scale? -/
  roundOnFine : Bool
  deriving Repr

def granularityExample : GranularityDatum :=
  { numeral := 48
  , coarseScale := "Dozens (12, 24, 36, 48, ...)"
  , roundOnCoarse := true   -- 4 dozen
  , fineScale := "Units (1, 2, 3, ...)"
  , roundOnFine := false    -- not divisible by 10
  }


/--
Core empirical generalizations about numeral imprecision.
-/
structure NumeralImprecisionGeneralizations where
  /-- Round numerals permit imprecision -/
  roundPermitsImprecision : Bool
  /-- Non-round require exactness -/
  nonRoundRequiresExact : Bool
  /-- "Exactly" removes imprecision -/
  exactlyRemoves : Bool
  /-- Negation requires polar questions -/
  negationRequiresPolar : Bool
  /-- No clear homogeneity gaps (unlike plurals) -/
  noHomogeneityGaps : Bool
  /-- Imprecision is context-sensitive -/
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

-- Summary

/-
## What This Module Provides

### Data Types
- `RoundnessLevel`: Classification of numeral roundness
- `NumeralImprecisionDatum`: Context-dependent exactness
- `RoundnessAsymmetryDatum`: Round vs non-round contrast
- `NegationConstraintDatum`: Polar question requirement
- `GameShowDatum`: Homogeneity gap test
- `ExactlyModifierDatum`: Imprecision removal
- `ApproximatelyDatum`: Explicit imprecision marking
- `GranularityDatum`: Scale-relative roundness

### Key Findings
1. Round numerals (100) permit imprecision; non-round (99) don't
2. "Exactly" removes imprecision (parallel to "all" for plurals)
3. Numerals under negation require polar question contexts
4. Unlike plurals, numerals don't show clear homogeneity gaps
5. Roundness is scale-relative (granularity matters)

### Key References
- Krifka (2007), Sauerland & Stateva (2007)
- Solt (2014, 2018), Solt & Waldon (2019), Solt (2023)
- Križ (2015)
-/

end Phenomena.Imprecision.Numerals
