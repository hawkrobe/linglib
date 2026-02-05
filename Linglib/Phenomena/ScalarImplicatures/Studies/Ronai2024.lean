/-
# Ronai (2024) Embedded Scalar Diversity Data

Experimental data on embedded scalar implicatures from:
Ronai, E. (2024). Embedded scalar diversity. SALT 34, 110-131.

## Main Question

Do embedded scalar implicatures (under universal quantifiers) show the same
cross-scale variation ("scalar diversity") as global SIs? And do the same
properties of alternatives predict this variation?

## Findings

1. Embedded SIs arise: strong inferences like "Every soup was warm" →
   "No soup was hot" are computed by hearers.

2. Scalar diversity extends to embedded SIs: cross-scale variation in
   embedded SI rates parallels global SI variation (r=0.76-0.80).

3. Semantic distance and boundedness predict both global and embedded SI rates.

## Theoretical Implications

Results support alternative-based accounts of embedded SI:
- Grammatical theory (Chierchia 2004; Chierchia, Fox & Spector 2012)
- Modified neo-Gricean (Sauerland 2004)
- Neo-Gricean uncertainty RSA-LU (Potts et al. 2015)

Results are less compatible with:
- Unconstrained uncertainty RSA-LU (Bergen et al. 2016)

This is because the alternative-free unconstrained model cannot explain
why the same alternative-driven variation arises in both global and
embedded contexts.

## Connection to Geurts & Pouscoulous (2009)

This paper directly responds to G&P 2009 (also in Linglib), which found
limited evidence for embedded SIs. Ronai's methodology uses the Gotzner &
Romoli (2018) paradigm and tests 42 scales, finding robust embedded SIs
with predictable cross-scale variation.

## References

- Ronai, E. (2024). Embedded scalar diversity. SALT 34, 110-131.
- van Tiel, B., Van Miltenburg, E., Zevakhina, N., & Geurts, B. (2016).
  Scalar diversity. Journal of Semantics, 33(1), 137-175.
- Gotzner, N. & Romoli, J. (2018). The scalar inferences of strong scalar
  terms under negative quantifiers. Journal of Semantics, 35(1), 95-126.
- Bergen, L., Levy, R., & Goodman, N. (2016). Pragmatic reasoning through
  semantic inference. Semantics and Pragmatics, 9.
-/

import Mathlib.Data.Rat.Defs

namespace Phenomena.Ronai2024


/--
A lexical scale with properties from van Tiel et al. (2016) and
embedded SI data from Ronai (2024).
-/
structure ScaleDatum where
  /-- The weaker scalar term (e.g., "some", "warm") -/
  weakerTerm : String
  /-- The stronger scalar term (e.g., "all", "hot") -/
  strongerTerm : String
  /-- Semantic distance (1-7 Likert scale, from van Tiel et al. 2016 Exp 4) -/
  semanticDistance : Option Float
  /-- Is the scale bounded? (stronger term = endpoint) -/
  bounded : Bool
  /-- Global SI rate from van Tiel et al. (2016) Exp 2 (percentage 0-100) -/
  globalSIRate : Option Nat
  /-- Strong inference rate from Ronai (2024) Exp 1 (sliding scale 0-100) -/
  embeddedSIRate_Exp1 : Option Nat
  /-- Strong inference rate from Ronai (2024) Exp 2 (percentage Yes responses) -/
  embeddedSIRate_Exp2 : Option Nat
  deriving Repr

/-- Display name for a scale -/
def ScaleDatum.name (s : ScaleDatum) : String :=
  s!"⟨{s.weakerTerm}, {s.strongerTerm}⟩"


/-!
## Scale Data

Data extracted from Ronai (2024) Figures 2, 3, 5, 6 and van Tiel et al. (2016).
The 42 scales are from van Tiel et al.'s original study.

Semantic distance: 1 = "equally strong" to 7 = "much stronger"
Boundedness: true if stronger term denotes scale endpoint
-/

-- Quantifier scales (bounded)
def someAll : ScaleDatum :=
  { weakerTerm := "some", strongerTerm := "all"
  , semanticDistance := some 5.3
  , bounded := true
  , globalSIRate := some 89
  , embeddedSIRate_Exp1 := some 49
  , embeddedSIRate_Exp2 := some 44 }

-- Modal scales (bounded)
def possibleCertain : ScaleDatum :=
  { weakerTerm := "possible", strongerTerm := "certain"
  , semanticDistance := some 5.8
  , bounded := true
  , globalSIRate := some 81
  , embeddedSIRate_Exp1 := some 57
  , embeddedSIRate_Exp2 := some 64 }

def allowedObligatory : ScaleDatum :=
  { weakerTerm := "allowed", strongerTerm := "obligatory"
  , semanticDistance := some 5.2
  , bounded := true
  , globalSIRate := some 72
  , embeddedSIRate_Exp1 := some 56
  , embeddedSIRate_Exp2 := some 47 }

def mayHaveTo : ScaleDatum :=
  { weakerTerm := "may", strongerTerm := "have to"
  , semanticDistance := some 5.5
  , bounded := true
  , globalSIRate := some 72
  , embeddedSIRate_Exp1 := some 58
  , embeddedSIRate_Exp2 := some 53 }

def mayWill : ScaleDatum :=
  { weakerTerm := "may", strongerTerm := "will"
  , semanticDistance := some 6.2
  , bounded := true
  , globalSIRate := some 100
  , embeddedSIRate_Exp1 := some 18
  , embeddedSIRate_Exp2 := some 9 }

-- Frequency/temporal scales (bounded)
def sometimesAlways : ScaleDatum :=
  { weakerTerm := "sometimes", strongerTerm := "always"
  , semanticDistance := some 5.5
  , bounded := true
  , globalSIRate := some 69
  , embeddedSIRate_Exp1 := some 43
  , embeddedSIRate_Exp2 := some 38 }

-- Achievement scales (bounded)
def cheapFree : ScaleDatum :=
  { weakerTerm := "cheap", strongerTerm := "free"
  , semanticDistance := some 6.0
  , bounded := true
  , globalSIRate := some 94
  , embeddedSIRate_Exp1 := some 63
  , embeddedSIRate_Exp2 := some 51 }

def difficultImpossible : ScaleDatum :=
  { weakerTerm := "difficult", strongerTerm := "impossible"
  , semanticDistance := some 5.7
  , bounded := true
  , globalSIRate := some 67
  , embeddedSIRate_Exp1 := some 42
  , embeddedSIRate_Exp2 := some 33 }

def hardUnsolvable : ScaleDatum :=
  { weakerTerm := "hard", strongerTerm := "unsolvable"
  , semanticDistance := some 5.4
  , bounded := true
  , globalSIRate := some 50
  , embeddedSIRate_Exp1 := some 47
  , embeddedSIRate_Exp2 := some 27 }

def rareExtinct : ScaleDatum :=
  { weakerTerm := "rare", strongerTerm := "extinct"
  , semanticDistance := some 5.8
  , bounded := true
  , globalSIRate := some 64
  , embeddedSIRate_Exp1 := some 50
  , embeddedSIRate_Exp2 := some 38 }

def scarceUnavailable : ScaleDatum :=
  { weakerTerm := "scarce", strongerTerm := "unavailable"
  , semanticDistance := some 5.0
  , bounded := true
  , globalSIRate := some 44
  , embeddedSIRate_Exp1 := some 38
  , embeddedSIRate_Exp2 := some 24 }

def lowDepleted : ScaleDatum :=
  { weakerTerm := "low", strongerTerm := "depleted"
  , semanticDistance := some 5.2
  , bounded := true
  , globalSIRate := some 53
  , embeddedSIRate_Exp1 := some 44
  , embeddedSIRate_Exp2 := some 29 }

-- Process/result scales (bounded)
def startFinish : ScaleDatum :=
  { weakerTerm := "start", strongerTerm := "finish"
  , semanticDistance := some 4.7
  , bounded := true
  , globalSIRate := some 25
  , embeddedSIRate_Exp1 := some 24
  , embeddedSIRate_Exp2 := none }

def trySucceed : ScaleDatum :=
  { weakerTerm := "try", strongerTerm := "succeed"
  , semanticDistance := some 4.8
  , bounded := true
  , globalSIRate := some 42
  , embeddedSIRate_Exp1 := some 32
  , embeddedSIRate_Exp2 := some 18 }

def participateWin : ScaleDatum :=
  { weakerTerm := "participate", strongerTerm := "win"
  , semanticDistance := some 5.0
  , bounded := true
  , globalSIRate := some 17
  , embeddedSIRate_Exp1 := some 25
  , embeddedSIRate_Exp2 := some 4 }

-- Epistemic scales (bounded)
def believeKnow : ScaleDatum :=
  { weakerTerm := "believe", strongerTerm := "know"
  , semanticDistance := some 4.6
  , bounded := true
  , globalSIRate := some 47
  , embeddedSIRate_Exp1 := some 28
  , embeddedSIRate_Exp2 := some 9 }

-- Quality scales (bounded)
def goodPerfect : ScaleDatum :=
  { weakerTerm := "good", strongerTerm := "perfect"
  , semanticDistance := some 4.5
  , bounded := true
  , globalSIRate := some 39
  , embeddedSIRate_Exp1 := some 42
  , embeddedSIRate_Exp2 := some 20 }

def memorableUnforgettable : ScaleDatum :=
  { weakerTerm := "memorable", strongerTerm := "unforgettable"
  , semanticDistance := some 4.8
  , bounded := true
  , globalSIRate := some 42
  , embeddedSIRate_Exp1 := some 42
  , embeddedSIRate_Exp2 := some 42 }

def specialUnique : ScaleDatum :=
  { weakerTerm := "special", strongerTerm := "unique"
  , semanticDistance := some 4.0
  , bounded := true
  , globalSIRate := some 8
  , embeddedSIRate_Exp1 := some 11
  , embeddedSIRate_Exp2 := some 2 }

-- Temperature scales (non-bounded)
def warmHot : ScaleDatum :=
  { weakerTerm := "warm", strongerTerm := "hot"
  , semanticDistance := some 5.1
  , bounded := false
  , globalSIRate := some 50
  , embeddedSIRate_Exp1 := some 40
  , embeddedSIRate_Exp2 := some 31 }

def coolCold : ScaleDatum :=
  { weakerTerm := "cool", strongerTerm := "cold"
  , semanticDistance := some 4.4
  , bounded := false
  , globalSIRate := some 28
  , embeddedSIRate_Exp1 := some 29
  , embeddedSIRate_Exp2 := some 13 }

-- Evaluative scales (non-bounded)
def goodExcellent : ScaleDatum :=
  { weakerTerm := "good", strongerTerm := "excellent"
  , semanticDistance := some 4.6
  , bounded := false
  , globalSIRate := some 31
  , embeddedSIRate_Exp1 := some 38
  , embeddedSIRate_Exp2 := some 16 }

def adequateGood : ScaleDatum :=
  { weakerTerm := "adequate", strongerTerm := "good"
  , semanticDistance := some 3.5
  , bounded := false
  , globalSIRate := some 8
  , embeddedSIRate_Exp1 := some 35
  , embeddedSIRate_Exp2 := some 16 }

def palatableDelicious : ScaleDatum :=
  { weakerTerm := "palatable", strongerTerm := "delicious"
  , semanticDistance := some 5.3
  , bounded := false
  , globalSIRate := some 58
  , embeddedSIRate_Exp1 := some 36
  , embeddedSIRate_Exp2 := some 20 }

-- Size scales (non-bounded)
def bigEnormous : ScaleDatum :=
  { weakerTerm := "big", strongerTerm := "enormous"
  , semanticDistance := some 4.5
  , bounded := false
  , globalSIRate := some 14
  , embeddedSIRate_Exp1 := some 22
  , embeddedSIRate_Exp2 := none }

def smallTiny : ScaleDatum :=
  { weakerTerm := "small", strongerTerm := "tiny"
  , semanticDistance := some 4.2
  , bounded := false
  , globalSIRate := some 19
  , embeddedSIRate_Exp1 := some 15
  , embeddedSIRate_Exp2 := some 4 }

-- Age scales (non-bounded)
def oldAncient : ScaleDatum :=
  { weakerTerm := "old", strongerTerm := "ancient"
  , semanticDistance := some 4.6
  , bounded := false
  , globalSIRate := some 14
  , embeddedSIRate_Exp1 := some 18
  , embeddedSIRate_Exp2 := some 4 }

-- Color scales (non-bounded)
def darkBlack : ScaleDatum :=
  { weakerTerm := "dark", strongerTerm := "black"
  , semanticDistance := some 4.2
  , bounded := false
  , globalSIRate := some 8
  , embeddedSIRate_Exp1 := some 13
  , embeddedSIRate_Exp2 := some 0 }

-- Emotion/attitude scales (non-bounded)
def contentHappy : ScaleDatum :=
  { weakerTerm := "content", strongerTerm := "happy"
  , semanticDistance := some 3.7
  , bounded := false
  , globalSIRate := some 8
  , embeddedSIRate_Exp1 := some 15
  , embeddedSIRate_Exp2 := none }

def likeLove : ScaleDatum :=
  { weakerTerm := "like", strongerTerm := "love"
  , semanticDistance := some 5.0
  , bounded := false
  , globalSIRate := some 44
  , embeddedSIRate_Exp1 := some 15
  , embeddedSIRate_Exp2 := some 9 }

def dislikeLoathe : ScaleDatum :=
  { weakerTerm := "dislike", strongerTerm := "loathe"
  , semanticDistance := some 4.7
  , bounded := false
  , globalSIRate := some 22
  , embeddedSIRate_Exp1 := some 17
  , embeddedSIRate_Exp2 := some 16 }

def waryScared : ScaleDatum :=
  { weakerTerm := "wary", strongerTerm := "scared"
  , semanticDistance := some 4.5
  , bounded := false
  , globalSIRate := some 25
  , embeddedSIRate_Exp1 := some 18
  , embeddedSIRate_Exp2 := none }

def unsettlingHorrific : ScaleDatum :=
  { weakerTerm := "unsettling", strongerTerm := "horrific"
  , semanticDistance := some 5.0
  , bounded := false
  , globalSIRate := some 36
  , embeddedSIRate_Exp1 := some 31
  , embeddedSIRate_Exp2 := some 31 }

def tiredExhausted : ScaleDatum :=
  { weakerTerm := "tired", strongerTerm := "exhausted"
  , semanticDistance := some 4.8
  , bounded := false
  , globalSIRate := some 31
  , embeddedSIRate_Exp1 := some 14
  , embeddedSIRate_Exp2 := none }

def hungryStarving : ScaleDatum :=
  { weakerTerm := "hungry", strongerTerm := "starving"
  , semanticDistance := some 5.2
  , bounded := false
  , globalSIRate := some 36
  , embeddedSIRate_Exp1 := some 21
  , embeddedSIRate_Exp2 := none }

-- Appearance scales (non-bounded)
def attractiveStunning : ScaleDatum :=
  { weakerTerm := "attractive", strongerTerm := "stunning"
  , semanticDistance := some 4.8
  , bounded := false
  , globalSIRate := some 17
  , embeddedSIRate_Exp1 := some 28
  , embeddedSIRate_Exp2 := some 0 }

def prettyBeautiful : ScaleDatum :=
  { weakerTerm := "pretty", strongerTerm := "beautiful"
  , semanticDistance := some 4.5
  , bounded := false
  , globalSIRate := some 28
  , embeddedSIRate_Exp1 := some 20
  , embeddedSIRate_Exp2 := none }

-- Intensity scales (non-bounded)
def sillyRidiculous : ScaleDatum :=
  { weakerTerm := "silly", strongerTerm := "ridiculous"
  , semanticDistance := some 3.9
  , bounded := false
  , globalSIRate := some 17
  , embeddedSIRate_Exp1 := some 18
  , embeddedSIRate_Exp2 := none }

def snugTight : ScaleDatum :=
  { weakerTerm := "snug", strongerTerm := "tight"
  , semanticDistance := some 3.1
  , bounded := false
  , globalSIRate := some 11
  , embeddedSIRate_Exp1 := some 10
  , embeddedSIRate_Exp2 := some 2 }

/-- All 42 scales tested in the study -/
def allScales : List ScaleDatum := [
  -- Bounded scales
  someAll, possibleCertain, allowedObligatory, mayHaveTo, mayWill,
  sometimesAlways, cheapFree, difficultImpossible, hardUnsolvable,
  rareExtinct, scarceUnavailable, lowDepleted, startFinish,
  trySucceed, participateWin, believeKnow, goodPerfect,
  memorableUnforgettable, specialUnique,
  -- Non-bounded scales
  warmHot, coolCold, goodExcellent, adequateGood, palatableDelicious,
  bigEnormous, smallTiny, oldAncient, darkBlack, contentHappy,
  likeLove, dislikeLoathe, waryScared, unsettlingHorrific,
  tiredExhausted, hungryStarving, attractiveStunning, prettyBeautiful,
  sillyRidiculous, snugTight
]

/-- Bounded scales -/
def boundedScales : List ScaleDatum := allScales.filter (·.bounded)

/-- Non-bounded scales -/
def nonBoundedScales : List ScaleDatum := allScales.filter (!·.bounded)


/--
Experiment 1 design (Gotzner & Romoli 2018 paradigm).

Participants judged to what extent Sentence 1 "suggests" Sentence 2
on a 0-100 sliding scale.

Four conditions per scale:
- strong: "Every soup was warm" → "No soup was hot"
- weak: "Every soup was warm" → "Not every soup was hot"
- true: "Every soup was warm" → "At least one soup was warm"
- false: "Every soup was warm" → "Not every soup was warm"
-/
structure Exp1Design where
  /-- Number of participants -/
  n : Nat
  /-- Number of scales tested -/
  nScales : Nat
  deriving Repr

def exp1Design : Exp1Design :=
  { n := 118, nScales := 42 }

/--
Experiment 1 aggregate results by condition (averaged across scales).
-/
structure Exp1AggregateResult where
  /-- Mean response for true control (0-100) -/
  trueControl : Nat
  /-- Mean response for weak inference (0-100) -/
  weakInference : Nat
  /-- Mean response for strong inference (0-100) -/
  strongInference : Nat
  /-- Mean response for false control (0-100) -/
  falseControl : Nat
  deriving Repr

/--
Aggregate results from Experiment 1 Figure 1.
-/
def exp1Aggregate : Exp1AggregateResult :=
  { trueControl := 85
  , weakInference := 45
  , strongInference := 32
  , falseControl := 6 }

/-- Response ordering matches prediction: true > weak > strong > false. -/
theorem exp1_ordering :
    exp1Aggregate.trueControl > exp1Aggregate.weakInference ∧
    exp1Aggregate.weakInference > exp1Aggregate.strongInference ∧
    exp1Aggregate.strongInference > exp1Aggregate.falseControl := by
  native_decide

/-- Strong inference (32%) significantly above false control (6%),
    indicating embedded SIs are computed. -/
theorem exp1_strong_above_false :
    exp1Aggregate.strongInference > exp1Aggregate.falseControl + 20 := by
  native_decide


/--
Experiment 2 design (van Tiel et al. 2016 inference task).

Binary Yes/No responses to:
"Mary: Every soup was warm.
 Would you conclude from this that, according to Mary, no soup was hot?"
-/
structure Exp2Design where
  /-- Number of participants -/
  n : Nat
  /-- Number of scales tested -/
  nScales : Nat
  deriving Repr

def exp2Design : Exp2Design :=
  { n := 45, nScales := 42 }


/--
Correlation between global SI rates (van Tiel et al. 2016) and
embedded SI rates (Ronai 2024).
-/
structure CorrelationResult where
  /-- Pearson correlation coefficient -/
  r : Float
  /-- p-value (significance) -/
  p : Float
  /-- Is significant at p < 0.001? -/
  significant : Bool
  deriving Repr

/--
Exp 1: Strong correlation between global and embedded SI rates.
-/
def exp1_globalEmbeddedCorrelation : CorrelationResult :=
  { r := 0.76, p := 0.001, significant := true }

/--
Exp 2: Strong correlation between global and embedded SI rates.
-/
def exp2_globalEmbeddedCorrelation : CorrelationResult :=
  { r := 0.80, p := 0.001, significant := true }

/-- Both experiments show strong positive correlation (r > 0.7),
    suggesting a shared mechanism for global and embedded SIs. -/
theorem high_correlations :
    exp1_globalEmbeddedCorrelation.r > 0.7 ∧
    exp2_globalEmbeddedCorrelation.r > 0.7 := by
  native_decide


/--
Effect of a predictor on SI rates.
-/
structure PredictorEffect where
  /-- Name of the predictor -/
  predictor : String
  /-- Direction of effect (positive = more SI) -/
  direction : String
  /-- Is the effect significant? -/
  significant : Bool
  /-- p-value -/
  p : Float
  deriving Repr

/--
Semantic distance effect: larger distance → more embedded SI.
-/
def semanticDistanceEffect_Exp1 : PredictorEffect :=
  { predictor := "Semantic Distance"
  , direction := "positive"
  , significant := true
  , p := 0.05 }

def semanticDistanceEffect_Exp2 : PredictorEffect :=
  { predictor := "Semantic Distance"
  , direction := "positive"
  , significant := true
  , p := 0.05 }

/--
Boundedness effect: bounded scales → more embedded SI.
-/
def boundednessEffect_Exp1 : PredictorEffect :=
  { predictor := "Boundedness"
  , direction := "positive"
  , significant := true
  , p := 0.001 }

def boundednessEffect_Exp2 : PredictorEffect :=
  { predictor := "Boundedness"
  , direction := "positive"
  , significant := true
  , p := 0.001 }

/-- Both predictors significant in both experiments. -/
theorem predictors_significant :
    semanticDistanceEffect_Exp1.significant ∧
    semanticDistanceEffect_Exp2.significant ∧
    boundednessEffect_Exp1.significant ∧
    boundednessEffect_Exp2.significant := by
  native_decide


/--
Mean embedded SI rate by boundedness (Exp 1).
From Figure 4.
-/
def boundedMean_Exp1 : Nat := 38
def nonBoundedMean_Exp1 : Nat := 21

/--
Mean embedded SI rate by boundedness (Exp 2).
From Figure 7.
-/
def boundedMean_Exp2 : Nat := 23
def nonBoundedMean_Exp2 : Nat := 10

/-- Bounded scales show higher embedded SI rates. -/
theorem bounded_higher :
    boundedMean_Exp1 > nonBoundedMean_Exp1 ∧
    boundedMean_Exp2 > nonBoundedMean_Exp2 := by
  native_decide


/--
Theoretical accounts evaluated in the paper.
-/
inductive TheoryType where
  /-- Grammatical theory (Chierchia 2004; Chierchia et al. 2012) -/
  | grammatical
  /-- Modified neo-Gricean (Sauerland 2004) -/
  | neoGricean
  /-- RSA-LU with neo-Gricean uncertainty (Potts et al. 2015) -/
  | rsaLU_neoGricean
  /-- RSA-LU with unconstrained uncertainty (Bergen et al. 2016) -/
  | rsaLU_unconstrained
  deriving DecidableEq, Repr

/--
Does a theory use scalar alternatives in the SI derivation?
-/
def usesAlternatives : TheoryType → Bool
  | .grammatical => true
  | .neoGricean => true
  | .rsaLU_neoGricean => true
  | .rsaLU_unconstrained => false

/--
Is a theory supported by the finding that alternative-based predictors
(semantic distance, boundedness) predict embedded SI variation?
-/
def supportedByData : TheoryType → Bool
  | .grammatical => true
  | .neoGricean => true
  | .rsaLU_neoGricean => true
  | .rsaLU_unconstrained => false

/-- Theories that use alternatives are supported by the data. -/
theorem alternatives_supported :
    ∀ t : TheoryType, usesAlternatives t = supportedByData t := by
  intro t
  cases t <;> native_decide


/--
Prior studies on embedded SI discussed in the paper.
-/
structure PriorStudy where
  /-- Citation -/
  citation : String
  /-- Did they find evidence for embedded SI? -/
  foundEmbeddedSI : Bool
  /-- Number of scales tested -/
  nScales : Nat
  deriving Repr

/-- Prior studies on embedded SIs. -/
def priorStudies : List PriorStudy := [
  { citation := "Geurts & Pouscoulous (2009)"
  , foundEmbeddedSI := false  -- Limited evidence
  , nScales := 1 },           -- Only some/all
  { citation := "Gotzner & Romoli (2018)"
  , foundEmbeddedSI := true
  , nScales := 1 },           -- Only some/all
  { citation := "Sun, Tian & Breheny (2018)"
  , foundEmbeddedSI := true   -- But no predictor effects
  , nScales := 43 },
  { citation := "Bleotu & Benz (to appear)"
  , foundEmbeddedSI := true   -- With predictor effects
  , nScales := 43 }
]

/-- Ronai (2024) combines the Gotzner & Romoli paradigm with
    van Tiel et al.'s 42 scales. -/
theorem comprehensive_test :
    exp1Design.nScales = 42 ∧
    exp2Design.nScales = 42 := by
  native_decide

end Phenomena.Ronai2024
