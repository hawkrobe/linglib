/-
# Van Tiel et al. (2016) - Scalar Diversity

Foundational experimental data on cross-scale variation in scalar implicature rates.

## Citation

van Tiel, B., van Miltenburg, E., Zevakhina, N., & Geurts, B. (2016).
Scalar Diversity. Journal of Semantics, 33(1), 137-175.
https://doi.org/10.1093/jos/ffu017

## Key Findings

1. **Scalar Diversity**: SI rates vary from 4% to 100% across 43 scales
2. **Distinctness matters**: Semantic distance and boundedness predict SI rates
3. **Availability doesn't matter**: Association strength, grammatical class,
   word frequency, and semantic relatedness have no significant effect
4. **Boundedness**: Bounded scales (stronger term = endpoint) yield higher SI rates

## Theoretical Impact

- Challenges the "uniformity assumption" that all scales behave alike
- Most SI research had focused on ⟨some, all⟩ and ⟨or, and⟩
- Shows ⟨some, all⟩ is an extreme case (96%), not representative
- Provides foundation for later work (Ronai 2024 on embedded SI diversity)

## Experiments

- **Experiment 1**: Inference task with neutral content (pronouns)
- **Experiment 2**: Inference task with non-neutral content (full NPs)
- **Experiment 3**: Modified cloze task (association strength)
- **Experiment 4**: Semantic distance ratings (1-7 scale)
-/

import Mathlib.Data.Rat.Defs

namespace Phenomena.VanTielEtAl2016


/--
Grammatical category of a scale.
Van Tiel et al. distinguish open vs closed classes for availability hypothesis.
-/
inductive GrammaticalClass where
  | adjective
  | adverb
  | auxiliaryVerb
  | mainVerb
  | quantifier
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Whether a scale is "open" or "closed" class.
Closed class = smaller search space for alternatives (predicted more available).
-/
def GrammaticalClass.isClosedClass : GrammaticalClass → Bool
  | .quantifier => true
  | .auxiliaryVerb => true
  | _ => false

/--
Complete data for each scale tested in van Tiel et al. (2016).

Fields capture all predictors tested in the paper:
- SI rates from Experiments 1 and 2
- Availability measures (cloze, frequency, LSA)
- Distinctness measures (semantic distance, boundedness)
-/
structure ScaleDatum where
  /-- Weaker scalar term -/
  weakerTerm : String
  /-- Stronger scalar term -/
  strongerTerm : String
  /-- Grammatical category -/
  category : GrammaticalClass
  /-- SI rate in Experiment 1 (neutral content, %) -/
  siRateExp1 : Nat
  /-- SI rate in Experiment 2 (non-neutral content, %) -/
  siRateExp2 : Nat
  /-- Cloze task: % mentioning stronger term (Exp3, neutral, lenient) -/
  clozeNeutral : Option Nat
  /-- Cloze task: % mentioning stronger term (Exp3, non-neutral, lenient) -/
  clozeNonNeutral : Option Nat
  /-- Log ratio of weaker/stronger term frequencies -/
  freqRatio : Option Float
  /-- LSA semantic relatedness (0-1) -/
  lsaRelatedness : Option Float
  /-- Mean semantic distance rating (1-7 scale, Exp4) -/
  semanticDistance : Float
  /-- Whether stronger term denotes an endpoint (bounded scale) -/
  bounded : Bool
  deriving Repr


namespace Scales

/-- ⟨cheap, free⟩ - highest SI rate (100%) -/
def cheapFree : ScaleDatum :=
  { weakerTerm := "cheap", strongerTerm := "free"
  , category := .adjective
  , siRateExp1 := 100, siRateExp2 := 93
  , clozeNeutral := some 0, clozeNonNeutral := some 0
  , freqRatio := some (-0.66), lsaRelatedness := some 0.19
  , semanticDistance := 5.52, bounded := true }

/-- ⟨sometimes, always⟩ -/
def sometimesAlways : ScaleDatum :=
  { weakerTerm := "sometimes", strongerTerm := "always"
  , category := .adverb
  , siRateExp1 := 100, siRateExp2 := 86
  , clozeNeutral := some 80, clozeNonNeutral := some 90
  , freqRatio := some (-1.05), lsaRelatedness := some 0.60
  , semanticDistance := 5.70, bounded := true }

/-- ⟨some, all⟩ - the "workhorse" of SI research -/
def someAll : ScaleDatum :=
  { weakerTerm := "some", strongerTerm := "all"
  , category := .quantifier
  , siRateExp1 := 96, siRateExp2 := 89
  , clozeNeutral := some 67, clozeNonNeutral := some 87
  , freqRatio := some (-0.12), lsaRelatedness := some 0.79
  , semanticDistance := 5.83, bounded := true }

/-- ⟨possible, certain⟩ -/
def possibleCertain : ScaleDatum :=
  { weakerTerm := "possible", strongerTerm := "certain"
  , category := .adjective
  , siRateExp1 := 92, siRateExp2 := 93
  , clozeNeutral := some 55, clozeNonNeutral := some 31
  , freqRatio := some 0.10, lsaRelatedness := some 0.42
  , semanticDistance := 5.65, bounded := true }

/-- ⟨may, will⟩ -/
def mayWill : ScaleDatum :=
  { weakerTerm := "may", strongerTerm := "will"
  , category := .auxiliaryVerb
  , siRateExp1 := 87, siRateExp2 := 89
  , clozeNeutral := some 83, clozeNonNeutral := some 80
  , freqRatio := some 0.68, lsaRelatedness := some 0.51
  , semanticDistance := 5.41, bounded := true }

/-- ⟨difficult, impossible⟩ -/
def difficultImpossible : ScaleDatum :=
  { weakerTerm := "difficult", strongerTerm := "impossible"
  , category := .adjective
  , siRateExp1 := 79, siRateExp2 := 96
  , clozeNeutral := some 13, clozeNonNeutral := some 10
  , freqRatio := some 0.46, lsaRelatedness := some 0.60
  , semanticDistance := 6.22, bounded := true }

/-- ⟨rare, extinct⟩ -/
def rareExtinct : ScaleDatum :=
  { weakerTerm := "rare", strongerTerm := "extinct"
  , category := .adjective
  , siRateExp1 := 79, siRateExp2 := 79
  , clozeNeutral := some 40, clozeNonNeutral := some 34
  , freqRatio := some 1.05, lsaRelatedness := some 0.29
  , semanticDistance := 5.83, bounded := true }

/-- ⟨may, have to⟩ -/
def mayHaveTo : ScaleDatum :=
  { weakerTerm := "may", strongerTerm := "have to"
  , category := .auxiliaryVerb
  , siRateExp1 := 75, siRateExp2 := 71
  , clozeNeutral := some 83, clozeNonNeutral := some 80
  , freqRatio := some (-1.22), lsaRelatedness := some 0.64
  , semanticDistance := 5.26, bounded := true }

/-- ⟨warm, hot⟩ -/
def warmHot : ScaleDatum :=
  { weakerTerm := "warm", strongerTerm := "hot"
  , category := .adjective
  , siRateExp1 := 75, siRateExp2 := 64
  , clozeNeutral := some 70, clozeNonNeutral := some 38
  , freqRatio := some (-0.28), lsaRelatedness := some 0.51
  , semanticDistance := 5.00, bounded := false }

/-- ⟨few, none⟩ -/
def fewNone : ScaleDatum :=
  { weakerTerm := "few", strongerTerm := "none"
  , category := .quantifier
  , siRateExp1 := 75, siRateExp2 := 54
  , clozeNeutral := some 20, clozeNonNeutral := some 30
  , freqRatio := some 0.75, lsaRelatedness := some 0.47
  , semanticDistance := 5.35, bounded := true }

/-- ⟨low, depleted⟩ -/
def lowDepleted : ScaleDatum :=
  { weakerTerm := "low", strongerTerm := "depleted"
  , category := .adjective
  , siRateExp1 := 71, siRateExp2 := 79
  , clozeNeutral := some 23, clozeNonNeutral := some 60
  , freqRatio := some 2.29, lsaRelatedness := some 0.16
  , semanticDistance := 4.87, bounded := true }

/-- ⟨hard, unsolvable⟩ -/
def hardUnsolvable : ScaleDatum :=
  { weakerTerm := "hard", strongerTerm := "unsolvable"
  , category := .adjective
  , siRateExp1 := 71, siRateExp2 := 71
  , clozeNeutral := some 10, clozeNonNeutral := some 10
  , freqRatio := some 2.87, lsaRelatedness := some 0.08
  , semanticDistance := 5.26, bounded := true }

/-- ⟨allowed, obligatory⟩ -/
def allowedObligatory : ScaleDatum :=
  { weakerTerm := "allowed", strongerTerm := "obligatory"
  , category := .adjective
  , siRateExp1 := 67, siRateExp2 := 82
  , clozeNeutral := some 20, clozeNonNeutral := some 47
  , freqRatio := some (-0.85), lsaRelatedness := some 0.02
  , semanticDistance := 5.35, bounded := true }

/-- ⟨scarce, unavailable⟩ -/
def scarceUnavailable : ScaleDatum :=
  { weakerTerm := "scarce", strongerTerm := "unavailable"
  , category := .adjective
  , siRateExp1 := 62, siRateExp2 := 57
  , clozeNeutral := some 40, clozeNonNeutral := some 17
  , freqRatio := some 0.29, lsaRelatedness := some 0.18
  , semanticDistance := 4.78, bounded := true }

/-- ⟨try, succeed⟩ -/
def trySucceed : ScaleDatum :=
  { weakerTerm := "try", strongerTerm := "succeed"
  , category := .mainVerb
  , siRateExp1 := 62, siRateExp2 := 39
  , clozeNeutral := some 37, clozeNonNeutral := some 57
  , freqRatio := some 1.23, lsaRelatedness := some 0.35
  , semanticDistance := 5.82, bounded := true }

/-- ⟨palatable, delicious⟩ -/
def palatableDelicious : ScaleDatum :=
  { weakerTerm := "palatable", strongerTerm := "delicious"
  , category := .adjective
  , siRateExp1 := 58, siRateExp2 := 61
  , clozeNeutral := some 67, clozeNonNeutral := some 47
  , freqRatio := some (-0.89), lsaRelatedness := some 0.32
  , semanticDistance := 5.52, bounded := false }

/-- ⟨memorable, unforgettable⟩ -/
def memorableUnforgettable : ScaleDatum :=
  { weakerTerm := "memorable", strongerTerm := "unforgettable"
  , category := .adjective
  , siRateExp1 := 50, siRateExp2 := 54
  , clozeNeutral := some 23, clozeNonNeutral := some 60
  , freqRatio := some 0.56, lsaRelatedness := some 0.29
  , semanticDistance := 4.83, bounded := true }

/-- ⟨like, love⟩ -/
def likeLove : ScaleDatum :=
  { weakerTerm := "like", strongerTerm := "love"
  , category := .mainVerb
  , siRateExp1 := 50, siRateExp2 := 25
  , clozeNeutral := some 80, clozeNonNeutral := some 57
  , freqRatio := some 0.23, lsaRelatedness := some 0.37
  , semanticDistance := 5.74, bounded := false }

/-- ⟨good, perfect⟩ -/
def goodPerfect : ScaleDatum :=
  { weakerTerm := "good", strongerTerm := "perfect"
  , category := .adjective
  , siRateExp1 := 46, siRateExp2 := 39
  , clozeNeutral := some 60, clozeNonNeutral := some 23
  , freqRatio := some 1.00, lsaRelatedness := some 0.42
  , semanticDistance := 6.09, bounded := true }

/-- ⟨good, excellent⟩ -/
def goodExcellent : ScaleDatum :=
  { weakerTerm := "good", strongerTerm := "excellent"
  , category := .adjective
  , siRateExp1 := 37, siRateExp2 := 32
  , clozeNeutral := some 60, clozeNonNeutral := some 57
  , freqRatio := some 1.34, lsaRelatedness := some 0.46
  , semanticDistance := 5.48, bounded := false }

/-- ⟨cool, cold⟩ -/
def coolCold : ScaleDatum :=
  { weakerTerm := "cool", strongerTerm := "cold"
  , category := .adjective
  , siRateExp1 := 33, siRateExp2 := 46
  , clozeNeutral := some 23, clozeNonNeutral := some 40
  , freqRatio := some (-0.21), lsaRelatedness := some 0.61
  , semanticDistance := 4.30, bounded := false }

/-- ⟨hungry, starving⟩ -/
def hungryStarving : ScaleDatum :=
  { weakerTerm := "hungry", strongerTerm := "starving"
  , category := .adjective
  , siRateExp1 := 33, siRateExp2 := 25
  , clozeNeutral := some 63, clozeNonNeutral := some 40
  , freqRatio := some 0.71, lsaRelatedness := some 0.52
  , semanticDistance := 5.74, bounded := false }

/-- ⟨adequate, good⟩ -/
def adequateGood : ScaleDatum :=
  { weakerTerm := "adequate", strongerTerm := "good"
  , category := .adjective
  , siRateExp1 := 29, siRateExp2 := 32
  , clozeNeutral := some 33, clozeNonNeutral := some 57
  , freqRatio := some (-1.52), lsaRelatedness := some 0.27
  , semanticDistance := 3.52, bounded := false }

/-- ⟨unsettling, horrific⟩ -/
def unsettlingHorrific : ScaleDatum :=
  { weakerTerm := "unsettling", strongerTerm := "horrific"
  , category := .adjective
  , siRateExp1 := 29, siRateExp2 := 25
  , clozeNeutral := some 37, clozeNonNeutral := some 37
  , freqRatio := some (-0.48), lsaRelatedness := none  -- NA in paper
  , semanticDistance := 5.65, bounded := false }

/-- ⟨dislike, loathe⟩ -/
def dislikeLoathe : ScaleDatum :=
  { weakerTerm := "dislike", strongerTerm := "loathe"
  , category := .mainVerb
  , siRateExp1 := 29, siRateExp2 := 18
  , clozeNeutral := some 93, clozeNonNeutral := some 90
  , freqRatio := some 0.46, lsaRelatedness := some 0.16
  , semanticDistance := 5.87, bounded := false }

/-- ⟨believe, know⟩ -/
def believeKnow : ScaleDatum :=
  { weakerTerm := "believe", strongerTerm := "know"
  , category := .mainVerb
  , siRateExp1 := 21, siRateExp2 := 61
  , clozeNeutral := some 67, clozeNonNeutral := some 67
  , freqRatio := some (-0.70), lsaRelatedness := some 0.46
  , semanticDistance := 5.04, bounded := true }

/-- ⟨start, finish⟩ -/
def startFinish : ScaleDatum :=
  { weakerTerm := "start", strongerTerm := "finish"
  , category := .mainVerb
  , siRateExp1 := 21, siRateExp2 := 21
  , clozeNeutral := some 43, clozeNonNeutral := some 50
  , freqRatio := some 0.70, lsaRelatedness := some 0.40
  , semanticDistance := 4.95, bounded := true }

/-- ⟨participate, win⟩ -/
def participateWin : ScaleDatum :=
  { weakerTerm := "participate", strongerTerm := "win"
  , category := .mainVerb
  , siRateExp1 := 21, siRateExp2 := 18
  , clozeNeutral := some 7, clozeNonNeutral := some 37
  , freqRatio := some (-0.62), lsaRelatedness := some 0.21
  , semanticDistance := 6.35, bounded := true }

/-- ⟨wary, scared⟩ -/
def waryScared : ScaleDatum :=
  { weakerTerm := "wary", strongerTerm := "scared"
  , category := .adjective
  , siRateExp1 := 21, siRateExp2 := 14
  , clozeNeutral := some 40, clozeNonNeutral := some 37
  , freqRatio := some (-0.48), lsaRelatedness := some 0.06
  , semanticDistance := 4.39, bounded := false }

/-- ⟨old, ancient⟩ -/
def oldAncient : ScaleDatum :=
  { weakerTerm := "old", strongerTerm := "ancient"
  , category := .adjective
  , siRateExp1 := 17, siRateExp2 := 36
  , clozeNeutral := some 50, clozeNonNeutral := some 33
  , freqRatio := some 1.08, lsaRelatedness := some 0.24
  , semanticDistance := 5.39, bounded := false }

/-- ⟨big, enormous⟩ -/
def bigEnormous : ScaleDatum :=
  { weakerTerm := "big", strongerTerm := "enormous"
  , category := .adjective
  , siRateExp1 := 17, siRateExp2 := 21
  , clozeNeutral := some 83, clozeNonNeutral := some 37
  , freqRatio := some 1.13, lsaRelatedness := some 0.21
  , semanticDistance := 5.43, bounded := false }

/-- ⟨snug, tight⟩ -/
def snugTight : ScaleDatum :=
  { weakerTerm := "snug", strongerTerm := "tight"
  , category := .adjective
  , siRateExp1 := 12, siRateExp2 := 21
  , clozeNeutral := some 87, clozeNonNeutral := some 87
  , freqRatio := some (-1.05), lsaRelatedness := some 0.30
  , semanticDistance := 2.86, bounded := false }

/-- ⟨attractive, stunning⟩ -/
def attractiveStunning : ScaleDatum :=
  { weakerTerm := "attractive", strongerTerm := "stunning"
  , category := .adjective
  , siRateExp1 := 8, siRateExp2 := 21
  , clozeNeutral := some 53, clozeNonNeutral := some 72
  , freqRatio := some 0.37, lsaRelatedness := some 0.07
  , semanticDistance := 5.78, bounded := false }

/-- ⟨special, unique⟩ -/
def specialUnique : ScaleDatum :=
  { weakerTerm := "special", strongerTerm := "unique"
  , category := .adjective
  , siRateExp1 := 8, siRateExp2 := 14
  , clozeNeutral := some 50, clozeNonNeutral := some 30
  , freqRatio := some 0.54, lsaRelatedness := some 0.32
  , semanticDistance := 3.48, bounded := true }

/-- ⟨pretty, beautiful⟩ -/
def prettyBeautiful : ScaleDatum :=
  { weakerTerm := "pretty", strongerTerm := "beautiful"
  , category := .adjective
  , siRateExp1 := 8, siRateExp2 := 11
  , clozeNeutral := some 73, clozeNonNeutral := some 50
  , freqRatio := some (-0.46), lsaRelatedness := some 0.41
  , semanticDistance := 5.04, bounded := false }

/-- ⟨intelligent, brilliant⟩ -/
def intelligentBrilliant : ScaleDatum :=
  { weakerTerm := "intelligent", strongerTerm := "brilliant"
  , category := .adjective
  , siRateExp1 := 8, siRateExp2 := 7
  , clozeNeutral := some 17, clozeNonNeutral := some 3
  , freqRatio := some (-0.12), lsaRelatedness := some 0.27
  , semanticDistance := 4.74, bounded := false }

/-- ⟨funny, hilarious⟩ -/
def funnyHilarious : ScaleDatum :=
  { weakerTerm := "funny", strongerTerm := "hilarious"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 29
  , clozeNeutral := some 50, clozeNonNeutral := some 33
  , freqRatio := some 1.17, lsaRelatedness := some 0.07
  , semanticDistance := 5.04, bounded := false }

/-- ⟨dark, black⟩ -/
def darkBlack : ScaleDatum :=
  { weakerTerm := "dark", strongerTerm := "black"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 29
  , clozeNeutral := some 30, clozeNonNeutral := some 27
  , freqRatio := some (-0.49), lsaRelatedness := some 0.40
  , semanticDistance := 4.04, bounded := true }

/-- ⟨small, tiny⟩ -/
def smallTiny : ScaleDatum :=
  { weakerTerm := "small", strongerTerm := "tiny"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 25
  , clozeNeutral := some 80, clozeNonNeutral := some 27
  , freqRatio := some 0.80, lsaRelatedness := some 0.54
  , semanticDistance := 4.22, bounded := false }

/-- ⟨ugly, hideous⟩ -/
def uglyHideous : ScaleDatum :=
  { weakerTerm := "ugly", strongerTerm := "hideous"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 18
  , clozeNeutral := some 37, clozeNonNeutral := some 31
  , freqRatio := some 0.86, lsaRelatedness := some 0.48
  , semanticDistance := 5.27, bounded := false }

/-- ⟨silly, ridiculous⟩ -/
def sillyRidiculous : ScaleDatum :=
  { weakerTerm := "silly", strongerTerm := "ridiculous"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 14
  , clozeNeutral := some 77, clozeNonNeutral := some 40
  , freqRatio := some 0.01, lsaRelatedness := some 0.43
  , semanticDistance := 4.17, bounded := false }

/-- ⟨tired, exhausted⟩ -/
def tiredExhausted : ScaleDatum :=
  { weakerTerm := "tired", strongerTerm := "exhausted"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 14
  , clozeNeutral := some 57, clozeNonNeutral := some 41
  , freqRatio := some 0.92, lsaRelatedness := some 0.45
  , semanticDistance := 5.13, bounded := false }

/-- ⟨content, happy⟩ - lowest SI rate (4%) -/
def contentHappy : ScaleDatum :=
  { weakerTerm := "content", strongerTerm := "happy"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 4
  , clozeNeutral := some 87, clozeNonNeutral := some 50
  , freqRatio := some (-0.85), lsaRelatedness := some 0.13
  , semanticDistance := 4.52, bounded := false }

end Scales

/-- All 43 scales tested in van Tiel et al. (2016) -/
def allScales : List ScaleDatum := [
  Scales.cheapFree,
  Scales.sometimesAlways,
  Scales.someAll,
  Scales.possibleCertain,
  Scales.mayWill,
  Scales.difficultImpossible,
  Scales.rareExtinct,
  Scales.mayHaveTo,
  Scales.warmHot,
  Scales.fewNone,
  Scales.lowDepleted,
  Scales.hardUnsolvable,
  Scales.allowedObligatory,
  Scales.scarceUnavailable,
  Scales.trySucceed,
  Scales.palatableDelicious,
  Scales.memorableUnforgettable,
  Scales.likeLove,
  Scales.goodPerfect,
  Scales.goodExcellent,
  Scales.coolCold,
  Scales.hungryStarving,
  Scales.adequateGood,
  Scales.unsettlingHorrific,
  Scales.dislikeLoathe,
  Scales.believeKnow,
  Scales.startFinish,
  Scales.participateWin,
  Scales.waryScared,
  Scales.oldAncient,
  Scales.bigEnormous,
  Scales.snugTight,
  Scales.attractiveStunning,
  Scales.specialUnique,
  Scales.prettyBeautiful,
  Scales.intelligentBrilliant,
  Scales.funnyHilarious,
  Scales.darkBlack,
  Scales.smallTiny,
  Scales.uglyHideous,
  Scales.sillyRidiculous,
  Scales.tiredExhausted,
  Scales.contentHappy
]


/-- Number of scales tested -/
def numScales : Nat := allScales.length

#guard numScales == 43

/-- Bounded scales -/
def boundedScales : List ScaleDatum := allScales.filter (·.bounded)

/-- Non-bounded scales -/
def nonBoundedScales : List ScaleDatum := allScales.filter (!·.bounded)

/-- Number of bounded scales -/
def numBounded : Nat := boundedScales.length

/-- Number of non-bounded scales -/
def numNonBounded : Nat := nonBoundedScales.length


/--
Main finding: SI rates vary enormously (4% to 100%).
The "uniformity assumption" is false.
-/
structure DiversityFinding where
  minSIRate : Nat := 4      -- content/happy
  maxSIRate : Nat := 100    -- cheap/free, sometimes/always
  meanSIRateExp1 : Nat := 42  -- approximate
  meanSIRateExp2 : Nat := 44  -- approximate

def diversityFinding : DiversityFinding := {}

/--
Regression model results (Table 5).
Full model R² = 0.52, fixed effects R² = 0.22
-/
structure RegressionResults where
  /-- Total variance explained by full model -/
  totalR2 : Float := 0.52
  /-- Variance explained by fixed effects -/
  fixedEffectsR2 : Float := 0.22
  /-- Variance from random effects (participants + items) -/
  randomEffectsR2 : Float := 0.30

/-- Predictor effect sizes from regression (Table 5) -/
structure PredictorEffect where
  name : String
  beta : Float
  se : Float
  z : Float
  p : Float
  r2 : Float

/-- Boundedness effect: significant predictor -/
def boundednessEffect : PredictorEffect :=
  { name := "boundedness"
  , beta := -1.87  -- negative because bounded = higher SI
  , se := 0.40
  , z := -4.72
  , p := 0.000
  , r2 := 0.108 }  -- explains 10.8% of variance

/-- Semantic distance effect: significant predictor -/
def semanticDistanceEffect : PredictorEffect :=
  { name := "semantic_distance"
  , beta := 0.65
  , se := 0.27
  , z := 2.36
  , p := 0.018
  , r2 := 0.027 }  -- explains 2.7% of variance

/-- Association strength: NOT significant -/
def associationStrengthEffect : PredictorEffect :=
  { name := "association_strength"
  , beta := 0.16
  , se := 0.31
  , z := 0.51
  , p := 0.611
  , r2 := 0.000 }

/-- Grammatical class: NOT significant -/
def grammaticalClassEffect : PredictorEffect :=
  { name := "grammatical_class"
  , beta := -0.38
  , se := 0.74
  , z := -0.52
  , p := 0.606
  , r2 := 0.001 }

/-- Relative frequency: NOT significant -/
def frequencyEffect : PredictorEffect :=
  { name := "relative_frequency"
  , beta := -0.15
  , se := 0.21
  , z := -0.74
  , p := 0.461
  , r2 := 0.003 }

/-- Semantic relatedness (LSA): NOT significant -/
def semanticRelatednessEffect : PredictorEffect :=
  { name := "semantic_relatedness"
  , beta := 0.10
  , se := 0.10
  , z := 0.93
  , p := 0.355
  , r2 := 0.006 }


/-- ⟨some, all⟩ is in the top tier (96%) -/
theorem someAll_high_rate : Scales.someAll.siRateExp1 = 96 := rfl

/-- ⟨content, happy⟩ is in the bottom tier (4%) -/
theorem contentHappy_low_rate : Scales.contentHappy.siRateExp1 = 4 := rfl

/-- Minimum SI rate in the data -/
def minSIRate : Nat := 4

/-- Maximum SI rate in the data -/
def maxSIRate : Nat := 100

-- Bounded scales have higher mean SI rate than non-bounded
-- Mean bounded ≈ 62%, mean non-bounded ≈ 25%
-- This is stated as the main finding, verified by examining the data

/-- Boundedness is a significant predictor (p < 0.01) -/
theorem boundedness_significant : boundednessEffect.p < 0.01 := by
  native_decide

/-- Semantic distance is a significant predictor (p < 0.05) -/
theorem semanticDistance_significant : semanticDistanceEffect.p < 0.05 := by
  native_decide

/-- Association strength is NOT significant (p > 0.05) -/
theorem associationStrength_not_significant : associationStrengthEffect.p > 0.05 := by
  native_decide

/-- Grammatical class is NOT significant (p > 0.05) -/
theorem grammaticalClass_not_significant : grammaticalClassEffect.p > 0.05 := by
  native_decide

/-- Frequency is NOT significant (p > 0.05) -/
theorem frequency_not_significant : frequencyEffect.p > 0.05 := by
  native_decide

/-- Semantic relatedness is NOT significant (p > 0.05) -/
theorem semanticRelatedness_not_significant : semanticRelatednessEffect.p > 0.05 := by
  native_decide


/-!
## Connection to Ronai (2024)

Van Tiel et al. (2016) established scalar diversity for **global** SI.
Ronai (2024) extends this to **embedded** SI, showing:

1. The same predictors (semantic distance, boundedness) work for embedded SI
2. Correlation between global and embedded SI rates: r = 0.76-0.80

## Connection to Geurts & Pouscoulous (2009)

Van Tiel et al. cite G&P's finding of 0% embedded SI for ⟨some, all⟩.
However, Ronai (2024) shows this varies by scale - it's not uniformly absent.

## Theoretical Implications

1. **Against uniformity**: Can't generalize from ⟨some, all⟩ to all scales
2. **Distinctness matters**: Formal (boundedness) and gradient (distance) properties
3. **Availability doesn't matter**: Challenges activation-based accounts
4. **Statistical patterns**: Suggests item-specific learning of SI rates
-/

/-- Predictor categories from van Tiel et al. -/
inductive PredictorCategory where
  | availability  -- association, class, frequency, relatedness
  | distinctness  -- semantic distance, boundedness
  deriving DecidableEq, Repr

/-- Whether a predictor was significant -/
def PredictorCategory.hasSignificantPredictors : PredictorCategory → Bool
  | .availability => false  -- none significant
  | .distinctness => true   -- both significant

/-- Main theoretical conclusion -/
def mainConclusion : String :=
  "The likelihood of a scalar inference depends on the distinctness of " ++
  "the scale members (semantic distance and boundedness), not on the " ++
  "availability of the scale (association strength, grammatical class, " ++
  "word frequency, or semantic relatedness)."

-- SUMMARY

/-!
## Summary of van Tiel et al. (2016)

### Data Provided
- 43 scales with SI rates from two experiments
- Predictor values: cloze scores, frequency, LSA, semantic distance, boundedness
- Regression results with effect sizes

### Key Findings
1. SI rates vary from 4% to 100% across scales
2. Distinctness (distance + boundedness) predicts SI rates
3. Availability measures (cloze, frequency, LSA, class) do not predict
4. ⟨some, all⟩ (96%) is extreme, not representative

### Theoretical Impact
- Refutes the uniformity assumption
- Identifies distinctness as the key factor
- Foundational for embedded SI research (Ronai 2024)

### Connection to Linglib
- Provides empirical foundation for `Fragments/Scales.lean`
- Informs RSA model priors over alternative salience
- Complements Ronai (2024) embedded SI data
-/

end Phenomena.VanTielEtAl2016
