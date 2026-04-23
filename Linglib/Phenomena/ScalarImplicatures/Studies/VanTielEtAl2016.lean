import Mathlib.Data.Rat.Defs
import Linglib.Features.Acceptability
import Linglib.Paradigms.Measurement

/-!
# @cite{van-tiel-geurts-2016} — Scalar Diversity
@cite{van-tiel-geurts-2016} @cite{ronai-2024}

Theory-neutral empirical data and argumentation chain from
@cite{van-tiel-geurts-2016}.

## Central Question

Do all scalar expressions yield scalar implicatures at comparable rates?
The "uniformity assumption" — implicit in decades of SI research focused
on ⟨some, all⟩ and ⟨or, and⟩ — predicts yes.

## Argumentative Structure

1. **Scalar diversity is real** (Exps 1–2, §2): SI rates vary continuously
   from 4% (⟨content, happy⟩) to 100% (⟨cheap, free⟩) across 43 scales.
   Experiment 1 (N=25) uses neutral content (pronouns); Experiment 2
   (N=29) uses non-neutral content (full NPs). Results correlate highly
   (r=.91), confirming robustness to sentential context.

2. **Availability does not explain diversity** (Exp 3, §4): Four
   operationalisations of scale availability all fail to predict SI rates:
   - Association strength (modified cloze task, Exp 3, N=60): β=0.16, n.s.
   - Grammatical class (open vs closed): β=−0.38, n.s.
   - Relative word frequency (corpus log-ratio): β=−0.15, n.s.
   - Semantic relatedness (LSA cosine): β=0.01, n.s.

3. **Distinctness does explain diversity** (Exp 4, §5): Two measures of
   how easy it is to distinguish scalemates both predict SI rates:
   - Semantic distance (7-point rating, Exp 4, N=24): β=0.65, p=.018
   - Boundedness (stronger term is endpoint): β=−1.87, p<.001

4. **Combined model** (§6, Table 5): Mixed model with all six predictors
   explains R²=0.52 of variance (0.22 fixed effects, 0.30 random). Of the
   fixed-effects variance, boundedness alone accounts for 10.8%, distance
   for 2.7%, and all four availability measures combined for <1%.

5. **Remaining variance** (§6): ~78% of variance is unexplained, suggesting
   item-specific statistical learning from language use — hearers track
   frequencies of upper-bounding inferences for individual scales and use
   Gricean reasoning to combine prior likelihoods with the current context.
-/

namespace VanTielEtAl2016

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
  deriving DecidableEq, Repr, Inhabited

/--
Whether a scale is "open" or "closed" class.
Closed class = smaller search space for alternatives (predicted more available).
-/
def GrammaticalClass.isClosedClass : GrammaticalClass → Bool
  | .quantifier => true
  | .auxiliaryVerb => true
  | _ => false

/--
Complete data for each scale tested in @cite{van-tiel-geurts-2016}.

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

/-- All 43 scales tested in @cite{van-tiel-geurts-2016} -/
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

#guard numBounded == 21
#guard numNonBounded == 22
#guard numBounded + numNonBounded == numScales


-- ============================================================================
-- Computed Data Properties
-- ============================================================================

/-- SI rates span 96 percentage points: 4% to 100%.
⟨content, happy⟩ is the floor, ⟨cheap, free⟩ the ceiling. -/
theorem si_range :
    allScales.all (·.siRateExp1 ≥ 4) ∧
    allScales.all (·.siRateExp1 ≤ 100) ∧
    allScales.any (·.siRateExp1 == 4) ∧
    allScales.any (·.siRateExp1 == 100) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Bounded scales yield far more SIs than non-bounded scales.

Total SI rate (Exp 1) across 21 bounded scales: 1287%.
Total SI rate (Exp 1) across 22 non-bounded scales: 465%.
Even though bounded scales have *fewer* items, their total is nearly 3× higher.
The paper reports mean bounded ≈ 62% vs mean non-bounded ≈ 25%. -/
theorem bounded_total_exceeds_nonbounded :
    (boundedScales.map (·.siRateExp1)).foldl (· + ·) 0 >
    (nonBoundedScales.map (·.siRateExp1)).foldl (· + ·) 0 := by native_decide

/-- ⟨some, all⟩ — the "workhorse" of SI research — sits near the top at 96%,
far above the mean. Generalizing from ⟨some, all⟩ to all scales is unjustified. -/
theorem someAll_above_median :
    Scales.someAll.siRateExp1 > 50 := by native_decide

/-- In this sample, every closed-class scale is also bounded.
This confound partially explains the nonsignificant grammatical-class effect:
closed-class scales look high-SI because they're all bounded, not because
the search space for alternatives is smaller. -/
theorem closed_class_subsumes_bounded :
    allScales.all (λ s => !s.category.isClosedClass || s.bounded) = true := by
  native_decide

/-- Experiments 1 and 2 agree directionally: no scale reverses from high to low
or vice versa (defined as >50% in one experiment and <15% in the other). -/
theorem exp1_exp2_directional_agreement :
    allScales.all (λ s =>
      !(s.siRateExp1 > 50 && s.siRateExp2 < 15) &&
      !(s.siRateExp2 > 50 && s.siRateExp1 < 15)) = true := by
  native_decide

-- ============================================================================
-- Regression Model (Table 5)
-- ============================================================================

/-- A row from the mixed-effects regression in Table 5.

The model predicts SI rates from Exps 1–2 using six fixed-effect predictors
(four availability measures, two distinctness measures) plus random slopes
and intercepts for participants and items. -/
structure RegressionRow where
  /-- Name of the predictor -/
  name : String
  /-- Estimated coefficient -/
  beta : ℚ
  /-- Standard error -/
  se : ℚ
  /-- z-statistic -/
  z : ℚ
  /-- p-value (two-tailed) -/
  p : ℚ
  /-- Marginal R² (variance explained by this predictor alone) -/
  r2 : ℚ
  deriving Repr

-- Availability predictors (§4): none significant

/-- Association strength (lenient cloze, Exp 3): β=0.16, p=.611. -/
def associationStrength : RegressionRow :=
  { name := "association_strength"
  , beta := 16/100, se := 31/100, z := 51/100
  , p := 611/1000, r2 := 0 }

/-- Grammatical class (open/closed): β=−0.38, p=.606.
Confounded with boundedness — all closed-class scales in this sample
are also bounded (see `closed_class_subsumes_bounded`). -/
def grammaticalClass : RegressionRow :=
  { name := "grammatical_class"
  , beta := -38/100, se := 74/100, z := -52/100
  , p := 606/1000, r2 := 1/1000 }

/-- Relative word frequency (log ratio weaker/stronger): β=−0.15, p=.461. -/
def relativeFrequency : RegressionRow :=
  { name := "relative_frequency"
  , beta := -15/100, se := 21/100, z := -74/100
  , p := 461/1000, r2 := 3/1000 }

/-- Semantic relatedness (LSA cosine): β=0.01, p=.355. -/
def semanticRelatedness : RegressionRow :=
  { name := "semantic_relatedness"
  , beta := 1/100, se := 1/100, z := 93/100
  , p := 355/1000, r2 := 6/1000 }

-- Distinctness predictors (§5): both significant

/-- Semantic distance (7-point rating, Exp 4): β=0.65, p=.018. -/
def semanticDistance : RegressionRow :=
  { name := "semantic_distance"
  , beta := 65/100, se := 27/100, z := 236/100
  , p := 18/1000, r2 := 27/1000 }

/-- Boundedness (stronger term is endpoint): β=−1.87, p<.001.
Negative β because the coding is bounded=1, so bounded scales are
associated with *higher* SI rates (higher positive response = lower
log-odds of "no"). Largest single predictor: R²=10.8%. -/
def boundedness : RegressionRow :=
  { name := "boundedness"
  , beta := -187/100, se := 40/100, z := -472/100
  , p := 0, r2 := 108/1000 }  -- p reported as .000 in Table 5

/-- All six predictor rows, for iteration. -/
def regressionRows : List RegressionRow :=
  [associationStrength, grammaticalClass, relativeFrequency,
   semanticRelatedness, semanticDistance, boundedness]

-- ============================================================================
-- Regression Significance Theorems
-- ============================================================================

/-- Both distinctness predictors are significant (p < .05). -/
theorem distinctness_both_significant :
    semanticDistance.p < 5/100 ∧ boundedness.p < 5/100 := by
  constructor <;> native_decide

/-- No availability predictor is significant (all p > .05). -/
theorem availability_none_significant :
    associationStrength.p > 5/100 ∧
    grammaticalClass.p > 5/100 ∧
    relativeFrequency.p > 5/100 ∧
    semanticRelatedness.p > 5/100 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Boundedness alone explains more variance than all four availability
predictors combined. R²(boundedness) = 0.108 > 0 + 0.001 + 0.003 + 0.006 = 0.010. -/
theorem boundedness_dominates_availability :
    boundedness.r2 >
    associationStrength.r2 + grammaticalClass.r2 +
    relativeFrequency.r2 + semanticRelatedness.r2 := by native_decide

/-- Distinctness explains >10× more variance than availability.
(27 + 108)/1000 = 135/1000 vs (0 + 1 + 3 + 6)/1000 = 10/1000. -/
theorem distinctness_exceeds_availability_tenfold :
    (semanticDistance.r2 + boundedness.r2) * 1000 >
    (associationStrength.r2 + grammaticalClass.r2 +
     relativeFrequency.r2 + semanticRelatedness.r2) * 10000 := by native_decide

end VanTielEtAl2016
