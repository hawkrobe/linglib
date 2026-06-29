import Mathlib.Data.Rat.Defs
import Linglib.Features.Acceptability

/-!
# [van-tiel-geurts-2016] — Scalar Diversity
[van-tiel-geurts-2016] [ronai-2024]

Theory-neutral empirical data and argumentation chain from
[van-tiel-geurts-2016].

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
Complete data for each scale tested in [van-tiel-geurts-2016].

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
  freqRatio : Option ℚ
  /-- LSA semantic relatedness (0-1) -/
  lsaRelatedness : Option ℚ
  /-- Mean semantic distance rating (1-7 scale, Exp4) -/
  semanticDistance : ℚ
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
  , freqRatio := some ((-66/100)), lsaRelatedness := some (19/100)
  , semanticDistance := (552/100), bounded := true }

/-- ⟨sometimes, always⟩ -/
def sometimesAlways : ScaleDatum :=
  { weakerTerm := "sometimes", strongerTerm := "always"
  , category := .adverb
  , siRateExp1 := 100, siRateExp2 := 86
  , clozeNeutral := some 80, clozeNonNeutral := some 90
  , freqRatio := some ((-105/100)), lsaRelatedness := some (60/100)
  , semanticDistance := (570/100), bounded := true }

/-- ⟨some, all⟩ - the "workhorse" of SI research -/
def someAll : ScaleDatum :=
  { weakerTerm := "some", strongerTerm := "all"
  , category := .quantifier
  , siRateExp1 := 96, siRateExp2 := 89
  , clozeNeutral := some 67, clozeNonNeutral := some 87
  , freqRatio := some ((-12/100)), lsaRelatedness := some (79/100)
  , semanticDistance := (583/100), bounded := true }

/-- ⟨possible, certain⟩ -/
def possibleCertain : ScaleDatum :=
  { weakerTerm := "possible", strongerTerm := "certain"
  , category := .adjective
  , siRateExp1 := 92, siRateExp2 := 93
  , clozeNeutral := some 55, clozeNonNeutral := some 31
  , freqRatio := some (10/100), lsaRelatedness := some (42/100)
  , semanticDistance := (565/100), bounded := true }

/-- ⟨may, will⟩ -/
def mayWill : ScaleDatum :=
  { weakerTerm := "may", strongerTerm := "will"
  , category := .auxiliaryVerb
  , siRateExp1 := 87, siRateExp2 := 89
  , clozeNeutral := some 83, clozeNonNeutral := some 80
  , freqRatio := some (68/100), lsaRelatedness := some (51/100)
  , semanticDistance := (541/100), bounded := true }

/-- ⟨difficult, impossible⟩ -/
def difficultImpossible : ScaleDatum :=
  { weakerTerm := "difficult", strongerTerm := "impossible"
  , category := .adjective
  , siRateExp1 := 79, siRateExp2 := 96
  , clozeNeutral := some 13, clozeNonNeutral := some 10
  , freqRatio := some (46/100), lsaRelatedness := some (60/100)
  , semanticDistance := (622/100), bounded := true }

/-- ⟨rare, extinct⟩ -/
def rareExtinct : ScaleDatum :=
  { weakerTerm := "rare", strongerTerm := "extinct"
  , category := .adjective
  , siRateExp1 := 79, siRateExp2 := 79
  , clozeNeutral := some 40, clozeNonNeutral := some 34
  , freqRatio := some (105/100), lsaRelatedness := some (29/100)
  , semanticDistance := (583/100), bounded := true }

/-- ⟨may, have to⟩ -/
def mayHaveTo : ScaleDatum :=
  { weakerTerm := "may", strongerTerm := "have to"
  , category := .auxiliaryVerb
  , siRateExp1 := 75, siRateExp2 := 71
  , clozeNeutral := some 83, clozeNonNeutral := some 80
  , freqRatio := some ((-122/100)), lsaRelatedness := some (64/100)
  , semanticDistance := (526/100), bounded := true }

/-- ⟨warm, hot⟩ -/
def warmHot : ScaleDatum :=
  { weakerTerm := "warm", strongerTerm := "hot"
  , category := .adjective
  , siRateExp1 := 75, siRateExp2 := 64
  , clozeNeutral := some 70, clozeNonNeutral := some 38
  , freqRatio := some ((-28/100)), lsaRelatedness := some (51/100)
  , semanticDistance := (500/100), bounded := false }

/-- ⟨few, none⟩ -/
def fewNone : ScaleDatum :=
  { weakerTerm := "few", strongerTerm := "none"
  , category := .quantifier
  , siRateExp1 := 75, siRateExp2 := 54
  , clozeNeutral := some 20, clozeNonNeutral := some 30
  , freqRatio := some (75/100), lsaRelatedness := some (47/100)
  , semanticDistance := (535/100), bounded := true }

/-- ⟨low, depleted⟩ -/
def lowDepleted : ScaleDatum :=
  { weakerTerm := "low", strongerTerm := "depleted"
  , category := .adjective
  , siRateExp1 := 71, siRateExp2 := 79
  , clozeNeutral := some 23, clozeNonNeutral := some 60
  , freqRatio := some (229/100), lsaRelatedness := some (16/100)
  , semanticDistance := (487/100), bounded := true }

/-- ⟨hard, unsolvable⟩ -/
def hardUnsolvable : ScaleDatum :=
  { weakerTerm := "hard", strongerTerm := "unsolvable"
  , category := .adjective
  , siRateExp1 := 71, siRateExp2 := 71
  , clozeNeutral := some 10, clozeNonNeutral := some 10
  , freqRatio := some (287/100), lsaRelatedness := some (8/100)
  , semanticDistance := (526/100), bounded := true }

/-- ⟨allowed, obligatory⟩ -/
def allowedObligatory : ScaleDatum :=
  { weakerTerm := "allowed", strongerTerm := "obligatory"
  , category := .adjective
  , siRateExp1 := 67, siRateExp2 := 82
  , clozeNeutral := some 20, clozeNonNeutral := some 47
  , freqRatio := some ((-85/100)), lsaRelatedness := some (2/100)
  , semanticDistance := (535/100), bounded := true }

/-- ⟨scarce, unavailable⟩ -/
def scarceUnavailable : ScaleDatum :=
  { weakerTerm := "scarce", strongerTerm := "unavailable"
  , category := .adjective
  , siRateExp1 := 62, siRateExp2 := 57
  , clozeNeutral := some 40, clozeNonNeutral := some 17
  , freqRatio := some (29/100), lsaRelatedness := some (18/100)
  , semanticDistance := (478/100), bounded := true }

/-- ⟨try, succeed⟩ -/
def trySucceed : ScaleDatum :=
  { weakerTerm := "try", strongerTerm := "succeed"
  , category := .mainVerb
  , siRateExp1 := 62, siRateExp2 := 39
  , clozeNeutral := some 37, clozeNonNeutral := some 57
  , freqRatio := some (123/100), lsaRelatedness := some (35/100)
  , semanticDistance := (582/100), bounded := true }

/-- ⟨palatable, delicious⟩ -/
def palatableDelicious : ScaleDatum :=
  { weakerTerm := "palatable", strongerTerm := "delicious"
  , category := .adjective
  , siRateExp1 := 58, siRateExp2 := 61
  , clozeNeutral := some 67, clozeNonNeutral := some 47
  , freqRatio := some ((-89/100)), lsaRelatedness := some (32/100)
  , semanticDistance := (552/100), bounded := false }

/-- ⟨memorable, unforgettable⟩ -/
def memorableUnforgettable : ScaleDatum :=
  { weakerTerm := "memorable", strongerTerm := "unforgettable"
  , category := .adjective
  , siRateExp1 := 50, siRateExp2 := 54
  , clozeNeutral := some 23, clozeNonNeutral := some 60
  , freqRatio := some (56/100), lsaRelatedness := some (29/100)
  , semanticDistance := (483/100), bounded := true }

/-- ⟨like, love⟩ -/
def likeLove : ScaleDatum :=
  { weakerTerm := "like", strongerTerm := "love"
  , category := .mainVerb
  , siRateExp1 := 50, siRateExp2 := 25
  , clozeNeutral := some 80, clozeNonNeutral := some 57
  , freqRatio := some (23/100), lsaRelatedness := some (37/100)
  , semanticDistance := (574/100), bounded := false }

/-- ⟨good, perfect⟩ -/
def goodPerfect : ScaleDatum :=
  { weakerTerm := "good", strongerTerm := "perfect"
  , category := .adjective
  , siRateExp1 := 46, siRateExp2 := 39
  , clozeNeutral := some 60, clozeNonNeutral := some 23
  , freqRatio := some (100/100), lsaRelatedness := some (42/100)
  , semanticDistance := (609/100), bounded := true }

/-- ⟨good, excellent⟩ -/
def goodExcellent : ScaleDatum :=
  { weakerTerm := "good", strongerTerm := "excellent"
  , category := .adjective
  , siRateExp1 := 37, siRateExp2 := 32
  , clozeNeutral := some 60, clozeNonNeutral := some 57
  , freqRatio := some (134/100), lsaRelatedness := some (46/100)
  , semanticDistance := (548/100), bounded := false }

/-- ⟨cool, cold⟩ -/
def coolCold : ScaleDatum :=
  { weakerTerm := "cool", strongerTerm := "cold"
  , category := .adjective
  , siRateExp1 := 33, siRateExp2 := 46
  , clozeNeutral := some 23, clozeNonNeutral := some 40
  , freqRatio := some ((-21/100)), lsaRelatedness := some (61/100)
  , semanticDistance := (430/100), bounded := false }

/-- ⟨hungry, starving⟩ -/
def hungryStarving : ScaleDatum :=
  { weakerTerm := "hungry", strongerTerm := "starving"
  , category := .adjective
  , siRateExp1 := 33, siRateExp2 := 25
  , clozeNeutral := some 63, clozeNonNeutral := some 40
  , freqRatio := some (71/100), lsaRelatedness := some (52/100)
  , semanticDistance := (574/100), bounded := false }

/-- ⟨adequate, good⟩ -/
def adequateGood : ScaleDatum :=
  { weakerTerm := "adequate", strongerTerm := "good"
  , category := .adjective
  , siRateExp1 := 29, siRateExp2 := 32
  , clozeNeutral := some 33, clozeNonNeutral := some 57
  , freqRatio := some ((-152/100)), lsaRelatedness := some (27/100)
  , semanticDistance := (352/100), bounded := false }

/-- ⟨unsettling, horrific⟩ -/
def unsettlingHorrific : ScaleDatum :=
  { weakerTerm := "unsettling", strongerTerm := "horrific"
  , category := .adjective
  , siRateExp1 := 29, siRateExp2 := 25
  , clozeNeutral := some 37, clozeNonNeutral := some 37
  , freqRatio := some ((-48/100)), lsaRelatedness := none  -- NA in paper
  , semanticDistance := (565/100), bounded := false }

/-- ⟨dislike, loathe⟩ -/
def dislikeLoathe : ScaleDatum :=
  { weakerTerm := "dislike", strongerTerm := "loathe"
  , category := .mainVerb
  , siRateExp1 := 29, siRateExp2 := 18
  , clozeNeutral := some 93, clozeNonNeutral := some 90
  , freqRatio := some (46/100), lsaRelatedness := some (16/100)
  , semanticDistance := (587/100), bounded := false }

/-- ⟨believe, know⟩ -/
def believeKnow : ScaleDatum :=
  { weakerTerm := "believe", strongerTerm := "know"
  , category := .mainVerb
  , siRateExp1 := 21, siRateExp2 := 61
  , clozeNeutral := some 67, clozeNonNeutral := some 67
  , freqRatio := some ((-70/100)), lsaRelatedness := some (46/100)
  , semanticDistance := (504/100), bounded := true }

/-- ⟨start, finish⟩ -/
def startFinish : ScaleDatum :=
  { weakerTerm := "start", strongerTerm := "finish"
  , category := .mainVerb
  , siRateExp1 := 21, siRateExp2 := 21
  , clozeNeutral := some 43, clozeNonNeutral := some 50
  , freqRatio := some (70/100), lsaRelatedness := some (40/100)
  , semanticDistance := (495/100), bounded := true }

/-- ⟨participate, win⟩ -/
def participateWin : ScaleDatum :=
  { weakerTerm := "participate", strongerTerm := "win"
  , category := .mainVerb
  , siRateExp1 := 21, siRateExp2 := 18
  , clozeNeutral := some 7, clozeNonNeutral := some 37
  , freqRatio := some ((-62/100)), lsaRelatedness := some (21/100)
  , semanticDistance := (635/100), bounded := true }

/-- ⟨wary, scared⟩ -/
def waryScared : ScaleDatum :=
  { weakerTerm := "wary", strongerTerm := "scared"
  , category := .adjective
  , siRateExp1 := 21, siRateExp2 := 14
  , clozeNeutral := some 40, clozeNonNeutral := some 37
  , freqRatio := some ((-48/100)), lsaRelatedness := some (6/100)
  , semanticDistance := (439/100), bounded := false }

/-- ⟨old, ancient⟩ -/
def oldAncient : ScaleDatum :=
  { weakerTerm := "old", strongerTerm := "ancient"
  , category := .adjective
  , siRateExp1 := 17, siRateExp2 := 36
  , clozeNeutral := some 50, clozeNonNeutral := some 33
  , freqRatio := some (108/100), lsaRelatedness := some (24/100)
  , semanticDistance := (539/100), bounded := false }

/-- ⟨big, enormous⟩ -/
def bigEnormous : ScaleDatum :=
  { weakerTerm := "big", strongerTerm := "enormous"
  , category := .adjective
  , siRateExp1 := 17, siRateExp2 := 21
  , clozeNeutral := some 83, clozeNonNeutral := some 37
  , freqRatio := some (113/100), lsaRelatedness := some (21/100)
  , semanticDistance := (543/100), bounded := false }

/-- ⟨snug, tight⟩ -/
def snugTight : ScaleDatum :=
  { weakerTerm := "snug", strongerTerm := "tight"
  , category := .adjective
  , siRateExp1 := 12, siRateExp2 := 21
  , clozeNeutral := some 87, clozeNonNeutral := some 87
  , freqRatio := some ((-105/100)), lsaRelatedness := some (30/100)
  , semanticDistance := (286/100), bounded := false }

/-- ⟨attractive, stunning⟩ -/
def attractiveStunning : ScaleDatum :=
  { weakerTerm := "attractive", strongerTerm := "stunning"
  , category := .adjective
  , siRateExp1 := 8, siRateExp2 := 21
  , clozeNeutral := some 53, clozeNonNeutral := some 72
  , freqRatio := some (37/100), lsaRelatedness := some (7/100)
  , semanticDistance := (578/100), bounded := false }

/-- ⟨special, unique⟩ -/
def specialUnique : ScaleDatum :=
  { weakerTerm := "special", strongerTerm := "unique"
  , category := .adjective
  , siRateExp1 := 8, siRateExp2 := 14
  , clozeNeutral := some 50, clozeNonNeutral := some 30
  , freqRatio := some (54/100), lsaRelatedness := some (32/100)
  , semanticDistance := (348/100), bounded := true }

/-- ⟨pretty, beautiful⟩ -/
def prettyBeautiful : ScaleDatum :=
  { weakerTerm := "pretty", strongerTerm := "beautiful"
  , category := .adjective
  , siRateExp1 := 8, siRateExp2 := 11
  , clozeNeutral := some 73, clozeNonNeutral := some 50
  , freqRatio := some ((-46/100)), lsaRelatedness := some (41/100)
  , semanticDistance := (504/100), bounded := false }

/-- ⟨intelligent, brilliant⟩ -/
def intelligentBrilliant : ScaleDatum :=
  { weakerTerm := "intelligent", strongerTerm := "brilliant"
  , category := .adjective
  , siRateExp1 := 8, siRateExp2 := 7
  , clozeNeutral := some 17, clozeNonNeutral := some 3
  , freqRatio := some ((-12/100)), lsaRelatedness := some (27/100)
  , semanticDistance := (474/100), bounded := false }

/-- ⟨funny, hilarious⟩ -/
def funnyHilarious : ScaleDatum :=
  { weakerTerm := "funny", strongerTerm := "hilarious"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 29
  , clozeNeutral := some 50, clozeNonNeutral := some 33
  , freqRatio := some (117/100), lsaRelatedness := some (7/100)
  , semanticDistance := (504/100), bounded := false }

/-- ⟨dark, black⟩ -/
def darkBlack : ScaleDatum :=
  { weakerTerm := "dark", strongerTerm := "black"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 29
  , clozeNeutral := some 30, clozeNonNeutral := some 27
  , freqRatio := some ((-49/100)), lsaRelatedness := some (40/100)
  , semanticDistance := (404/100), bounded := true }

/-- ⟨small, tiny⟩ -/
def smallTiny : ScaleDatum :=
  { weakerTerm := "small", strongerTerm := "tiny"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 25
  , clozeNeutral := some 80, clozeNonNeutral := some 27
  , freqRatio := some (80/100), lsaRelatedness := some (54/100)
  , semanticDistance := (422/100), bounded := false }

/-- ⟨ugly, hideous⟩ -/
def uglyHideous : ScaleDatum :=
  { weakerTerm := "ugly", strongerTerm := "hideous"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 18
  , clozeNeutral := some 37, clozeNonNeutral := some 31
  , freqRatio := some (86/100), lsaRelatedness := some (48/100)
  , semanticDistance := (527/100), bounded := false }

/-- ⟨silly, ridiculous⟩ -/
def sillyRidiculous : ScaleDatum :=
  { weakerTerm := "silly", strongerTerm := "ridiculous"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 14
  , clozeNeutral := some 77, clozeNonNeutral := some 40
  , freqRatio := some (1/100), lsaRelatedness := some (43/100)
  , semanticDistance := (417/100), bounded := false }

/-- ⟨tired, exhausted⟩ -/
def tiredExhausted : ScaleDatum :=
  { weakerTerm := "tired", strongerTerm := "exhausted"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 14
  , clozeNeutral := some 57, clozeNonNeutral := some 41
  , freqRatio := some (92/100), lsaRelatedness := some (45/100)
  , semanticDistance := (513/100), bounded := false }

/-- ⟨content, happy⟩ - lowest SI rate (4%) -/
def contentHappy : ScaleDatum :=
  { weakerTerm := "content", strongerTerm := "happy"
  , category := .adjective
  , siRateExp1 := 4, siRateExp2 := 4
  , clozeNeutral := some 87, clozeNonNeutral := some 50
  , freqRatio := some ((-85/100)), lsaRelatedness := some (13/100)
  , semanticDistance := (452/100), bounded := false }

end Scales

/-- All 43 scales tested in [van-tiel-geurts-2016] -/
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
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Bounded scales yield far more SIs than non-bounded scales.

Total SI rate (Exp 1) across 21 bounded scales: 1287%.
Total SI rate (Exp 1) across 22 non-bounded scales: 465%.
Even though bounded scales have *fewer* items, their total is nearly 3× higher.
The paper reports mean bounded ≈ 62% vs mean non-bounded ≈ 25%. -/
theorem bounded_total_exceeds_nonbounded :
    (boundedScales.map (·.siRateExp1)).foldl (· + ·) 0 >
    (nonBoundedScales.map (·.siRateExp1)).foldl (· + ·) 0 := by decide

/-- ⟨some, all⟩ — the "workhorse" of SI research — sits near the top at 96%,
far above the mean. Generalizing from ⟨some, all⟩ to all scales is unjustified. -/
theorem someAll_above_median :
    Scales.someAll.siRateExp1 > 50 := by decide

/-- In this sample, every closed-class scale is also bounded.
This confound partially explains the nonsignificant grammatical-class effect:
closed-class scales look high-SI because they're all bounded, not because
the search space for alternatives is smaller. -/
theorem closed_class_subsumes_bounded :
    allScales.all (λ s => !s.category.isClosedClass || s.bounded) = true := by
  decide

/-- Experiments 1 and 2 agree directionally: no scale reverses from high to low
or vice versa (defined as >50% in one experiment and <15% in the other). -/
theorem exp1_exp2_directional_agreement :
    allScales.all (λ s =>
      !(s.siRateExp1 > 50 && s.siRateExp2 < 15) &&
      !(s.siRateExp2 > 50 && s.siRateExp1 < 15)) = true := by
  decide

/-! ### Explaining diversity: distinctness, not availability

The mixed model (Table 5) regressed SI rates on six predictors. Of these, only
the two **distinctness** measures are significant: semantic distance (β = 0.65,
SE = 0.27, Z = 2.36, p = .018, R² = .027) and boundedness (β = −1.87, SE = 0.40,
Z = −4.72, p < .001, R² = .108 — the negative sign reflects bounded = 1 against a
"no" = 1 dependent variable, i.e. bounded scales project *more*). The four
**availability** measures are all null: association strength (β = 0.16, p = .611),
grammatical class (β = −0.38, p = .606), relative word frequency (β = −0.15,
p = .461), and LSA relatedness (β = 0.01, p = .355). The full model explains
R² = .52 (.22 fixed); boundedness alone accounts for ≈ 10× the variance of all
availability measures combined. Effect sizes stay in prose; the qualitative
content is carried structurally by `bounded_total_exceeds_nonbounded` (the
dominant distinctness factor, read directly off the SI data) and
`closed_class_subsumes_bounded` (why the grammatical-class availability measure is
confounded out once boundedness is in the model). -/

-- ============================================================================
-- The two-stage model of scalar inference (§6)
-- ============================================================================

/-! Following [soames-1982] and [sauerland-2004], a scalar inference from φ[α] to
¬φ[β] is computed in two steps. The *primary* step yields that the speaker does
not believe the stronger alternative (¬Bel_S φ[β]). A *competence* assumption —
the speaker is opinionated about φ[β] (Bel_S φ[β] ∨ Bel_S ¬φ[β]) — upgrades this
to the scalar inference Bel_S ¬φ[β]. Scalar diversity is then variation in whether
the competence step fires: it is better warranted when the scalemates are
*distinct* (bounded or semantically distant), so that the speaker is plausibly
opinionated about the stronger term — which is exactly why distinctness, not
availability, predicts the rates. -/

/-- The two-stage (epistemic) model: the primary inference together with the
    competence assumption *yields* the scalar inference. The conclusion is derived
    from the premises, not stipulated. -/
theorem two_stage_inference {belStronger belNotStronger : Prop}
    (primary : ¬ belStronger) (competence : belStronger ∨ belNotStronger) :
    belNotStronger :=
  competence.resolve_left primary

/-- Competence is load-bearing: the primary step alone leaves the stronger
    alternative epistemically open (the speaker may be agnostic), so no scalar
    inference follows. Cross-scale variation in this step is where diversity
    lives. -/
theorem primary_underdetermines_si :
    ∃ belStronger belNotStronger : Prop, ¬ belStronger ∧ ¬ belNotStronger :=
  ⟨False, False, not_false, not_false⟩

end VanTielEtAl2016
