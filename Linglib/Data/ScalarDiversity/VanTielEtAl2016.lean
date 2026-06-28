import Linglib.Data.ScalarDiversity.Schema

/-!
# VanTielEtAl2016 — scalar-diversity data (generated)
[van-tiel-geurts-2016]

Auto-generated from `Linglib/Data/ScalarDiversity/VanTielEtAl2016.json` by
`scripts/gen_scalardiversity.py`. **Do not edit by hand** — edit the JSON and
re-run the generator. The 43 lexical scales of [van-tiel-geurts-2016]
(Table 3): SI rates, cloze rates, frequency ratio, LSA relatedness, semantic
distance, and boundedness.
-/

namespace VanTielEtAl2016

namespace Scales

def cheapFree : ScaleDatum :=
  { weakerTerm := "cheap", strongerTerm := "free", category := .adjective,
    siRateExp1 := 100, siRateExp2 := 93,
    clozeNeutral := some 0, clozeNonNeutral := some 0,
    freqRatio := some (-66/100), lsaRelatedness := some (19/100),
    semanticDistance := 552/100, bounded := true }

def sometimesAlways : ScaleDatum :=
  { weakerTerm := "sometimes", strongerTerm := "always", category := .adverb,
    siRateExp1 := 100, siRateExp2 := 86,
    clozeNeutral := some 80, clozeNonNeutral := some 90,
    freqRatio := some (-105/100), lsaRelatedness := some (60/100),
    semanticDistance := 570/100, bounded := true }

def someAll : ScaleDatum :=
  { weakerTerm := "some", strongerTerm := "all", category := .quantifier,
    siRateExp1 := 96, siRateExp2 := 89,
    clozeNeutral := some 67, clozeNonNeutral := some 87,
    freqRatio := some (-12/100), lsaRelatedness := some (79/100),
    semanticDistance := 583/100, bounded := true }

def possibleCertain : ScaleDatum :=
  { weakerTerm := "possible", strongerTerm := "certain", category := .adjective,
    siRateExp1 := 92, siRateExp2 := 93,
    clozeNeutral := some 55, clozeNonNeutral := some 31,
    freqRatio := some (10/100), lsaRelatedness := some (42/100),
    semanticDistance := 565/100, bounded := true }

def mayWill : ScaleDatum :=
  { weakerTerm := "may", strongerTerm := "will", category := .auxiliaryVerb,
    siRateExp1 := 87, siRateExp2 := 89,
    clozeNeutral := some 83, clozeNonNeutral := some 80,
    freqRatio := some (68/100), lsaRelatedness := some (51/100),
    semanticDistance := 541/100, bounded := true }

def difficultImpossible : ScaleDatum :=
  { weakerTerm := "difficult", strongerTerm := "impossible", category := .adjective,
    siRateExp1 := 79, siRateExp2 := 96,
    clozeNeutral := some 13, clozeNonNeutral := some 10,
    freqRatio := some (46/100), lsaRelatedness := some (60/100),
    semanticDistance := 622/100, bounded := true }

def rareExtinct : ScaleDatum :=
  { weakerTerm := "rare", strongerTerm := "extinct", category := .adjective,
    siRateExp1 := 79, siRateExp2 := 79,
    clozeNeutral := some 40, clozeNonNeutral := some 34,
    freqRatio := some (105/100), lsaRelatedness := some (29/100),
    semanticDistance := 583/100, bounded := true }

def mayHaveTo : ScaleDatum :=
  { weakerTerm := "may", strongerTerm := "have to", category := .auxiliaryVerb,
    siRateExp1 := 75, siRateExp2 := 71,
    clozeNeutral := some 83, clozeNonNeutral := some 80,
    freqRatio := some (-122/100), lsaRelatedness := some (64/100),
    semanticDistance := 526/100, bounded := true }

def warmHot : ScaleDatum :=
  { weakerTerm := "warm", strongerTerm := "hot", category := .adjective,
    siRateExp1 := 75, siRateExp2 := 64,
    clozeNeutral := some 70, clozeNonNeutral := some 38,
    freqRatio := some (-28/100), lsaRelatedness := some (51/100),
    semanticDistance := 500/100, bounded := false }

def fewNone : ScaleDatum :=
  { weakerTerm := "few", strongerTerm := "none", category := .quantifier,
    siRateExp1 := 75, siRateExp2 := 54,
    clozeNeutral := some 20, clozeNonNeutral := some 30,
    freqRatio := some (75/100), lsaRelatedness := some (47/100),
    semanticDistance := 535/100, bounded := true }

def lowDepleted : ScaleDatum :=
  { weakerTerm := "low", strongerTerm := "depleted", category := .adjective,
    siRateExp1 := 71, siRateExp2 := 79,
    clozeNeutral := some 23, clozeNonNeutral := some 60,
    freqRatio := some (229/100), lsaRelatedness := some (16/100),
    semanticDistance := 487/100, bounded := true }

def hardUnsolvable : ScaleDatum :=
  { weakerTerm := "hard", strongerTerm := "unsolvable", category := .adjective,
    siRateExp1 := 71, siRateExp2 := 71,
    clozeNeutral := some 10, clozeNonNeutral := some 10,
    freqRatio := some (287/100), lsaRelatedness := some (8/100),
    semanticDistance := 526/100, bounded := true }

def allowedObligatory : ScaleDatum :=
  { weakerTerm := "allowed", strongerTerm := "obligatory", category := .adjective,
    siRateExp1 := 67, siRateExp2 := 82,
    clozeNeutral := some 20, clozeNonNeutral := some 47,
    freqRatio := some (-85/100), lsaRelatedness := some (2/100),
    semanticDistance := 535/100, bounded := true }

def scarceUnavailable : ScaleDatum :=
  { weakerTerm := "scarce", strongerTerm := "unavailable", category := .adjective,
    siRateExp1 := 62, siRateExp2 := 57,
    clozeNeutral := some 40, clozeNonNeutral := some 17,
    freqRatio := some (29/100), lsaRelatedness := some (18/100),
    semanticDistance := 478/100, bounded := true }

def trySucceed : ScaleDatum :=
  { weakerTerm := "try", strongerTerm := "succeed", category := .mainVerb,
    siRateExp1 := 62, siRateExp2 := 39,
    clozeNeutral := some 37, clozeNonNeutral := some 57,
    freqRatio := some (123/100), lsaRelatedness := some (35/100),
    semanticDistance := 582/100, bounded := true }

def palatableDelicious : ScaleDatum :=
  { weakerTerm := "palatable", strongerTerm := "delicious", category := .adjective,
    siRateExp1 := 58, siRateExp2 := 61,
    clozeNeutral := some 67, clozeNonNeutral := some 47,
    freqRatio := some (-89/100), lsaRelatedness := some (32/100),
    semanticDistance := 552/100, bounded := false }

def memorableUnforgettable : ScaleDatum :=
  { weakerTerm := "memorable", strongerTerm := "unforgettable", category := .adjective,
    siRateExp1 := 50, siRateExp2 := 54,
    clozeNeutral := some 23, clozeNonNeutral := some 60,
    freqRatio := some (56/100), lsaRelatedness := some (29/100),
    semanticDistance := 483/100, bounded := true }

def likeLove : ScaleDatum :=
  { weakerTerm := "like", strongerTerm := "love", category := .mainVerb,
    siRateExp1 := 50, siRateExp2 := 25,
    clozeNeutral := some 80, clozeNonNeutral := some 57,
    freqRatio := some (23/100), lsaRelatedness := some (37/100),
    semanticDistance := 574/100, bounded := false }

def goodPerfect : ScaleDatum :=
  { weakerTerm := "good", strongerTerm := "perfect", category := .adjective,
    siRateExp1 := 46, siRateExp2 := 39,
    clozeNeutral := some 60, clozeNonNeutral := some 23,
    freqRatio := some (100/100), lsaRelatedness := some (42/100),
    semanticDistance := 609/100, bounded := true }

def goodExcellent : ScaleDatum :=
  { weakerTerm := "good", strongerTerm := "excellent", category := .adjective,
    siRateExp1 := 37, siRateExp2 := 32,
    clozeNeutral := some 60, clozeNonNeutral := some 57,
    freqRatio := some (134/100), lsaRelatedness := some (46/100),
    semanticDistance := 548/100, bounded := false }

def coolCold : ScaleDatum :=
  { weakerTerm := "cool", strongerTerm := "cold", category := .adjective,
    siRateExp1 := 33, siRateExp2 := 46,
    clozeNeutral := some 23, clozeNonNeutral := some 40,
    freqRatio := some (-21/100), lsaRelatedness := some (61/100),
    semanticDistance := 430/100, bounded := false }

def hungryStarving : ScaleDatum :=
  { weakerTerm := "hungry", strongerTerm := "starving", category := .adjective,
    siRateExp1 := 33, siRateExp2 := 25,
    clozeNeutral := some 63, clozeNonNeutral := some 40,
    freqRatio := some (71/100), lsaRelatedness := some (52/100),
    semanticDistance := 574/100, bounded := false }

def adequateGood : ScaleDatum :=
  { weakerTerm := "adequate", strongerTerm := "good", category := .adjective,
    siRateExp1 := 29, siRateExp2 := 32,
    clozeNeutral := some 33, clozeNonNeutral := some 57,
    freqRatio := some (-152/100), lsaRelatedness := some (27/100),
    semanticDistance := 352/100, bounded := false }

def unsettlingHorrific : ScaleDatum :=
  { weakerTerm := "unsettling", strongerTerm := "horrific", category := .adjective,
    siRateExp1 := 29, siRateExp2 := 25,
    clozeNeutral := some 37, clozeNonNeutral := some 37,
    freqRatio := some (-48/100), lsaRelatedness := none,
    semanticDistance := 565/100, bounded := false }

def dislikeLoathe : ScaleDatum :=
  { weakerTerm := "dislike", strongerTerm := "loathe", category := .mainVerb,
    siRateExp1 := 29, siRateExp2 := 18,
    clozeNeutral := some 93, clozeNonNeutral := some 90,
    freqRatio := some (46/100), lsaRelatedness := some (16/100),
    semanticDistance := 587/100, bounded := false }

def believeKnow : ScaleDatum :=
  { weakerTerm := "believe", strongerTerm := "know", category := .mainVerb,
    siRateExp1 := 21, siRateExp2 := 61,
    clozeNeutral := some 67, clozeNonNeutral := some 67,
    freqRatio := some (-70/100), lsaRelatedness := some (46/100),
    semanticDistance := 504/100, bounded := true }

def startFinish : ScaleDatum :=
  { weakerTerm := "start", strongerTerm := "finish", category := .mainVerb,
    siRateExp1 := 21, siRateExp2 := 21,
    clozeNeutral := some 43, clozeNonNeutral := some 50,
    freqRatio := some (70/100), lsaRelatedness := some (40/100),
    semanticDistance := 495/100, bounded := true }

def participateWin : ScaleDatum :=
  { weakerTerm := "participate", strongerTerm := "win", category := .mainVerb,
    siRateExp1 := 21, siRateExp2 := 18,
    clozeNeutral := some 7, clozeNonNeutral := some 37,
    freqRatio := some (-62/100), lsaRelatedness := some (21/100),
    semanticDistance := 635/100, bounded := true }

def waryScared : ScaleDatum :=
  { weakerTerm := "wary", strongerTerm := "scared", category := .adjective,
    siRateExp1 := 21, siRateExp2 := 14,
    clozeNeutral := some 40, clozeNonNeutral := some 37,
    freqRatio := some (-48/100), lsaRelatedness := some (6/100),
    semanticDistance := 439/100, bounded := false }

def oldAncient : ScaleDatum :=
  { weakerTerm := "old", strongerTerm := "ancient", category := .adjective,
    siRateExp1 := 17, siRateExp2 := 36,
    clozeNeutral := some 50, clozeNonNeutral := some 33,
    freqRatio := some (108/100), lsaRelatedness := some (24/100),
    semanticDistance := 539/100, bounded := false }

def bigEnormous : ScaleDatum :=
  { weakerTerm := "big", strongerTerm := "enormous", category := .adjective,
    siRateExp1 := 17, siRateExp2 := 21,
    clozeNeutral := some 83, clozeNonNeutral := some 37,
    freqRatio := some (113/100), lsaRelatedness := some (21/100),
    semanticDistance := 543/100, bounded := false }

def snugTight : ScaleDatum :=
  { weakerTerm := "snug", strongerTerm := "tight", category := .adjective,
    siRateExp1 := 12, siRateExp2 := 21,
    clozeNeutral := some 87, clozeNonNeutral := some 87,
    freqRatio := some (-105/100), lsaRelatedness := some (30/100),
    semanticDistance := 286/100, bounded := false }

def attractiveStunning : ScaleDatum :=
  { weakerTerm := "attractive", strongerTerm := "stunning", category := .adjective,
    siRateExp1 := 8, siRateExp2 := 21,
    clozeNeutral := some 53, clozeNonNeutral := some 72,
    freqRatio := some (37/100), lsaRelatedness := some (7/100),
    semanticDistance := 578/100, bounded := false }

def specialUnique : ScaleDatum :=
  { weakerTerm := "special", strongerTerm := "unique", category := .adjective,
    siRateExp1 := 8, siRateExp2 := 14,
    clozeNeutral := some 50, clozeNonNeutral := some 30,
    freqRatio := some (54/100), lsaRelatedness := some (32/100),
    semanticDistance := 348/100, bounded := true }

def prettyBeautiful : ScaleDatum :=
  { weakerTerm := "pretty", strongerTerm := "beautiful", category := .adjective,
    siRateExp1 := 8, siRateExp2 := 11,
    clozeNeutral := some 73, clozeNonNeutral := some 50,
    freqRatio := some (-46/100), lsaRelatedness := some (41/100),
    semanticDistance := 504/100, bounded := false }

def intelligentBrilliant : ScaleDatum :=
  { weakerTerm := "intelligent", strongerTerm := "brilliant", category := .adjective,
    siRateExp1 := 8, siRateExp2 := 7,
    clozeNeutral := some 17, clozeNonNeutral := some 3,
    freqRatio := some (-12/100), lsaRelatedness := some (27/100),
    semanticDistance := 474/100, bounded := false }

def funnyHilarious : ScaleDatum :=
  { weakerTerm := "funny", strongerTerm := "hilarious", category := .adjective,
    siRateExp1 := 4, siRateExp2 := 29,
    clozeNeutral := some 50, clozeNonNeutral := some 33,
    freqRatio := some (117/100), lsaRelatedness := some (7/100),
    semanticDistance := 504/100, bounded := false }

def darkBlack : ScaleDatum :=
  { weakerTerm := "dark", strongerTerm := "black", category := .adjective,
    siRateExp1 := 4, siRateExp2 := 29,
    clozeNeutral := some 30, clozeNonNeutral := some 27,
    freqRatio := some (-49/100), lsaRelatedness := some (40/100),
    semanticDistance := 404/100, bounded := true }

def smallTiny : ScaleDatum :=
  { weakerTerm := "small", strongerTerm := "tiny", category := .adjective,
    siRateExp1 := 4, siRateExp2 := 25,
    clozeNeutral := some 80, clozeNonNeutral := some 27,
    freqRatio := some (80/100), lsaRelatedness := some (54/100),
    semanticDistance := 422/100, bounded := false }

def uglyHideous : ScaleDatum :=
  { weakerTerm := "ugly", strongerTerm := "hideous", category := .adjective,
    siRateExp1 := 4, siRateExp2 := 18,
    clozeNeutral := some 37, clozeNonNeutral := some 31,
    freqRatio := some (86/100), lsaRelatedness := some (48/100),
    semanticDistance := 527/100, bounded := false }

def sillyRidiculous : ScaleDatum :=
  { weakerTerm := "silly", strongerTerm := "ridiculous", category := .adjective,
    siRateExp1 := 4, siRateExp2 := 14,
    clozeNeutral := some 77, clozeNonNeutral := some 40,
    freqRatio := some (1/100), lsaRelatedness := some (43/100),
    semanticDistance := 417/100, bounded := false }

def tiredExhausted : ScaleDatum :=
  { weakerTerm := "tired", strongerTerm := "exhausted", category := .adjective,
    siRateExp1 := 4, siRateExp2 := 14,
    clozeNeutral := some 57, clozeNonNeutral := some 41,
    freqRatio := some (92/100), lsaRelatedness := some (45/100),
    semanticDistance := 513/100, bounded := false }

def contentHappy : ScaleDatum :=
  { weakerTerm := "content", strongerTerm := "happy", category := .adjective,
    siRateExp1 := 4, siRateExp2 := 4,
    clozeNeutral := some 87, clozeNonNeutral := some 50,
    freqRatio := some (-85/100), lsaRelatedness := some (13/100),
    semanticDistance := 452/100, bounded := false }

end Scales

/-- All 43 lexical scales ([van-tiel-geurts-2016], Table 3). -/
def allScales : List ScaleDatum :=
  [Scales.cheapFree, Scales.sometimesAlways, Scales.someAll, Scales.possibleCertain, Scales.mayWill, Scales.difficultImpossible, Scales.rareExtinct, Scales.mayHaveTo, Scales.warmHot, Scales.fewNone, Scales.lowDepleted, Scales.hardUnsolvable, Scales.allowedObligatory, Scales.scarceUnavailable, Scales.trySucceed, Scales.palatableDelicious, Scales.memorableUnforgettable, Scales.likeLove, Scales.goodPerfect, Scales.goodExcellent, Scales.coolCold, Scales.hungryStarving, Scales.adequateGood, Scales.unsettlingHorrific, Scales.dislikeLoathe, Scales.believeKnow, Scales.startFinish, Scales.participateWin, Scales.waryScared, Scales.oldAncient, Scales.bigEnormous, Scales.snugTight, Scales.attractiveStunning, Scales.specialUnique, Scales.prettyBeautiful, Scales.intelligentBrilliant, Scales.funnyHilarious, Scales.darkBlack, Scales.smallTiny, Scales.uglyHideous, Scales.sillyRidiculous, Scales.tiredExhausted, Scales.contentHappy]

end VanTielEtAl2016
