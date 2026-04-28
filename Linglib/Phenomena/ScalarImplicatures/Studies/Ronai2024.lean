import Linglib.Phenomena.ScalarImplicatures.Studies.VanTielEtAl2016
import Mathlib.Data.Rat.Defs

/-!
# @cite{ronai-2024} — Embedded Scalar Diversity
@cite{ronai-2024} @cite{van-tiel-geurts-2016} @cite{gotzner-romoli-2018}
@cite{chierchia-2004} @cite{chierchia-fox-spector-2012} @cite{bergen-levy-goodman-2016}
@cite{potts-levy-2015} @cite{sauerland-2004} @cite{geurts-pouscoulous-2009}
@cite{chemla-spector-2011}

The graded-rating sliding-scale paradigm Ronai 2024 adopts (via
@cite{gotzner-romoli-2018}) descends from @cite{chemla-spector-2011}'s
methodological innovation of measuring embedded-SI rates on a
continuous cursor scale rather than via binary inference judgments.
CS11 established that graded TVJ detects local readings that GP09's
binary task missed; Ronai extends the paradigm to test whether the
embedded-SI rate variation across @cite{van-tiel-geurts-2016}'s 42
scales mirrors the global SI variation that VT-G first documented.

Theory-neutral empirical data from @cite{ronai-2024}.

## Central Question

Do embedded scalar implicatures (under universal quantifiers) show the same
cross-scale variation ("scalar diversity") as global SIs? And do the same
properties of alternatives predict this variation?

## Argumentative Structure

1. **Embedded SIs exist** (Exp 1, §3, N=118): Using @cite{gotzner-romoli-2018}'s
   sliding-scale paradigm with 42 scales under *every*, the "strong" condition
   (e.g., "Every soup was warm" → "No soup was hot") is rated significantly
   above the false control (Estimate=−26.12, SE=1.47, t=−17.81, p<.001),
   confirming participants compute embedded SIs.

2. **Embedded scalar diversity mirrors global** (Exp 1, §3.3): Strong inference
   rates vary across the 42 scales and correlate strongly with
   @cite{van-tiel-geurts-2016}'s global SI rates (r=0.76, p<.001).

3. **Alternative-based predictors explain the variation** (Exp 1, §3.3):
   - Semantic distance: Estimate=7.28, SE=3.29, t=2.21, p<.05
   - Boundedness: Estimate=18.37, SE=4.41, t=4.17, p<.001

4. **Binary replication rules out baseline concerns** (Exp 2, §4, N=45):
   Using @cite{van-tiel-geurts-2016}'s Yes/No inference task, the same pattern
   emerges: global–embedded correlation r=0.80 (p<.001), with both semantic
   distance (Estimate=0.63, SE=0.31, z=2.05, p<.05) and boundedness
   (Estimate=1.54, SE=0.39, z=3.91, p<.001) significant.

5. **Alternative-based accounts supported** (§5): Results favor accounts that
   build in scalar alternatives — the grammatical theory (@cite{chierchia-2004};
   @cite{chierchia-fox-spector-2012}), modified neo-Gricean (@cite{sauerland-2004}),
   or neo-Gricean RSA-LU (@cite{potts-levy-2015}) — over unconstrained RSA-LU
   (@cite{bergen-levy-goodman-2016}), which cannot explain why alternative-driven
   variation arises in both global and embedded contexts.

## Data Provenance

Scale properties (global SI rate, semantic distance, boundedness) are imported
from `VanTielEtAl2016.Scales` rather than duplicated. The 42 scales are
@cite{van-tiel-geurts-2016}'s 43 minus ⟨few, none⟩.

Embedded SI rates are computed from the raw data deposited at
https://osf.io/kx42p/ — per-scale means of the "strong" condition
from `exp1_data.csv` (Exp 1, 0–100 sliding scale) and `exp2_data.csv`
(Exp 2, binary Yes/No converted to % "Yes"). Values are rounded to
the nearest integer.
-/

namespace Ronai2024


-- ============================================================================
-- Data Structure
-- ============================================================================

/-- Embedded SI data for a single scale.

Scale properties (global SI rate, semantic distance, boundedness) reference
@cite{van-tiel-geurts-2016} directly rather than duplicating values.
Embedded SI rates are from @cite{ronai-2024}'s two experiments, computed
from the raw data at https://osf.io/kx42p/. -/
structure EmbeddedSIDatum where
  /-- VT2016 scale entry (provides global SI rate, semantic distance, bounded) -/
  vt2016 : VanTielEtAl2016.ScaleDatum
  /-- Mean strong inference rate from Exp 1 (0–100 sliding scale, rounded) -/
  exp1Rate : Nat
  /-- % "Yes" responses in Exp 2 strong condition (rounded) -/
  exp2Rate : Nat
  deriving Repr

/-- Global SI rate from @cite{van-tiel-geurts-2016} Exp 2 (%). -/
def EmbeddedSIDatum.globalSIRate (d : EmbeddedSIDatum) : Nat := d.vt2016.siRateExp2

/-- Semantic distance from @cite{van-tiel-geurts-2016} Exp 4 (1–7 Likert). -/
def EmbeddedSIDatum.semanticDistance (d : EmbeddedSIDatum) : Float :=
  d.vt2016.semanticDistance

/-- Boundedness from @cite{van-tiel-geurts-2016} (author-annotated). -/
def EmbeddedSIDatum.bounded (d : EmbeddedSIDatum) : Bool := d.vt2016.bounded


-- ============================================================================
-- Scale Data (42 scales = VT2016's 43 minus ⟨few, none⟩)
-- ============================================================================

-- Per-scale means computed from raw data at https://osf.io/kx42p/
-- Exp 1: mean of "strong" condition responses (0–100), rounded
-- Exp 2: % "Yes" in strong condition (N=45 per scale), rounded

def someAll : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.someAll
  , exp1Rate := 46, exp2Rate := 40 }

def possibleCertain : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.possibleCertain
  , exp1Rate := 66, exp2Rate := 62 }

def allowedObligatory : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.allowedObligatory
  , exp1Rate := 55, exp2Rate := 49 }

def mayHaveTo : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.mayHaveTo
  , exp1Rate := 67, exp2Rate := 53 }

def mayWill : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.mayWill
  , exp1Rate := 7, exp2Rate := 4 }

def sometimesAlways : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.sometimesAlways
  , exp1Rate := 39, exp2Rate := 33 }

def cheapFree : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.cheapFree
  , exp1Rate := 74, exp2Rate := 49 }

def difficultImpossible : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.difficultImpossible
  , exp1Rate := 43, exp2Rate := 31 }

def hardUnsolvable : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.hardUnsolvable
  , exp1Rate := 49, exp2Rate := 22 }

def rareExtinct : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.rareExtinct
  , exp1Rate := 50, exp2Rate := 33 }

def scarceUnavailable : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.scarceUnavailable
  , exp1Rate := 37, exp2Rate := 20 }

def lowDepleted : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.lowDepleted
  , exp1Rate := 46, exp2Rate := 29 }

def startFinish : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.startFinish
  , exp1Rate := 22, exp2Rate := 7 }

def trySucceed : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.trySucceed
  , exp1Rate := 33, exp2Rate := 13 }

def participateWin : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.participateWin
  , exp1Rate := 24, exp2Rate := 0 }

def believeKnow : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.believeKnow
  , exp1Rate := 29, exp2Rate := 9 }

def goodPerfect : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.goodPerfect
  , exp1Rate := 45, exp2Rate := 18 }

def memorableUnforgettable : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.memorableUnforgettable
  , exp1Rate := 43, exp2Rate := 44 }

def specialUnique : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.specialUnique
  , exp1Rate := 16, exp2Rate := 2 }

def darkBlack : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.darkBlack
  , exp1Rate := 9, exp2Rate := 0 }

def warmHot : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.warmHot
  , exp1Rate := 45, exp2Rate := 31 }

def coolCold : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.coolCold
  , exp1Rate := 25, exp2Rate := 9 }

def goodExcellent : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.goodExcellent
  , exp1Rate := 39, exp2Rate := 13 }

def adequateGood : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.adequateGood
  , exp1Rate := 34, exp2Rate := 7 }

def palatableDelicious : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.palatableDelicious
  , exp1Rate := 35, exp2Rate := 18 }

def bigEnormous : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.bigEnormous
  , exp1Rate := 21, exp2Rate := 2 }

def smallTiny : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.smallTiny
  , exp1Rate := 17, exp2Rate := 7 }

def oldAncient : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.oldAncient
  , exp1Rate := 16, exp2Rate := 7 }

def contentHappy : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.contentHappy
  , exp1Rate := 12, exp2Rate := 4 }

def likeLove : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.likeLove
  , exp1Rate := 13, exp2Rate := 9 }

def dislikeLoathe : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.dislikeLoathe
  , exp1Rate := 14, exp2Rate := 13 }

def waryScared : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.waryScared
  , exp1Rate := 16, exp2Rate := 4 }

def unsettlingHorrific : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.unsettlingHorrific
  , exp1Rate := 28, exp2Rate := 4 }

def tiredExhausted : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.tiredExhausted
  , exp1Rate := 12, exp2Rate := 7 }

def hungryStarving : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.hungryStarving
  , exp1Rate := 14, exp2Rate := 4 }

def attractiveStunning : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.attractiveStunning
  , exp1Rate := 26, exp2Rate := 0 }

def prettyBeautiful : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.prettyBeautiful
  , exp1Rate := 21, exp2Rate := 7 }

def sillyRidiculous : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.sillyRidiculous
  , exp1Rate := 18, exp2Rate := 7 }

def snugTight : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.snugTight
  , exp1Rate := 13, exp2Rate := 7 }

def intelligentBrilliant : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.intelligentBrilliant
  , exp1Rate := 15, exp2Rate := 7 }

def funnyHilarious : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.funnyHilarious
  , exp1Rate := 15, exp2Rate := 4 }

def uglyHideous : EmbeddedSIDatum :=
  { vt2016 := VanTielEtAl2016.Scales.uglyHideous
  , exp1Rate := 17, exp2Rate := 7 }


-- ============================================================================
-- Scale Lists
-- ============================================================================

/-- All 42 scales tested in @cite{ronai-2024}. -/
def allScales : List EmbeddedSIDatum := [
  -- Bounded scales (20 = VT2016's 21 minus ⟨few, none⟩)
  someAll, possibleCertain, allowedObligatory, mayHaveTo, mayWill,
  sometimesAlways, cheapFree, difficultImpossible, hardUnsolvable,
  rareExtinct, scarceUnavailable, lowDepleted, startFinish,
  trySucceed, participateWin, believeKnow, goodPerfect,
  memorableUnforgettable, specialUnique, darkBlack,
  -- Non-bounded scales (22)
  warmHot, coolCold, goodExcellent, adequateGood, palatableDelicious,
  bigEnormous, smallTiny, oldAncient, contentHappy,
  likeLove, dislikeLoathe, waryScared, unsettlingHorrific,
  tiredExhausted, hungryStarving, attractiveStunning, prettyBeautiful,
  sillyRidiculous, snugTight, intelligentBrilliant, funnyHilarious,
  uglyHideous
]

#guard allScales.length == 42

/-- Bounded scales (by VT2016 annotation). -/
def boundedScales : List EmbeddedSIDatum := allScales.filter (·.bounded)

/-- Non-bounded scales. -/
def nonBoundedScales : List EmbeddedSIDatum := allScales.filter (!·.bounded)

#guard boundedScales.length == 20
#guard nonBoundedScales.length == 22


-- ============================================================================
-- Experiment Metadata
-- ============================================================================

/-- Experiment 1: @cite{gotzner-romoli-2018} sliding-scale paradigm.
119 recruited, 1 excluded (bilingual), N=118.
Within-subjects (Latin Square), 42 critical items × 4 conditions. -/
def exp1N : Nat := 118

/-- Experiment 2: @cite{van-tiel-geurts-2016} binary inference task (Yes/No).
N=45 (all data reported). Within-subjects, 42 critical items. -/
def exp2N : Nat := 45


-- ============================================================================
-- Experiment 1: Aggregate Results (computed from OSF raw data)
-- ============================================================================

/-- Mean sliding scale response by condition, computed from raw data.
Reference level is "strong"; contrasts reported in the paper:
true−strong: Estimate=55.6, SE=2.75, t=20.19, p<.001
weak−strong: Estimate=12.79, SE=1.93, t=6.62, p<.001
false−strong: Estimate=−26.12, SE=1.47, t=−17.81, p<.001 -/
structure Exp1Aggregate where
  trueControl : Nat
  weakInference : Nat
  strongInference : Nat
  falseControl : Nat
  deriving Repr

def exp1Aggregate : Exp1Aggregate :=
  { trueControl := 86     -- mean=85.5, round to 86
  , weakInference := 42   -- mean=42.4
  , strongInference := 30 -- mean=29.8
  , falseControl := 4 }   -- mean=3.5

/-- Response ordering: true > weak > strong > false.
This replicates @cite{gotzner-romoli-2018}'s finding across 42 scales. -/
theorem exp1_ordering :
    exp1Aggregate.trueControl > exp1Aggregate.weakInference ∧
    exp1Aggregate.weakInference > exp1Aggregate.strongInference ∧
    exp1Aggregate.strongInference > exp1Aggregate.falseControl := by
  native_decide

/-- Strong inference significantly above false control: embedded SIs exist.
The 26-point gap corresponds to Estimate=−26.12, t=−17.81 in the regression. -/
theorem exp1_strong_above_false :
    exp1Aggregate.strongInference > exp1Aggregate.falseControl + 20 := by
  native_decide


-- ============================================================================
-- Regression Results (ℚ, from paper text)
-- ============================================================================

/-- Mixed-effects regression coefficient. -/
structure RegressionCoeff where
  predictor : String
  /-- Estimate (unstandardized) -/
  estimate : ℚ
  /-- Standard error -/
  se : ℚ
  /-- Test statistic (t for LMER in Exp 1, z for GLMER in Exp 2) -/
  statistic : ℚ
  deriving Repr

-- Exp 1: Linear mixed effects, strong condition only.
-- Predicting Response (0–100) by predictor, with by-participant and
-- by-item random intercepts.

/-- Exp 1: Semantic distance → strong inference (p<.05). -/
def exp1_semanticDistance : RegressionCoeff :=
  { predictor := "semantic_distance"
  , estimate := 728 / 100   -- 7.28
  , se := 329 / 100         -- 3.29
  , statistic := 221 / 100  -- t = 2.21
  }

/-- Exp 1: Boundedness → strong inference (p<.001). -/
def exp1_boundedness : RegressionCoeff :=
  { predictor := "boundedness"
  , estimate := 1837 / 100   -- 18.37
  , se := 441 / 100          -- 4.41
  , statistic := 417 / 100   -- t = 4.17
  }

-- Exp 2: Logistic mixed effects (binary Yes/No).
-- Predicting Response (Yes vs No) by predictor, same random effects.

/-- Exp 2: Semantic distance → strong inference (p<.05). -/
def exp2_semanticDistance : RegressionCoeff :=
  { predictor := "semantic_distance"
  , estimate := 63 / 100    -- 0.63
  , se := 31 / 100          -- 0.31
  , statistic := 205 / 100  -- z = 2.05
  }

/-- Exp 2: Boundedness → strong inference (p<.001). -/
def exp2_boundedness : RegressionCoeff :=
  { predictor := "boundedness"
  , estimate := 154 / 100   -- 1.54
  , se := 39 / 100          -- 0.39
  , statistic := 391 / 100  -- z = 3.91
  }


-- ============================================================================
-- Correlation Results (ℚ)
-- ============================================================================

/-- Exp 1: Pearson r between VT2016 global SI rate and Exp 1 strong inference.
r=0.76, p<.001. -/
def exp1Correlation : ℚ := 76 / 100

/-- Exp 2: Pearson r between VT2016 global SI rate and Exp 2 strong inference.
r=0.80, p<.001. -/
def exp2Correlation : ℚ := 80 / 100


-- ============================================================================
-- Computed Theorems
-- ============================================================================

/-- Both predictors are significant in Exp 1 (t > 1.96). -/
theorem exp1_both_predictors_significant :
    exp1_semanticDistance.statistic > 196 / 100 ∧
    exp1_boundedness.statistic > 196 / 100 := by
  constructor <;> native_decide

/-- Both predictors are significant in Exp 2 (z > 1.96). -/
theorem exp2_both_predictors_significant :
    exp2_semanticDistance.statistic > 196 / 100 ∧
    exp2_boundedness.statistic > 196 / 100 := by
  constructor <;> native_decide

/-- Boundedness has a larger effect than semantic distance in both experiments.
This parallels @cite{van-tiel-geurts-2016}'s finding that boundedness
dominates the combined model. -/
theorem boundedness_dominates_distance :
    exp1_boundedness.estimate > exp1_semanticDistance.estimate ∧
    exp2_boundedness.estimate > exp2_semanticDistance.estimate := by
  constructor <;> native_decide

/-- Exp 2 correlation is at least as strong as Exp 1.
The binary task (less noisy) yields a tighter global–embedded relationship. -/
theorem exp2_correlation_at_least_exp1 :
    exp2Correlation ≥ exp1Correlation := by native_decide

/-- Both correlations are strong (r > 0.70). -/
theorem both_correlations_strong :
    exp1Correlation > 70 / 100 ∧ exp2Correlation > 70 / 100 := by
  constructor <;> native_decide

/-- Bounded scales yield more embedded SIs than non-bounded in both experiments.
Total rates across 20 bounded scales exceed total across 22 non-bounded,
despite having fewer items. -/
theorem bounded_higher_both_exps :
    (boundedScales.map (·.exp1Rate)).foldl (· + ·) 0 >
    (nonBoundedScales.map (·.exp1Rate)).foldl (· + ·) 0 ∧
    (boundedScales.map (·.exp2Rate)).foldl (· + ·) 0 >
    (nonBoundedScales.map (·.exp2Rate)).foldl (· + ·) 0 := by
  constructor <;> native_decide

/-- ⟨some, all⟩ embedded SI rate substantially above the overall mean (30),
consistent with it being a "workhorse" scale for SI research. -/
theorem someAll_embedded_above_mean :
    someAll.exp1Rate > exp1Aggregate.strongInference := by native_decide

/-- ⟨may, will⟩ is an outlier: very high global SI rate (VT2016 Exp 2 = 89%)
but extremely low embedded SI rate (Exp 1 = 7), suggesting embedding under
*every* disrupts SI for this modal scale specifically. -/
theorem mayWill_outlier :
    mayWill.globalSIRate > 80 ∧ mayWill.exp1Rate < 10 := by native_decide

/-- The global SI rate for each scale is derived from VT2016, not stored
independently. This structural test verifies the derivation: ⟨some, all⟩'s
global SI rate matches VT2016 Exp 2 by construction. -/
theorem globalSIRate_is_vt2016_exp2 :
    someAll.globalSIRate = VanTielEtAl2016.Scales.someAll.siRateExp2 := rfl

/-- Boundedness is derived from VT2016, not stored independently. -/
theorem bounded_is_vt2016 :
    darkBlack.bounded = VanTielEtAl2016.Scales.darkBlack.bounded := rfl

end Ronai2024
