import Linglib.Semantics.Quantification.Numerals.Roundness
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# [woodin-etal-2023]: Numeral Frequency and Roundness
[sigurd-1988] [woodin-etal-2023]

Corpus study showing number frequency is predicted by:
(a) log magnitude, and
(b) graded roundness via Sigurd/Jansen & Pollmann k-ness properties.

Key finding: each k-ness property has an independent positive effect on frequency,
with 10-ness being the strongest predictor and multipleOf5 the weakest.

## Register Effect

Informational texts (Wikipedia) show stronger roundness effects than
non-informational texts (fiction, conversation), suggesting roundness
interacts with communicative goals.

-/

namespace WoodinEtAl2024

open Semantics.Numerals.Roundness

/-! ### β coefficients from the negative binomial regression (§4.2, [woodin-etal-2023]) -/

/--
Regression coefficient for each k-ness property on log frequency.

Higher β = stronger positive effect on numeral frequency in corpora.
All coefficients are positive: each property independently increases frequency.
-/
structure RoundnessCoefficient where
  property : String
  β : ℚ
  deriving Repr

/-- β coefficients ordered by magnitude (§4.2). -/
def β_tenness : RoundnessCoefficient :=
  { property := "10-ness", β := 446 / 100 }  -- 4.46

def β_2_5ness : RoundnessCoefficient :=
  { property := "2.5-ness", β := 384 / 100 }  -- 3.84

def β_5ness : RoundnessCoefficient :=
  { property := "5-ness", β := 339 / 100 }  -- 3.39

def β_2ness : RoundnessCoefficient :=
  { property := "2-ness", β := 274 / 100 }  -- 2.74

def β_mult10 : RoundnessCoefficient :=
  { property := "multipleOf10", β := 245 / 100 }  -- 2.45

def β_mult5 : RoundnessCoefficient :=
  { property := "multipleOf5", β := 6 / 100 }  -- 0.06

/-- The 6 coefficients in descending order. -/
def roundnessHierarchy : List RoundnessCoefficient :=
  [β_tenness, β_2_5ness, β_5ness, β_2ness, β_mult10, β_mult5]

-- Hierarchy ordering verification
#guard β_tenness.β > β_2_5ness.β
#guard β_2_5ness.β > β_5ness.β
#guard β_5ness.β > β_2ness.β
#guard β_2ness.β > β_mult10.β
#guard β_mult10.β > β_mult5.β

theorem hierarchy_ordering :
    β_tenness.β > β_2_5ness.β ∧
    β_2_5ness.β > β_5ness.β ∧
    β_5ness.β > β_2ness.β ∧
    β_2ness.β > β_mult10.β ∧
    β_mult10.β > β_mult5.β := by
  norm_num [β_tenness, β_2_5ness, β_5ness, β_2ness, β_mult10, β_mult5]

/-! ### Frequency-weighted roundness score -/

/--
Frequency-weighted roundness score using Woodin et al.'s β coefficients.

Unlike the unweighted `roundnessScore` (which counts properties equally),
this weights each property by its empirical frequency effect.
-/
def weightedRoundnessScore (n : ℕ) : ℚ :=
  (if 5 ∣ n then β_mult5.β else 0) +
  (if 10 ∣ n then β_mult10.β else 0) +
  (if HasKness n 2 then β_2ness.β else 0) +
  (if Has2_5ness n then β_2_5ness.β else 0) +
  (if HasKness n 5 then β_5ness.β else 0) +
  (if HasKness n 10 then β_tenness.β else 0)

-- Weighted score verification
#guard weightedRoundnessScore 7 = 0
#guard weightedRoundnessScore 100 > weightedRoundnessScore 50
#guard weightedRoundnessScore 50 > weightedRoundnessScore 110

theorem weighted_100_gt_50 :
    weightedRoundnessScore 100 > weightedRoundnessScore 50 := by
  simp +decide [weightedRoundnessScore, β_tenness, β_2_5ness, β_5ness, β_2ness, β_mult10, β_mult5]; norm_num

theorem weighted_50_gt_110 :
    weightedRoundnessScore 50 > weightedRoundnessScore 110 := by
  simp +decide [weightedRoundnessScore, β_2_5ness, β_5ness, β_mult10, β_mult5]; norm_num

theorem weighted_7_eq_zero :
    weightedRoundnessScore 7 = 0 := by simp +decide [weightedRoundnessScore]

/-- `weightedRoundnessScore 50 > 0`: 50 has multipleOf5, multipleOf10,
    2.5-ness, 5-ness, and 10-ness (50 = 5 × 10¹), so its weighted score is
    the strictly positive sum of those β coefficients. -/
theorem weighted_50_pos : weightedRoundnessScore 50 > 0 := by
  simp +decide [weightedRoundnessScore, β_2_5ness, β_5ness, β_mult10, β_mult5]; norm_num

theorem weighted_50_gt_7 :
    weightedRoundnessScore 50 > weightedRoundnessScore 7 := by
  rw [weighted_7_eq_zero]; exact weighted_50_pos

/-- **RSA utterance prior from corpus frequency.** Rounder numerals have
    higher prior weight, so `weightedRoundnessScore` doubles as an
    empirically-grounded RSA utterance prior: rounder numerals are more
    likely to be chosen, all else equal. The strict-monotonicity chain
    `100 > 50 > 7` realises this on representative cases. -/
theorem roundness_prior_monotone :
    weightedRoundnessScore 100 > weightedRoundnessScore 50 ∧
    weightedRoundnessScore 50 > weightedRoundnessScore 7 :=
  ⟨weighted_100_gt_50, weighted_50_gt_7⟩

/-! ### Register effect data -/

/--
Register type from corpus analysis.

Informational registers (Wikipedia) show stronger roundness effects
than non-informational registers (fiction, conversation).
-/
inductive Register where
  | informational      -- Wikipedia, academic, news
  | nonInformational   -- fiction, conversation
  deriving Repr, DecidableEq

/-- Register effect datum: roundness β is larger in informational texts. -/
structure RegisterEffectDatum where
  register : Register
  roundnessEffectMagnitude : String  -- qualitative comparison
  notes : String
  deriving Repr

def informationalEffect : RegisterEffectDatum :=
  { register := .informational
  , roundnessEffectMagnitude := "stronger"
  , notes := "Wikipedia shows strongest roundness effects; consistent with communicative precision demands"
  }

def nonInformationalEffect : RegisterEffectDatum :=
  { register := .nonInformational
  , roundnessEffectMagnitude := "weaker"
  , notes := "Fiction/conversation show weaker roundness effects; approximate use less marked"
  }

end WoodinEtAl2024
