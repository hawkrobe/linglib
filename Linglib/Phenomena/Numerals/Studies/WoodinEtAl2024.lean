import Linglib.Core.Roundness
import Mathlib.Data.Rat.Defs

/-!
# Woodin, Winter & Bhatt (2024): Numeral Frequency and Roundness

Corpus study showing number frequency is predicted by:
(a) log magnitude, and
(b) graded roundness via Sigurd/Jansen & Pollmann k-ness properties.

Key finding: each k-ness property has an independent positive effect on frequency,
with 10-ness being the strongest predictor and multipleOf5 the weakest.

## Register Effect

Informational texts (Wikipedia) show stronger roundness effects than
non-informational texts (fiction, conversation), suggesting roundness
interacts with communicative goals.

## References

- Woodin, Winter & Bhatt (2024). Why are some numbers more frequent than
  others? A corpus study of numeral roundness.
- Sigurd (1988). Round numbers.
- Jansen & Pollmann (2001). On round numbers: An analysis of numerical
  turn-taking points.
-/

namespace Phenomena.Numerals.Studies.WoodinEtAl2024

open Core.Roundness

-- ============================================================================
-- β coefficients from regression model (Table 3, Woodin et al. 2024)
-- ============================================================================

/--
Regression coefficient for each k-ness property on log frequency.

Higher β = stronger positive effect on numeral frequency in corpora.
All coefficients are positive: each property independently increases frequency.
-/
structure RoundnessCoefficient where
  property : String
  β : ℚ
  deriving Repr

/-- β coefficients ordered by magnitude (Table 3). -/
def β_tenness : RoundnessCoefficient :=
  { property := "10-ness", β := 446 / 100 }  -- 4.46

def β_2_5ness : RoundnessCoefficient :=
  { property := "2.5-ness", β := 384 / 100 }  -- 3.84

def β_5ness : RoundnessCoefficient :=
  { property := "5-ness", β := 261 / 100 }  -- 2.61

def β_2ness : RoundnessCoefficient :=
  { property := "2-ness", β := 156 / 100 }  -- 1.56

def β_mult10 : RoundnessCoefficient :=
  { property := "multipleOf10", β := 52 / 100 }  -- 0.52

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
  unfold β_tenness β_2_5ness β_5ness β_2ness β_mult10 β_mult5
  native_decide

-- ============================================================================
-- Frequency-weighted roundness score
-- ============================================================================

/--
Frequency-weighted roundness score using Woodin et al.'s β coefficients.

Unlike the unweighted `roundnessScore` (which counts properties equally),
this weights each property by its empirical frequency effect.
-/
def weightedRoundnessScore (n : Nat) : ℚ :=
  let rp := roundnessProperties n
  (if rp.multipleOf5 then β_mult5.β else 0) +
  (if rp.multipleOf10 then β_mult10.β else 0) +
  (if rp.twoness then β_2ness.β else 0) +
  (if rp.twoPointFiveness then β_2_5ness.β else 0) +
  (if rp.fiveness then β_5ness.β else 0) +
  (if rp.tenness then β_tenness.β else 0)

-- Weighted score verification
#guard weightedRoundnessScore 7 == 0
#guard weightedRoundnessScore 100 > weightedRoundnessScore 50
#guard weightedRoundnessScore 50 > weightedRoundnessScore 110

theorem weighted_100_gt_50 :
    weightedRoundnessScore 100 > weightedRoundnessScore 50 := by native_decide

theorem weighted_50_gt_110 :
    weightedRoundnessScore 50 > weightedRoundnessScore 110 := by native_decide

theorem weighted_7_eq_zero :
    weightedRoundnessScore 7 = 0 := by native_decide

-- ============================================================================
-- Register effect data
-- ============================================================================

/--
Register type from corpus analysis.

Informational registers (Wikipedia) show stronger roundness effects
than non-informational registers (fiction, conversation).
-/
inductive Register where
  | informational      -- Wikipedia, academic, news
  | nonInformational   -- fiction, conversation
  deriving Repr, DecidableEq, BEq

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

end Phenomena.Numerals.Studies.WoodinEtAl2024
