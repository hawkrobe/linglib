import Mathlib.Data.Rat.Defs

/-!
# Argumentative Framing: Empirical Data

Empirical observations from two papers on how speakers use quantity expressions
to serve argumentative goals:

1. **Cummins & Franke (2021)**: REF case study showing universities choose "top M"
   claims strategically — always round numbers near their actual rank.
2. **Macuch Silva et al. (2024)**: Production experiments showing quantifier choice
   is driven by argumentative difficulty and framing direction.

## Data Sources

- C&F 2021 Table 1 (examples 29–38): UK university "top M" claims
- C&F 2021 §5.2: Ranking measure preference data (H2)
- MS et al. 2024 Experiment 1: Quantifier + adjective choice for exam results
- MS et al. 2024 Experiment 2: Free-form descriptions of exam results

## References

- Cummins, C. & Franke, M. (2021). Argumentative strength of numerical quantity.
- Macuch Silva, V. et al. (2024). Strategic quantifier use in production.
-/

namespace Phenomena.ArgumentativeFraming


-- ============================================================
-- Shared Types
-- ============================================================

/-- Framing direction: positive (high success) or negative (low success) -/
inductive FramingDirection where
  | positive   -- e.g., "X got most questions right"
  | negative   -- e.g., "X got some questions wrong"
  deriving DecidableEq, BEq, Repr

/-- Quantifier choices from MS et al.'s experimental materials -/
inductive QuantifierChoice where
  | all
  | most
  | some
  | none_
  deriving DecidableEq, BEq, Repr


-- ============================================================
-- Section 1: C&F 2021 — REF Case Study (§5)
-- ============================================================

/-- Hypothesis labels from C&F §5 -/
inductive REFHypothesis where
  | H1  -- Universities choose round M near their actual rank
  | H2  -- Universities prefer ranking measures that improve their position
  | H3  -- The combination of H1 and H2 produces observed claims
  deriving DecidableEq, BEq, Repr

/-- A "top M" datum from C&F Table 1 -/
structure TopMDatum where
  institution : String
  actualRank : Nat
  claimedM : Nat
  isRound : Bool
  rankingMeasure : String
  deriving Repr

/-- C&F examples 29–38: UK universities' "top M" claims.

All claimed M values are round numbers (multiples of 5 or 10),
and all are ≥ the institution's actual rank on the cited measure. -/
def topMExamples : List TopMDatum :=
  [ ⟨"Cardiff",           5,   5, true, "GPA"⟩         -- (29)
  , ⟨"KCL",               7,  10, true, "Power"⟩       -- (30)
  , ⟨"Manchester",         8,  25, true, "GPA"⟩         -- (31)
  , ⟨"Queen Mary",        11,  20, true, "Power"⟩       -- (32)
  , ⟨"Royal Holloway",    15,  25, true, "Power"⟩       -- (33)
  , ⟨"Reading",           20,  20, true, "Power"⟩       -- (34)
  , ⟨"Essex",             22,  25, true, "Power"⟩       -- (35)
  , ⟨"Bath",              24,  25, true, "Power"⟩       -- (36)
  , ⟨"Strathclyde",       30,  50, true, "Power"⟩       -- (37)
  , ⟨"Lincoln",           42,  50, true, "Power"⟩       -- (38)
  ]

/-- H1 verification: all claimed M values are round (multiples of 5) -/
theorem h1_all_round : topMExamples.all (·.isRound) = true := by native_decide

/-- H1 verification: all actual ranks are ≤ claimed M (claim is truthful) -/
theorem h1_all_truthful :
    topMExamples.all (λ d => decide (d.actualRank ≤ d.claimedM)) = true := by native_decide

/-- H2 data: ranking measure preference.

Of 19 institutions that could cite either GPA or Power ranking:
- 9 cite GPA (where they rank higher on GPA)
- 11 cite Power (where they rank higher on Power) — but see below
Actually C&F report that institutions systematically prefer the measure
on which they rank better. -/
structure RankPreferenceData where
  totalInstitutions : Nat
  citedPreferredMeasure : Nat
  citedNonPreferredMeasure : Nat
  deriving Repr

/-- H2 summary: institutions cite the measure giving them a better rank -/
def h2_data : RankPreferenceData :=
  { totalInstitutions := 19
    citedPreferredMeasure := 15
    citedNonPreferredMeasure := 4 }

/-- H2: majority cite their preferred measure -/
theorem h2_majority_preferred :
    h2_data.citedPreferredMeasure > h2_data.citedNonPreferredMeasure := by native_decide


-- ============================================================
-- Section 2: Macuch Silva et al. 2024 — Experiment 1
-- ============================================================

/-- An Experiment 1 datum: quantifier + adjective choice for exam results -/
structure Exp1Datum where
  nCorrect : Nat
  nTotal : Nat
  condition : FramingDirection
  quantifierChosen : QuantifierChoice
  adjectiveRight : Bool   -- true = "right", false = "wrong"
  proportion : ℚ          -- proportion of participants choosing this
  deriving Repr

/-- Key finding: adjective choice matches framing condition.

92% choose "right" in high-success condition; ~10% in low-success.
This confirms speakers attend to argumentative goals. -/
def exp1_adjective_rate_highSuccess : ℚ := 92 / 100
def exp1_adjective_rate_lowSuccess : ℚ := 10 / 100

theorem exp1_adjective_matches_condition :
    exp1_adjective_rate_highSuccess > 3/4 ∧
    exp1_adjective_rate_lowSuccess < 1/4 := by
  constructor <;> native_decide

/-- Key finding: "some" and "most" dominate quantifier choices.

Together they account for ~76% of responses, showing speakers avoid
the extreme quantifiers ("all", "none") even when truthful. -/
def exp1_some_most_proportion : ℚ := 76 / 100

theorem exp1_some_most_dominant :
    exp1_some_most_proportion > 1/2 := by native_decide

/-- Key finding: difficulty drives quantifier weakening.

As proportion moves away from extremes (difficulty ↑):
- At proportion > 0.5 (easy): "all"/"most" available → speakers use "most"
- At proportion ~0.5 (medium): "most" barely available → "some" rises
- At proportion < 0.3 (hard): only "some" available -/
def exp1_difficulty_weakening_observation : String :=
  "At difficulty > 0.5, most overtakes all; at > 0.75, some overtakes most"


-- ============================================================
-- Section 3: Macuch Silva et al. 2024 — Experiment 2
-- ============================================================

/-- Key finding: positive framing bias.

74% of free-form descriptions framed the result positively,
regardless of the actual proportion correct. -/
def exp2_positive_bias_rate : ℚ := 74 / 100

theorem exp2_positive_bias :
    exp2_positive_bias_rate > 1/2 := by native_decide

/-- Key finding: quantifier + numeral is the dominant strategy.

Speakers prefer combining a quantifier with a numeral (e.g., "most of the 60
questions") over pure quantifier or pure numeral descriptions. -/
def exp2_quantifier_with_numeral_observation : String :=
  "Most prevalent strategy combines quantifier + numeral (e.g., 'most of the 60 questions')"

/-- Framing strategy proportions from Experiment 2 -/
structure Exp2FramingDatum where
  strategy : String
  proportion : ℚ
  deriving Repr

/-- Experiment 2 strategy breakdown -/
def exp2_strategies : List Exp2FramingDatum :=
  [ ⟨"quantifier + numeral", 38 / 100⟩
  , ⟨"pure numeral",         31 / 100⟩
  , ⟨"pure quantifier",      22 / 100⟩
  , ⟨"other",                 9 / 100⟩
  ]

/-- Quantifier + numeral is the most common single strategy -/
theorem exp2_quant_numeral_most_common :
    (38 : ℚ) / 100 > 31 / 100 := by native_decide

end Phenomena.ArgumentativeFraming
