import Linglib.Core.Roundness
import Linglib.Core.SocialMeaning

/-!
# Beltrama & Schwarz (2024): Social Stereotypes and Imprecision — Data
@cite{beltrama-schwarz-2024}

Theory-neutral experimental data from two experiments showing that
speaker persona stereotypes affect imprecision resolution for round
numerals.

## Experiments

1. **Experiment 1 (Covered Screen Task)**: Participants choose which of
   two phone screens (COVERED vs VISIBLE) a speaker was looking at when
   making a round-numeral statement. Both Nerdy and Chill personae
   significantly affect choice rates.

2. **Experiment 2 (Truth-Value Judgment Task)**: Participants judge whether
   a speaker's round-numeral statement is RIGHT or WRONG given a visible
   phone screen. Only the Chill persona significantly affects judgments.

## Key empirical generalization

Speaker persona stereotypes modulate imprecision resolution
bi-directionally in inference tasks (Exp 1) but asymmetrically in
judgment tasks (Exp 2): Chill speakers increase tolerance for
imprecision in both tasks, but Nerdy speakers only increase
exactness demands in the inference task.

## Reference

Beltrama, A. & Schwarz, F. (2024). Social stereotypes affect imprecision
resolution across different tasks. *Semantics & Pragmatics* 17(10): 1–34.
-/

namespace Phenomena.Gradability.Imprecision.Studies.BeltramaSchwarz2024

-- ============================================================================
-- Conditions
-- ============================================================================

/-- Speaker persona condition (between-subjects).
    Participants read a short vignette describing the speaker (§3.1). -/
inductive PersonaCondition where
  | nerdy      -- "Ryan is studious, articulate, introverted, and uptight"
  | chill      -- "Ryan is laid-back, sociable, extroverted, and care-free"
  | noPersona  -- no persona description provided (baseline)
  deriving DecidableEq, BEq, Repr

/-- Screen fit condition (within-subjects, §3.1).
    Determines the relationship between the speaker's round-numeral
    statement and the amount shown on the VISIBLE phone screen. -/
inductive ScreenFit where
  | match_     -- visible screen shows exact stated amount ($200 when "$200")
  | mismatch   -- visible screen shows very different amount
  | imprecise  -- visible screen shows close-but-not-exact amount ($193 when "$200")
  deriving DecidableEq, BEq, Repr

/-- Experimental task type. -/
inductive TaskType where
  | coveredScreen        -- Exp 1: infer which phone the speaker saw
  | truthValueJudgment   -- Exp 2: judge the statement RIGHT vs WRONG
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Persona trait descriptions (§3.1)
-- ============================================================================

/-- The trait descriptors used for each persona condition.
    Each participant read: "Ryan is [descriptors]." -/
def personaDescriptors : PersonaCondition → List String
  | .nerdy     => ["studious", "articulate", "introverted", "uptight"]
  | .chill     => ["laid-back", "sociable", "extroverted", "care-free"]
  | .noPersona => []

-- ============================================================================
-- Regression coefficients
-- ============================================================================

/-- A coefficient from a mixed-effects logistic regression model.
    Models fitted via `glmer` in R (lme4; Bates et al. 2015). -/
structure RegressionCoefficient where
  /-- Predictor label -/
  predictor : String
  /-- Coefficient estimate (log-odds) -/
  beta : ℚ
  /-- Standard error -/
  se : ℚ
  /-- Significant at p < 0.05? -/
  significant : Bool
  deriving Repr

-- ============================================================================
-- Experiment 1: Covered Screen Task (§4)
-- ============================================================================

/-- Experiment 1 sample size after exclusions (§4.1).
    134 participants from 151 recruited. -/
def exp1_n : Nat := 134

/-- Experiment 1, Model 1 (main effects only).
    DV: COVERED (1) vs VISIBLE (0).
    Reference levels: NoPersona, ScreenFit[Imprecise].
    Table 1, Model 1 (§4.2). -/
def exp1_intercept : RegressionCoefficient :=
  { predictor := "Intercept", beta := 67/100, se := 18/100, significant := true }
def exp1_chill : RegressionCoefficient :=
  { predictor := "Chill", beta := -67/100, se := 13/100, significant := true }
def exp1_nerdy : RegressionCoefficient :=
  { predictor := "Nerdy", beta := 77/100, se := 14/100, significant := true }
def exp1_screenFitMatch : RegressionCoefficient :=
  { predictor := "ScreenFit[Match]", beta := -447/100, se := 18/100, significant := true }
def exp1_screenFitMismatch : RegressionCoefficient :=
  { predictor := "ScreenFit[Mismatch]", beta := 248/100, se := 20/100, significant := true }

def exp1_model1 : List RegressionCoefficient :=
  [exp1_intercept, exp1_chill, exp1_nerdy, exp1_screenFitMatch, exp1_screenFitMismatch]

/-- Experiment 1, Model 2 interaction terms (Table 1, Model 2).
    All Persona × ScreenFit interactions are non-significant (§4.2.2):
    persona effects are comparable across screen fit conditions. -/
def exp1_chillMatch : RegressionCoefficient :=
  { predictor := "Chill:Match", beta := -16/100, se := 37/100, significant := false }
def exp1_chillMismatch : RegressionCoefficient :=
  { predictor := "Chill:Mismatch", beta := 12/100, se := 40/100, significant := false }
def exp1_nerdyMatch : RegressionCoefficient :=
  { predictor := "Nerdy:Match", beta := 11/100, se := 35/100, significant := false }
def exp1_nerdyMismatch : RegressionCoefficient :=
  { predictor := "Nerdy:Mismatch", beta := -22/100, se := 38/100, significant := false }

def exp1_interactions : List RegressionCoefficient :=
  [exp1_chillMatch, exp1_chillMismatch, exp1_nerdyMatch, exp1_nerdyMismatch]

-- ============================================================================
-- Experiment 2: Truth-Value Judgment Task (§5)
-- ============================================================================

/-- Experiment 2 sample size after exclusions (§5.1).
    132 participants from 150 recruited. -/
def exp2_n : Nat := 132

/-- Experiment 2, Model 1 (main effects only).
    DV: RIGHT (1) vs WRONG (0).
    Reference levels: NoPersona, ScreenFit[Imprecise].
    Table 2, Model 1 (§5.2). -/
def exp2_intercept : RegressionCoefficient :=
  { predictor := "Intercept", beta := -78/100, se := 16/100, significant := true }
def exp2_chill : RegressionCoefficient :=
  { predictor := "Chill", beta := 104/100, se := 16/100, significant := true }
def exp2_nerdy : RegressionCoefficient :=
  { predictor := "Nerdy", beta := 2/100, se := 17/100, significant := false }
def exp2_screenFitMatch : RegressionCoefficient :=
  { predictor := "ScreenFit[Match]", beta := 455/100, se := 20/100, significant := true }
def exp2_screenFitMismatch : RegressionCoefficient :=
  { predictor := "ScreenFit[Mismatch]", beta := -263/100, se := 18/100, significant := true }

def exp2_model1 : List RegressionCoefficient :=
  [exp2_intercept, exp2_chill, exp2_nerdy, exp2_screenFitMatch, exp2_screenFitMismatch]

-- ============================================================================
-- Stimuli properties (§3.1)
-- ============================================================================

/-- All critical items use round dollar amounts.
    Example from §3.1: "The phone costs $200." -/
def exampleStatedAmount : Nat := 200

/-- The imprecise screen shows a close-but-not-exact amount.
    Example from §3.1: visible screen shows $193 when statement says $200. -/
def exampleImpreciseAmount : Nat := 193

/-- Stimulus numerals are round: high roundness grade. -/
theorem stimulus_is_round :
    Core.Roundness.roundnessGrade exampleStatedAmount = .high := by native_decide

/-- The imprecise value is non-round: zero roundness. -/
theorem imprecise_value_is_nonround :
    Core.Roundness.roundnessGrade exampleImpreciseAmount = .none := by native_decide

/-- Roundness scores differ maximally: 6 vs 0. -/
theorem roundness_gap :
    Core.Roundness.roundnessScore exampleStatedAmount = 6 ∧
    Core.Roundness.roundnessScore exampleImpreciseAmount = 0 := by
  constructor <;> native_decide

-- ============================================================================
-- Key empirical generalizations
-- ============================================================================

/-- Core finding: both persona conditions significantly affect Exp 1
    (inference task). -/
theorem exp1_both_personae_significant :
    exp1_chill.significant = true ∧ exp1_nerdy.significant = true := by
  exact ⟨rfl, rfl⟩

/-- Key asymmetry: in Exp 2 (judgment task), only Chill is significant. -/
theorem exp2_chill_only :
    exp2_chill.significant = true ∧ exp2_nerdy.significant = false := by
  exact ⟨rfl, rfl⟩

/-- Chill decreases COVERED rate (negative β): Chill persona leads
    listeners to favor the VISIBLE screen, treating the round numeral
    as imprecise (§4.2.2). -/
theorem chill_reduces_exactness_exp1 :
    exp1_chill.beta < 0 := by native_decide

/-- Nerdy increases COVERED rate (positive β): Nerdy persona leads
    listeners to favor the COVERED screen, treating the round numeral
    as exact (§4.2.2). -/
theorem nerdy_increases_exactness_exp1 :
    exp1_nerdy.beta > 0 := by native_decide

/-- Chill increases RIGHT rate (positive β on RIGHT DV), i.e.,
    increases tolerance for imprecision in truth-value judgments (§5.2.2). -/
theorem chill_increases_tolerance_exp2 :
    exp2_chill.beta > 0 := by native_decide

/-- Nerdy has no significant effect on truth-value judgments (§5.2.2). -/
theorem nerdy_null_in_exp2 :
    exp2_nerdy.significant = false := rfl

/-- No significant Persona × ScreenFit interactions in Exp 1 (§4.2.2):
    persona effects are comparable across all screen fit conditions. -/
theorem exp1_no_interactions :
    exp1_chillMatch.significant = false ∧
    exp1_chillMismatch.significant = false ∧
    exp1_nerdyMatch.significant = false ∧
    exp1_nerdyMismatch.significant = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The Chill effect is larger in Exp 2 (|β| = 1.04) than in
    Exp 1 (|β| = 0.67). -/
theorem chill_effect_larger_in_exp2 :
    exp2_chill.beta > -exp1_chill.beta := by native_decide

-- ============================================================================
-- Persona → social dimension mapping
-- ============================================================================

open Core.SocialMeaning in
/-- B&S frame the Nerdy/Chill contrast in terms of Fiske et al.'s (2007)
    Stereotype Content Model (§2): Nerdy ↔ Competence, Chill ↔ Warmth. -/
def personaDimension : PersonaCondition → Option SocialDimension
  | .nerdy     => some .competence
  | .chill     => some .warmth
  | .noPersona => none

end Phenomena.Gradability.Imprecision.Studies.BeltramaSchwarz2024
