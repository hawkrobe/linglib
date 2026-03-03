import Linglib.Core.Scales.Roundness
import Linglib.Core.SocialMeaning
import Linglib.Theories.Semantics.Lexical.Numeral.Precision
import Linglib.Theories.Sociolinguistics.SCM
import Mathlib.Tactic.NormNum

/-!
# @cite{beltrama-schwarz-2024}: Empirical Data
@cite{beltrama-schwarz-2024}

Experimental data from @cite{beltrama-schwarz-2024}, showing that speaker
persona stereotypes affect imprecision resolution for round numerals.

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

-/

namespace Phenomena.Imprecision.Studies.BeltramaSchwarz2024

-- ============================================================================
-- §1. Conditions
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

/-- The trait descriptors used for each persona condition.
    Each participant read: "Ryan is [descriptors]." -/
def personaDescriptors : PersonaCondition → List String
  | .nerdy     => ["studious", "articulate", "introverted", "uptight"]
  | .chill     => ["laid-back", "sociable", "extroverted", "care-free"]
  | .noPersona => []

-- ============================================================================
-- §2. Regression coefficients
-- ============================================================================

/-- A coefficient from a mixed-effects logistic regression model.
    Models fitted via `glmer` in R (lme4; @cite{bates-etal-2015}). -/
structure RegressionCoefficient where
  predictor : String
  /-- Coefficient estimate (log-odds) -/
  beta : ℚ
  /-- Standard error -/
  se : ℚ
  /-- Significant at p < 0.05? -/
  significant : Bool
  deriving Repr

-- Experiment 1: Covered Screen Task (§4)

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

-- Experiment 2: Truth-Value Judgment Task (§5)

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
-- §3. Stimuli properties (§3.1)
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
-- §4. Empirical generalizations
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
    persona effects are comparable across all screen fit conditions.

    This absence (while main effects ARE significant) implies that persona
    modulates a global interpretive parameter — the precision threshold —
    rather than a local disambiguation strategy that operates only in
    ambiguous contexts. -/
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
-- § Precision Indexical Field and Theory Bridge
-- ============================================================================

open Core.SocialMeaning
open Sociolinguistics.SCM
open Semantics.Lexical.Numeral.Precision

/-- Precision variants for numeral use. -/
inductive PrecisionVariant where
  | exact
  | approximate
  deriving DecidableEq, BEq, Repr

/-- The indexical field for numeral precision. -/
def precisionField : IndexicalField PrecisionVariant SocialDimension :=
  { association := λ v d => match v, d with
    | .exact,       .competence      =>  1
    | .exact,       .warmth          => -1
    | .exact,       .antiSolidarity  =>  1
    | .approximate, .warmth          =>  1
    | .approximate, .competence      => -1
    | .approximate, .antiSolidarity  => -1
  , order := .third }

/-- The precision variant favored by a given persona condition. -/
def personaPrecision : PersonaCondition → Option PrecisionVariant
  | .nerdy     => some .exact
  | .chill     => some .approximate
  | .noPersona => none

/-- Persona conditions mapped to SCM social dimensions. -/
def personaDimension : PersonaCondition → Option SocialDimension
  | .nerdy     => some .competence
  | .chill     => some .warmth
  | .noPersona => none

/-- **Bidirectionality theorem**: production and comprehension mappings cohere. -/
theorem bidirectionality
    (p : PersonaCondition) (d : SocialDimension) (v : PrecisionVariant)
    (hd : personaDimension p = some d) (hv : personaPrecision p = some v) :
    precisionField.indexes v d := by
  cases p with
  | nerdy =>
    simp [personaDimension] at hd
    simp [personaPrecision] at hv
    subst hd; subst hv
    show (1 : ℚ) > 0; norm_num
  | chill =>
    simp [personaDimension] at hd
    simp [personaPrecision] at hv
    subst hd; subst hv
    show (1 : ℚ) > 0; norm_num
  | noPersona =>
    simp [personaDimension] at hd

theorem scm_coherence_nerdy :
    precisionField.indexes .exact .competence :=
  bidirectionality .nerdy .competence .exact rfl rfl

theorem scm_coherence_chill :
    precisionField.indexes .approximate .warmth :=
  bidirectionality .chill .warmth .approximate rfl rfl

/-- Exact and approximate use have opposite associations with every dimension. -/
theorem opposite_directions (d : SocialDimension) :
    precisionField.association .exact d =
    - precisionField.association .approximate d := by
  cases d <;> simp [precisionField]

-- ============================================================================
-- § Task Asymmetry from Prejudiciality
-- ============================================================================

inductive ResponseShift where
  | towardRejection
  | towardAcceptance
  deriving DecidableEq, BEq, Repr

def shiftDirection : PrecisionVariant → ResponseShift
  | .exact       => .towardRejection
  | .approximate => .towardAcceptance

def rejectionIsPrejudicial : TaskType → Prop
  | .coveredScreen      => False
  | .truthValueJudgment => True

instance (t : TaskType) : Decidable (rejectionIsPrejudicial t) :=
  match t with
  | .coveredScreen      => .isFalse id
  | .truthValueJudgment => .isTrue trivial

def shiftManifests (shift : ResponseShift) (task : TaskType) : Prop :=
  match shift with
  | .towardAcceptance => True
  | .towardRejection  => ¬ rejectionIsPrejudicial task

def personaEffectPredicted (persona : PersonaCondition) (task : TaskType) : Prop :=
  match personaPrecision persona with
  | none   => False
  | some v => shiftManifests (shiftDirection v) task

theorem acceptance_never_blocked (task : TaskType) :
    shiftManifests .towardAcceptance task := trivial

theorem rejection_manifests_in_cst :
    shiftManifests .towardRejection .coveredScreen :=
  id

theorem rejection_blocked_in_tvjt :
    ¬ shiftManifests .towardRejection .truthValueJudgment :=
  fun h => h trivial

/-- Both personae's effects manifest in CST. -/
theorem cst_both_manifest :
    personaEffectPredicted .nerdy .coveredScreen ∧
    personaEffectPredicted .chill .coveredScreen := by
  constructor
  · exact rejection_manifests_in_cst
  · exact acceptance_never_blocked .coveredScreen

/-- Only Chill's effect manifests in TVJT. -/
theorem tvjt_chill_only :
    personaEffectPredicted .chill .truthValueJudgment ∧
    ¬ personaEffectPredicted .nerdy .truthValueJudgment := by
  constructor
  · exact acceptance_never_blocked .truthValueJudgment
  · exact rejection_blocked_in_tvjt

theorem noPersona_no_effect (task : TaskType) :
    ¬ personaEffectPredicted .noPersona task :=
  id

/-- Combined task asymmetry matches empirical significance pattern. -/
theorem task_asymmetry_derived :
    (personaEffectPredicted .nerdy .coveredScreen ∧
     personaEffectPredicted .chill .coveredScreen) ∧
    (personaEffectPredicted .chill .truthValueJudgment ∧
     ¬ personaEffectPredicted .nerdy .truthValueJudgment) ∧
    (exp1_nerdy.significant = true ∧ exp1_chill.significant = true) ∧
    (exp2_chill.significant = true ∧ exp2_nerdy.significant = false) :=
  ⟨cst_both_manifest, tvjt_chill_only, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- ============================================================================
-- § Roundness Gating
-- ============================================================================

/-- Whether imprecise readings are available for a numeral. -/
def impreciseReadingAvailable (n : Nat) : Prop :=
  inferPrecisionMode n = .approximate

instance (n : Nat) : Decidable (impreciseReadingAvailable n) :=
  inferInstanceAs (Decidable (inferPrecisionMode n = .approximate))

/-- Roundness gates persona effects: $200 supports imprecision, $193 does not. -/
theorem roundness_gates_persona :
    impreciseReadingAvailable exampleStatedAmount ∧
    ¬ impreciseReadingAvailable exampleImpreciseAmount := by
  constructor <;> native_decide

/-- Multiples of 10 always have imprecise readings. -/
theorem div10_enables_imprecision (n : Nat) (h10 : n % 10 = 0) :
    impreciseReadingAvailable n := by
  unfold impreciseReadingAvailable inferPrecisionMode
  exact if_pos (Core.Roundness.score_ge_two_of_div10 n h10)

end Phenomena.Imprecision.Studies.BeltramaSchwarz2024
