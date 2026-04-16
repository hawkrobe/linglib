import Linglib.Core.Scales.Roundness
import Linglib.Core.SocialMeaning
import Linglib.Theories.Semantics.Lexical.Numeral.Precision
import Linglib.Theories.Sociolinguistics.SCM
import Linglib.Theories.Sociolinguistics.EckertMontague
import Linglib.Phenomena.Imprecision.Studies.BeltramaSoltBurnett2022
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

namespace BeltramaSchwarz2024

open Core.SocialMeaning
open Sociolinguistics.SCM
open Semantics.Lexical.Numeral.Precision
open Sociolinguistics.EckertMontague

-- ============================================================================
-- Conditions
-- ============================================================================

/-- Speaker persona condition (between-subjects).
    Participants read a short vignette describing the speaker (§4.1). -/
inductive PersonaCondition where
  | nerdy      -- "studious, articulate, introverted, and uptight" (§4.1)
  | chill      -- "laid-back, sociable, extroverted, and care-free" (§4.1)
  | noPersona  -- no persona description provided (baseline)
  deriving DecidableEq, Repr

/-- Screen fit condition (within-subjects, §4.1).
    Determines the relationship between the speaker's round-numeral
    statement and the amount shown on the VISIBLE phone screen.
    In regression models, Match and Mismatch are collapsed into a binary
    "Control" factor, with Imprecise as the critical level (§4.5, §5.3). -/
inductive ScreenFit where
  | match_     -- visible screen shows exact stated amount ($200 when "$200")
  | mismatch   -- visible screen shows very different amount
  | imprecise  -- visible screen shows close-but-not-exact amount ($207 when "$200")
  deriving DecidableEq, Repr

/-- Experimental task type. -/
inductive TaskType where
  | coveredScreen        -- Exp 1: infer which phone the speaker saw
  | truthValueJudgment   -- Exp 2: judge the statement RIGHT vs WRONG
  deriving DecidableEq, Repr

/-- The trait descriptors used for each persona condition (§4.1).
    Context sentences described the dialogue characters using these traits,
    e.g. "Arthur and Rachel, who have been described as Nerdy people,
    are looking for a plane ticket" (Figure 2). -/
def personaDescriptors : PersonaCondition → List String
  | .nerdy     => ["studious", "articulate", "introverted", "uptight"]
  | .chill     => ["laid-back", "sociable", "extroverted", "care-free"]
  | .noPersona => []

-- ============================================================================
-- Regression coefficients
-- ============================================================================

/-- A coefficient from a mixed-effects logistic regression model.
    Models fitted via `lmer_alt` from the afex package in R, which wraps
    lme4 (@cite{bates-etal-2015}; see footnote 6 of paper). -/
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

/-- Experiment 1 participants (§4.4).
    282 self-declared native English speakers recruited on Prolific. -/
def exp1_n : Nat := 282

/-- Experiment 1 regression model (§4.5).
    DV: COVERED (1) vs VISIBLE (0).
    Persona: treatment-coded, NoPersona as reference.
    ScreenFit: binary (Control = Match+Mismatch collapsed vs Imprecise),
    sum-coded. Maximal converging mixed-effects logistic regression. -/
def exp1_chill : RegressionCoefficient :=
  { predictor := "Chill", beta := -67/100, se := 13/100, significant := true }
def exp1_nerdy : RegressionCoefficient :=
  { predictor := "Nerdy", beta := 77/100, se := 14/100, significant := true }
def exp1_screenFit : RegressionCoefficient :=
  { predictor := "ScreenFit", beta := 0, se := 10/100, significant := false }

/-- Experiment 1 Persona × ScreenFit interactions (§4.5).
    Both are significant: persona effects are concentrated in the
    Imprecise condition. In Control conditions, no significant persona
    contrasts were found. -/
def exp1_chillScreenFit : RegressionCoefficient :=
  { predictor := "Chill:ScreenFit", beta := 66/100, se := 13/100, significant := true }
def exp1_nerdyScreenFit : RegressionCoefficient :=
  { predictor := "Nerdy:ScreenFit", beta := -78/100, se := 13/100, significant := true }

def exp1_model : List RegressionCoefficient :=
  [exp1_chill, exp1_nerdy, exp1_screenFit,
   exp1_chillScreenFit, exp1_nerdyScreenFit]

-- Experiment 2: Truth-Value Judgment Task (§5)

/-- Experiment 2 participants (§5.2).
    244 recruited on Prolific. -/
def exp2_n : Nat := 244

/-- Experiment 2 regression model (§5.3).
    DV: acceptance rate. The paper describes fitting on "WRONG choices" but
    the positive Chill coefficient (β = 1.04) with the finding that Chill
    speakers had *lower* WRONG rates (§5.3, Figure 6) indicates the
    effective coding is acceptance (RIGHT = 1, WRONG = 0).
    Persona: treatment-coded, NoPersona as reference.
    ScreenFit: binary (Control vs Imprecise), sum-coded. -/
def exp2_chill : RegressionCoefficient :=
  { predictor := "Chill", beta := 104/100, se := 16/100, significant := true }
def exp2_nerdy : RegressionCoefficient :=
  { predictor := "Nerdy", beta := 2/100, se := 15/100, significant := false }

/-- Experiment 2 Persona × ScreenFit interactions (§5.3).
    Only Chill × ScreenFit is significant: the Chill tolerance effect
    is concentrated in the Imprecise condition. -/
def exp2_chillScreenFit : RegressionCoefficient :=
  { predictor := "Chill:ScreenFit", beta := 100/100, se := 16/100, significant := true }
def exp2_nerdyScreenFit : RegressionCoefficient :=
  { predictor := "Nerdy:ScreenFit", beta := 3/100, se := 18/100, significant := false }

def exp2_model : List RegressionCoefficient :=
  [exp2_chill, exp2_nerdy, exp2_chillScreenFit, exp2_nerdyScreenFit]

-- Combined Analysis (§6)

/-- The critical Nerdy × Task interaction (§6): the Covered Screen Task
    features a higher rejection rate for Nerdy than No.Persona, but the
    Truth Value Judgment task does not. This is the formal statistical
    confirmation of the task asymmetry captured by `task_asymmetry_derived`. -/
def combined_nerdyTask : RegressionCoefficient :=
  { predictor := "Nerdy:Task", beta := 62/100, se := 31/100, significant := true }

-- ============================================================================
-- Stimuli properties (§4.1–4.2)
-- ============================================================================

/-- All critical items use round dollar amounts.
    Example from §2: "The ticket costs $200." -/
def exampleStatedAmount : Nat := 200

/-- The imprecise screen shows a close-but-not-exact amount.
    Example from Figure 1: visible screen shows ~$207 when statement says $200. -/
def exampleImpreciseAmount : Nat := 207

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
-- Empirical generalizations
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
    as imprecise (§4.5). -/
theorem chill_reduces_exactness_exp1 :
    exp1_chill.beta < 0 := by native_decide

/-- Nerdy increases COVERED rate (positive β): Nerdy persona leads
    listeners to favor the COVERED screen, treating the round numeral
    as exact (§4.5). -/
theorem nerdy_increases_exactness_exp1 :
    exp1_nerdy.beta > 0 := by native_decide

/-- Chill increases RIGHT rate (positive β on RIGHT DV), i.e.,
    increases tolerance for imprecision in truth-value judgments (§5.3). -/
theorem chill_increases_tolerance_exp2 :
    exp2_chill.beta > 0 := by native_decide

/-- Nerdy has no significant effect on truth-value judgments (§5.3). -/
theorem nerdy_null_in_exp2 :
    exp2_nerdy.significant = false := rfl

/-- Significant Persona × ScreenFit interactions in Exp 1 (§4.5):
    persona effects are concentrated in the Imprecise condition. In Control
    conditions, no significant persona contrasts were found. -/
theorem exp1_interactions_significant :
    exp1_chillScreenFit.significant = true ∧
    exp1_nerdyScreenFit.significant = true := by
  exact ⟨rfl, rfl⟩

/-- Exp 2 interaction asymmetry (§5.3): only Chill × ScreenFit is
    significant. Nerdy speakers show no interaction, consistent with
    the null main effect. -/
theorem exp2_chill_interaction_only :
    exp2_chillScreenFit.significant = true ∧
    exp2_nerdyScreenFit.significant = false := by
  exact ⟨rfl, rfl⟩

/-- No main effect of ScreenFit in Exp 1 (§4.5): COVERED rates do not
    differ across Imprecise and Control conditions overall. The persona
    effect is entirely driven by the interaction. -/
theorem exp1_no_screenFit_main_effect :
    exp1_screenFit.significant = false := rfl

/-- The Chill main effect is larger in Exp 2 (|β| = 1.04) than in
    Exp 1 (|β| = 0.67). -/
theorem chill_effect_larger_in_exp2 :
    exp2_chill.beta > -exp1_chill.beta := by native_decide

/-- The combined analysis confirms the Nerdy × Task interaction is
    significant, validating the prejudiciality-based explanation. -/
theorem combined_nerdy_task_significant :
    combined_nerdyTask.significant = true := rfl

/-- The combined analysis interaction sign is positive (§6): Nerdy
    speakers have higher rejection rates in CST than TVJ relative to
    baseline, consistent with rejection being blocked in TVJ. -/
theorem combined_nerdy_task_positive :
    combined_nerdyTask.beta > 0 := by native_decide

-- ============================================================================
-- Precision indexical field
-- ============================================================================

/-- The indexical field for numeral precision, parameterized by
    `PrecisionMode` from `Semantics.Lexical.Numeral.Precision` rather than
    a study-local type — the sociolinguistic variable whose social meaning
    is under study IS the semantic precision mode. -/
def precisionField : IndexicalField PrecisionMode SocialDimension :=
  { association := λ v d => match v, d with
    | .exact,       .competence      =>  1
    | .exact,       .warmth          => -1
    | .exact,       .antiSolidarity  =>  1
    | .approximate, .warmth          =>  1
    | .approximate, .competence      => -1
    | .approximate, .antiSolidarity  => -1
  , order := .third }

/-- The precision mode favored by a given persona condition. -/
def personaPrecision : PersonaCondition → Option PrecisionMode
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
    (p : PersonaCondition) (d : SocialDimension) (v : PrecisionMode)
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

/-- Exact and approximate modes have opposite associations with every dimension. -/
theorem opposite_directions (d : SocialDimension) :
    precisionField.association .exact d =
    - precisionField.association .approximate d := by
  cases d <;> simp [precisionField]

-- ============================================================================
-- Task asymmetry from prejudiciality
-- ============================================================================

inductive ResponseShift where
  | towardRejection
  | towardAcceptance
  deriving DecidableEq, Repr

def shiftDirection : PrecisionMode → ResponseShift
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

/-- Combined task asymmetry matches empirical significance pattern:
    theoretical prediction from prejudiciality aligns with both the main
    effects and the interaction structure across experiments. -/
theorem task_asymmetry_derived :
    -- Theoretical prediction
    (personaEffectPredicted .nerdy .coveredScreen ∧
     personaEffectPredicted .chill .coveredScreen) ∧
    (personaEffectPredicted .chill .truthValueJudgment ∧
     ¬ personaEffectPredicted .nerdy .truthValueJudgment) ∧
    -- Empirical main effects
    (exp1_nerdy.significant = true ∧ exp1_chill.significant = true) ∧
    (exp2_chill.significant = true ∧ exp2_nerdy.significant = false) ∧
    -- Interactions confirm localization to Imprecise condition
    (exp1_chillScreenFit.significant = true ∧
     exp1_nerdyScreenFit.significant = true) ∧
    (exp2_chillScreenFit.significant = true ∧
     exp2_nerdyScreenFit.significant = false) :=
  ⟨cst_both_manifest, tvjt_chill_only, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
   ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- ============================================================================
-- Roundness gating
-- ============================================================================

/-- Whether imprecise readings are available for a numeral. -/
def impreciseReadingAvailable (n : Nat) : Prop :=
  inferPrecisionMode n = .approximate

instance (n : Nat) : Decidable (impreciseReadingAvailable n) :=
  inferInstanceAs (Decidable (inferPrecisionMode n = .approximate))

/-- Roundness gates persona effects: $200 supports imprecision, $207 does not. -/
theorem roundness_gates_persona :
    impreciseReadingAvailable exampleStatedAmount ∧
    ¬ impreciseReadingAvailable exampleImpreciseAmount := by
  constructor <;> native_decide

/-- Multiples of 10 always have imprecise readings. -/
theorem div10_enables_imprecision (n : Nat) (h10 : n % 10 = 0) :
    impreciseReadingAvailable n := by
  unfold impreciseReadingAvailable inferPrecisionMode
  exact if_pos (Core.Roundness.score_ge_two_of_div10 n h10)

-- ============================================================================
-- Integration
-- ============================================================================

-- Eckert–Montague bridge

/-! The precision field can be lifted to a grounded field over the SCM
property space via `fromIndexicalField`, connecting it to
@cite{burnett-2019}'s persona-theoretic infrastructure. -/

/-- The precision field converted to a grounded field over the SCM
    property space. -/
def precisionGroundedField : GroundedField PrecisionMode scmSpace :=
  fromIndexicalField precisionField

/-- Exact indexes {competent, cold, antiSolidary}. -/
theorem exact_scmProperties :
    precisionGroundedField.indexedProperties .exact =
      {.competent, .cold, .antiSolidary} := by
  native_decide

/-- Approximate indexes {incompetent, warm, solidary}. -/
theorem approx_scmProperties :
    precisionGroundedField.indexedProperties .approximate =
      {.incompetent, .warm, .solidary} := by
  native_decide

-- BSB2022 bridge

/-! @cite{beltrama-solt-burnett-2023}'s three-way variant contrast
(precise/underspecified/approximate) refines B&S2024's binary distinction.
The "underspecified" variant — a bare round numeral like "fifty" — is
exactly the kind of stimulus B&S2024 studies: its precision is
contextually determined. -/

/-- BSB2022's round stimulus (50) has an imprecise reading available,
    just like B&S2024's stimulus (200). Both are round numbers whose
    precision resolution is the object of study. -/
theorem bsb_stim_also_round :
    impreciseReadingAvailable
      BeltramaSoltBurnett2022.stimRound := by
  native_decide

-- Speaker-conditioned precision

/-! The core finding of @cite{beltrama-schwarz-2024} — that numeral
precision is jointly determined by roundness AND speaker identity — is
captured by `speakerModulatedHalo` in the theory layer
(`Semantics.Lexical.Numeral.Precision`). Nerdy speakers get narrower
halos (multiplier < 1), Chill speakers get wider ones (multiplier > 1). -/

/-- A larger multiplier produces a wider halo: the monotonicity that
    connects the competence/warmth ordering to tolerance width. -/
theorem wider_halo_of_larger_multiplier (m₁ m₂ : ℚ) (n : Nat)
    (hm : m₁ < m₂) (hn : 0 < haloWidth n) :
    speakerModulatedHalo m₁ n < speakerModulatedHalo m₂ n := by
  unfold speakerModulatedHalo
  exact mul_lt_mul_of_pos_right hm hn

/-- Round numbers have positive halo width, so speaker modulation
    has a genuine effect. -/
theorem round_has_positive_halo :
    0 < haloWidth exampleStatedAmount := by native_decide

end BeltramaSchwarz2024
