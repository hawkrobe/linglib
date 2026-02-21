import Linglib.Core.Roundness
import Linglib.Core.SocialMeaning
import Linglib.Theories.Semantics.Lexical.Numeral.Precision
import Mathlib.Tactic.NormNum

/-!
# Beltrama & Schwarz (2024): Social Stereotypes and Imprecision
@cite{beltrama-schwarz-2024}

Experimental data and formalized theoretical arguments from Beltrama &
Schwarz (2024), showing that speaker persona stereotypes affect
imprecision resolution for round numerals.

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

## Formalized claims

1. **Bidirectionality** (`bidirectionality`): The paper's central
   contribution (§1, §7). Prior work (Beltrama, Solt & Burnett 2022)
   showed that precision in production indexes social traits; this paper
   shows that the same social traits, when provided as context, modulate
   how listeners resolve imprecision. We prove that these two directions
   are coherent: for each persona, the social dimension it occupies and
   the precision variant it favors are positively associated in the
   indexical field. This composes three independently defined mappings.

2. **Task asymmetry from prejudiciality** (`task_asymmetry_derived`,
   §7 pp.24–25): The pattern where both personae affect CST but only
   Chill affects TVJT follows from two independent structural facts:
   (a) the two personae shift interpretation in opposite directions
   (toward rejection vs. acceptance of imprecision), and (b) TVJT
   rejection ("wrong") is prejudicial while CST choice is not.
   Shifts toward the prejudicial response are blocked.

3. **Roundness gating** (`roundness_gates_persona`, `div10_enables_
   imprecision`): Persona effects on imprecision resolution presuppose
   that imprecise readings exist, which requires roundness. Non-round
   numerals lack imprecise readings, leaving nothing for persona to
   modulate.

4. **Opposite-direction effects** (`opposite_directions`): Nerdy and
   Chill produce opposite effects because exact and approximate use
   have algebraically opposite associations with every social dimension
   in the indexical field.

## References

* Beltrama, A. & Schwarz, F. (2024). Social stereotypes affect
  imprecision resolution across different tasks.
  *Semantics & Pragmatics* 17(10): 1–34.
* Beltrama, A., Solt, S. & Burnett, H. (2022). Context, precision,
  and social perception: A sociopragmatic study.
  *Language in Society* 52(5): 805–835.
* Eckert, P. (2008). Variation and the indexical field.
  *J. Sociolinguistics* 12(4): 453–476.
* Fiske, S. T., Cuddy, A. J. C. & Glick, P. (2007). Universal
  dimensions of social cognition: Warmth and competence.
  *Trends in Cognitive Sciences* 11(2): 77–83.
-/

namespace Phenomena.Gradability.Imprecision.Studies.BeltramaSchwarz2024

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
    Models fitted via `glmer` in R (lme4; Bates et al. 2015). -/
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
-- §5. Precision variants and the indexical field (Beltrama et al. 2022, B&S §2)
-- ============================================================================

open Core.SocialMeaning
open Semantics.Lexical.Numeral.Precision

/-- Precision variants for numeral use: the sociolinguistic variable whose
    social meaning B&S investigate. A speaker can use a numeral exactly or
    approximately (the latter only available for round numerals). -/
inductive PrecisionVariant where
  | exact       -- speaker uses numeral with exact intended reading
  | approximate -- speaker uses round numeral with approximate intended reading
  deriving DecidableEq, BEq, Repr

/-- The indexical field for numeral precision (Beltrama et al. 2022,
    cited in B&S §2).

    **Production-side social meaning**: using a numeral exactly vs.
    approximately indexes different social dimensions. Exact use indexes
    *toward* competence and *away from* warmth; approximate use indexes
    the reverse.

    The association values (±1) are an idealization — the paper provides
    no numeric field strengths. What matters for the theorems is the sign
    structure: exact→competence and approximate→warmth are positive, and
    the two variants are anti-symmetric across dimensions.

    The variable is third-order (Silverstein 2003): stereotyped and
    subject to overt metapragmatic commentary. -/
def precisionField : IndexicalField PrecisionVariant SocialDimension :=
  { association := λ v d => match v, d with
    | .exact,       .competence =>  1
    | .exact,       .warmth     => -1
    | .approximate, .warmth     =>  1
    | .approximate, .competence => -1
  , order := .third }

-- ============================================================================
-- §6. Persona mappings
-- ============================================================================

/-- The precision variant favored by a given persona condition.

    **Comprehension-side mapping** (B&S Hypothesis 1, §2.3): given a
    speaker's persona, which precision variant does the listener expect?
    A nerdy speaker is expected to use numerals exactly; a chill speaker
    is expected to use them approximately. -/
def personaPrecision : PersonaCondition → Option PrecisionVariant
  | .nerdy     => some .exact
  | .chill     => some .approximate
  | .noPersona => none

/-- B&S frame the Nerdy/Chill contrast in terms of Fiske et al.'s (2007)
    Stereotype Content Model (§2, §7 p.22): Nerdy traits cluster on
    Competence; Chill traits cluster on Warmth.

    This is a theoretical interpretation — B&S's own framing of their
    persona conditions within the SCM — not raw data. -/
def personaDimension : PersonaCondition → Option SocialDimension
  | .nerdy     => some .competence
  | .chill     => some .warmth
  | .noPersona => none

-- ============================================================================
-- §7. Bidirectionality
-- ============================================================================

/-- **Bidirectionality theorem**: the production-side and comprehension-side
    mappings are coherent.

    For each persona with a social dimension (d) and a favored precision
    variant (v): the indexical field associates v *positively* with d.
    That is, the variant that the persona favors in comprehension is the
    same variant that indexes toward the persona's social dimension in
    production.

    This composes three independently defined functions:
    - `personaDimension` : PersonaCondition → Option SocialDimension
    - `personaPrecision` : PersonaCondition → Option PrecisionVariant
    - `precisionField.association` : PrecisionVariant → SocialDimension → ℚ

    The coherence is not stipulated in any single definition — it follows
    from the substantive content of each mapping and must be verified by
    case analysis across personae. -/
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

/-- Instantiation: exact use indexes toward the competence dimension
    that the Nerdy persona occupies. -/
theorem scm_coherence_nerdy :
    precisionField.indexes .exact .competence :=
  bidirectionality .nerdy .competence .exact rfl rfl

/-- Instantiation: approximate use indexes toward the warmth dimension
    that the Chill persona occupies. -/
theorem scm_coherence_chill :
    precisionField.indexes .approximate .warmth :=
  bidirectionality .chill .warmth .approximate rfl rfl

-- ============================================================================
-- §8. Opposite-direction effects from indexical field structure
-- ============================================================================

/-- Exact and approximate use have algebraically opposite associations
    with every social dimension. This is the structural source of the
    opposite β-signs in Experiment 1: β_Nerdy > 0 and β_Chill < 0. -/
theorem opposite_directions (d : SocialDimension) :
    precisionField.association .exact d =
    - precisionField.association .approximate d := by
  cases d <;> simp [precisionField]

-- ============================================================================
-- §9. Task response structure and prejudiciality (§7, pp.24–25)
-- ============================================================================

/-- The direction in which a precision expectation shifts the listener's
    response to an imprecise statement.

    An expectation of exactness makes the listener more likely to *reject*
    the imprecise statement (CST: choose COVERED; TVJT: say WRONG).
    An expectation of approximation makes the listener more likely to
    *accept* it (CST: choose VISIBLE; TVJT: say RIGHT). -/
inductive ResponseShift where
  | towardRejection
  | towardAcceptance
  deriving DecidableEq, BEq, Repr

/-- Map a favored precision variant to its response shift direction. -/
def shiftDirection : PrecisionVariant → ResponseShift
  | .exact       => .towardRejection
  | .approximate => .towardAcceptance

/-- Whether a task's rejection response is *prejudicial*: it commits
    the comprehender to a negative assessment of the speaker's linguistic
    behavior.

    B&S (§7, p.25): "Saying a statement is wrong is prejudicial in the
    sense that it commits the comprehender to a negative assessment of
    the speaker's linguistic choices." In contrast, choosing COVERED in
    the CST "involves no such negative connotation." -/
def rejectionIsPrejudicial : TaskType → Prop
  | .coveredScreen      => False
  | .truthValueJudgment => True

instance (t : TaskType) : Decidable (rejectionIsPrejudicial t) :=
  match t with
  | .coveredScreen      => .isFalse id
  | .truthValueJudgment => .isTrue trivial

/-- A response shift *manifests* in a task when it is not blocked by
    prejudiciality. A shift toward rejection is blocked in tasks where
    rejection is prejudicial. A shift toward acceptance is never blocked. -/
def shiftManifests (shift : ResponseShift) (task : TaskType) : Prop :=
  match shift with
  | .towardAcceptance => True
  | .towardRejection  => ¬ rejectionIsPrejudicial task

/-- Whether a persona's effect on imprecision resolution is predicted to
    manifest in a given task. Composes:
    persona → precision variant → shift direction → manifestation. -/
def personaEffectPredicted (persona : PersonaCondition) (task : TaskType) : Prop :=
  match personaPrecision persona with
  | none   => False
  | some v => shiftManifests (shiftDirection v) task

-- ============================================================================
-- §10. Task asymmetry: derivation from prejudiciality
-- ============================================================================

/-- Shifts toward acceptance are never blocked, in any task. -/
theorem acceptance_never_blocked (task : TaskType) :
    shiftManifests .towardAcceptance task := trivial

/-- Shifts toward rejection manifest in CST (no prejudiciality). -/
theorem rejection_manifests_in_cst :
    shiftManifests .towardRejection .coveredScreen :=
  id

/-- Shifts toward rejection are blocked in TVJT (rejection is prejudicial). -/
theorem rejection_blocked_in_tvjt :
    ¬ shiftManifests .towardRejection .truthValueJudgment :=
  fun h => h trivial

/-- **Task asymmetry (CST)**: Both personae's effects manifest in the
    Covered Screen Task, because neither response direction is prejudicial.

    Matches Experiment 1: both β_Chill and β_Nerdy are significant
    (Table 1, Model 1). -/
theorem cst_both_manifest :
    personaEffectPredicted .nerdy .coveredScreen ∧
    personaEffectPredicted .chill .coveredScreen := by
  constructor
  · exact rejection_manifests_in_cst
  · exact acceptance_never_blocked .coveredScreen

/-- **Task asymmetry (TVJT)**: Only Chill's effect manifests in the
    Truth-Value Judgment Task.

    - Chill → approximate → towardAcceptance → manifests (always)
    - Nerdy → exact → towardRejection → blocked (WRONG is prejudicial)

    Matches Experiment 2: β_Chill is significant, β_Nerdy is not
    (Table 2, Model 1). -/
theorem tvjt_chill_only :
    personaEffectPredicted .chill .truthValueJudgment ∧
    ¬ personaEffectPredicted .nerdy .truthValueJudgment := by
  constructor
  · exact acceptance_never_blocked .truthValueJudgment
  · exact rejection_blocked_in_tvjt

/-- The no-persona condition produces no effect in either task. -/
theorem noPersona_no_effect (task : TaskType) :
    ¬ personaEffectPredicted .noPersona task :=
  id

/-- **Combined task asymmetry**: the full predicted pattern matches the
    empirical significance pattern across all four Persona × Task cells.

    | Persona | CST (Exp 1) | TVJT (Exp 2) |
    |---------|-------------|--------------|
    | Nerdy   | predicted ✓ | ¬predicted ✓ |
    | Chill   | predicted ✓ | predicted ✓  |

    The structural predictions follow from composing the persona→shift
    and task→prejudiciality mappings. The empirical match is verified
    against the regression significance values. -/
theorem task_asymmetry_derived :
    (personaEffectPredicted .nerdy .coveredScreen ∧
     personaEffectPredicted .chill .coveredScreen) ∧
    (personaEffectPredicted .chill .truthValueJudgment ∧
     ¬ personaEffectPredicted .nerdy .truthValueJudgment) ∧
    (exp1_nerdy.significant = true ∧ exp1_chill.significant = true) ∧
    (exp2_chill.significant = true ∧ exp2_nerdy.significant = false) :=
  ⟨cst_both_manifest, tvjt_chill_only, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- ============================================================================
-- §11. Roundness gating: persona effects require imprecise readings
-- ============================================================================

/-- Whether imprecise readings are available for a numeral.
    Requires approximate precision mode (roundnessScore ≥ 2). -/
def impreciseReadingAvailable (n : Nat) : Prop :=
  inferPrecisionMode n = .approximate

instance (n : Nat) : Decidable (impreciseReadingAvailable n) :=
  inferInstanceAs (Decidable (inferPrecisionMode n = .approximate))

/-- **Roundness gating**: the stimulus numeral $200 (round) supports
    persona-modulated imprecision, while the imprecise-screen value $193
    (non-round) does not.

    B&S use round numerals precisely because they have imprecise readings.
    If the stimulus used $193, there would be no imprecision to resolve
    and no persona effect to observe. -/
theorem roundness_gates_persona :
    impreciseReadingAvailable exampleStatedAmount ∧
    ¬ impreciseReadingAvailable exampleImpreciseAmount := by
  constructor <;> native_decide

/-- **General roundness gating**: multiples of 10 always have imprecise
    readings available, because multipleOf5 + multipleOf10 guarantee
    roundnessScore ≥ 2, meeting the threshold for approximate precision
    mode.

    Composes `Core.Roundness.score_ge_two_of_div10` with the Precision
    module's threshold. -/
theorem div10_enables_imprecision (n : Nat) (h10 : n % 10 = 0) :
    impreciseReadingAvailable n := by
  unfold impreciseReadingAvailable inferPrecisionMode
  exact if_pos (Core.Roundness.score_ge_two_of_div10 n h10)

end Phenomena.Gradability.Imprecision.Studies.BeltramaSchwarz2024
