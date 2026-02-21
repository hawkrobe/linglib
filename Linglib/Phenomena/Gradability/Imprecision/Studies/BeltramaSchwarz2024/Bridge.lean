import Linglib.Phenomena.Gradability.Imprecision.Studies.BeltramaSchwarz2024.Data
import Linglib.Core.SocialMeaning
import Linglib.Theories.Semantics.Lexical.Numeral.Precision
import Linglib.Theories.Sociolinguistics.SCM
import Mathlib.Tactic.NormNum

/-!
# Beltrama & Schwarz (2024): Theory Bridge
@cite{beltrama-schwarz-2024}

Connects B&S's empirical data to their theoretical apparatus: the
precision indexical field (from Beltrama, Solt & Burnett 2022), persona
mappings onto the Stereotype Content Model (Fiske et al. 2007),
bidirectionality between production and comprehension, and the
prejudiciality-based account of task asymmetry.

**Data source**: `BeltramaSchwarz2024.Data`
**Theories used**: `Core.SocialMeaning` (IndexicalField),
  `Theories.Sociolinguistics.SCM` (SocialDimension),
  `Theories.Semantics.Lexical.Numeral.Precision` (inferPrecisionMode)

## Formalized claims

1. **Bidirectionality** (`bidirectionality`): production-side and
   comprehension-side mappings are coherent.

2. **Task asymmetry from prejudiciality** (`task_asymmetry_derived`):
   the pattern where both personae affect CST but only Chill affects
   TVJT follows from prejudiciality of rejection in TVJT.

3. **Roundness gating** (`roundness_gates_persona`): persona effects
   presuppose imprecise readings, which require roundness.

4. **Opposite-direction effects** (`opposite_directions`): exact and
   approximate use have algebraically opposite associations with every
   social dimension.

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

open Core.SocialMeaning
open Sociolinguistics.SCM
open Semantics.Lexical.Numeral.Precision

-- ============================================================================
-- §5. Precision variants and the indexical field (Beltrama et al. 2022, B&S §2)
-- ============================================================================

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
    | .exact,       .competence      =>  1
    | .exact,       .warmth          => -1
    | .exact,       .antiSolidarity  =>  1
    | .approximate, .warmth          =>  1
    | .approximate, .competence      => -1
    | .approximate, .antiSolidarity  => -1
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
