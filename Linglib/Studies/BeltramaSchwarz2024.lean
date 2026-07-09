import Linglib.Semantics.Quantification.Numerals.Roundness
import Linglib.Semantics.Quantification.Numerals.Precision
import Linglib.Pragmatics.SocialMeaning.IndexicalField
import Linglib.Pragmatics.SocialMeaning.SCM
import Linglib.Pragmatics.SocialMeaning.EckertMontague
import Linglib.Studies.BeltramaSoltBurnett2022
import Linglib.Data.Examples.BeltramaSchwarz2024
import Mathlib.Data.Sign.Defs
import Mathlib.Tactic.NormNum

/-!
# [beltrama-schwarz-2024]: Social stereotypes affect imprecision resolution

[beltrama-schwarz-2024] ask whether a speaker's social persona shifts how
comprehenders resolve numeral imprecision, and find that it does — but
*asymmetrically across tasks*. Two stereotypes anchor the high vs. low ends of
the precision scale ([beltrama-2018], [beltrama-solt-burnett-2023]): a **Nerdy**
persona (studious, articulate, introverted, uptight) indexes high Competence and
precise speech; a **Chill** persona (laid-back, sociable, extroverted, care-free)
indexes high Warmth and tolerant speech.

The puzzle this file formalizes is the *task asymmetry*. In an inference task
(Experiment 1, a Covered-Screen paradigm) **both** personae move interpretation:
Nerdy speakers' round numerals are read more strictly, Chill speakers' more
loosely. In a judgment task (Experiment 2, a Truth-Value Judgment), only the
**Chill** effect survives — the Nerdy strictness vanishes. [beltrama-schwarz-2024]
(§7) attribute this to the *prejudiciality of rejection*: in a TVJ, calling a
statement "wrong" commits the comprehender to blaming the speaker (an instance of
testimonial (in)justice, [fricker-2007]), and comprehenders are reluctant to
blame a speaker they read as conscientious. We make that the structural pivot:
acceptance shifts always manifest; rejection shifts are suppressed exactly in
tasks where rejection is prejudicial — which derives the asymmetry rather than
stipulating it.

## Main definitions
* `precisionField` — the [eckert-2008] indexical field linking `PrecisionMode`
  to [fiske-cuddy-glick-2007] social dimensions; `personaPrecision` /
  `personaDimension` read off the two personae.
* `personaShift` — the precision-driven shift on the "reject the imprecise
  reading" scale, derived from `personaPrecision` (a `SignType`).
* `RejectionPrejudicial` / `predictedShift` — the prejudiciality mechanism: a
  persona's shift, suppressed when it is a rejection-shift in a prejudicial task.

## Main results
* `bidirectionality`, `opposite_directions` — the persona ↔ precision mapping is
  coherent and the two modes are exact opposites on every dimension.
* `predictedShift_coveredScreen`, `predictedShift_truthValueJudgment`,
  `nerdy_effect_is_task_dependent`, `acceptance_shift_never_blocked`,
  `shift_blocked_iff` — the task asymmetry, derived from prejudiciality.
* `roundness_gates_persona` — persona effects need a round numeral to act on.
* the `#guard` over `Examples.all` checks each predicted shift against the
  text-reported observed direction in every persona × task cell.

## Empirical findings (prose, per [beltrama-schwarz-2024])
Effect sizes are documented here, not encoded as theorems (regression
coefficients are not Lean content). Experiment 1 (Covered-Screen, n = 282, §4.5):
in the critical Imprecise cell, COVERED (= precise/rejection) rates were higher
for Nerdy than for the no-persona baseline (z = 6.62, p < .0001) and lower for
Chill (z = 7.61, p < .0001); no persona contrast in the controls. Experiment 2
(Truth-Value Judgment, n = 244, §5.3): WRONG (= rejection) rates were lower for
Chill (z = 8.43, p < .0001) but did not differ from baseline for Nerdy (z = 0.15,
p = .87). The pooled analysis (§6) found a Nerdy × Task interaction (β = 0.62,
z = 1.99, p = .04): higher rejection for Nerdy than baseline in the Covered-Screen
task (z = 4.40, p < .0001) but no difference in the TVJ (z = 1.51, p = .28).

## Implementation notes
The illustrated stimulus (the "$200" ticket dialogue against a $207 screen) and
the text-reported observed directions live in `Data.Examples.BeltramaSchwarz2024`;
the structural predictions are checked against them by `#guard`. Persona ↔
precision indexing reuses `Pragmatics.SocialMeaning` (the [eckert-2008] field and
[burnett-2019]'s Eckert–Montague lift); `speakerModulatedHalo` scales the
substrate `haloWidth` by a speaker multiplier — the paper's claim that the
halo is a property of the number–speaker pair, not the number alone.
-/

namespace BeltramaSchwarz2024

open SocialMeaning.IndexicalField
open SocialMeaning.SCM
open SocialMeaning.EckertMontague
open Semantics.Numerals.Precision
open Data.Examples (LinguisticExample)

/-! ### Conditions -/

/-- Speaker persona condition (between-subjects, §4.1). The two stereotypes
    anchor the high/low ends of the precision scale; `noPersona` is the
    baseline with no social description. -/
inductive PersonaCondition where
  | nerdy
  | chill
  | noPersona
  deriving DecidableEq, Repr

/-- Experimental task (§4 vs. §5): inferring the speaker's referent from a round
    numeral (Covered-Screen) vs. judging an utterance true/false against a known
    value (Truth-Value Judgment). -/
inductive TaskType where
  | coveredScreen
  | truthValueJudgment
  deriving DecidableEq, Repr

/-- Trait descriptors made explicit to participants for each persona (§4.1). -/
def personaDescriptors : PersonaCondition → List String
  | .nerdy     => ["studious", "articulate", "introverted", "uptight"]
  | .chill     => ["laid-back", "sociable", "extroverted", "care-free"]
  | .noPersona => []

/-! ### Persona-indexed precision (Hypothesis 1)

The persona → precision link is an [eckert-2008] indexical field over the
[fiske-cuddy-glick-2007] social dimensions: precise speech indexes Competence
and anti-Solidarity (pedantic/uptight) but away from Warmth; approximate speech
the reverse (§2). -/

/-- The indexical field for numeral precision. The variable under study is the
    semantic `PrecisionMode` itself, not a study-local proxy. -/
def precisionField : IndexicalField PrecisionMode SocialDimension where
  association
    | .exact,       .competence     =>  1
    | .exact,       .warmth         => -1
    | .exact,       .antiSolidarity =>  1
    | .approximate, .competence     => -1
    | .approximate, .warmth         =>  1
    | .approximate, .antiSolidarity => -1
  order := .third

/-- The precision mode a persona favors (Nerdy precise, Chill approximate). -/
def personaPrecision : PersonaCondition → Option PrecisionMode
  | .nerdy     => some .exact
  | .chill     => some .approximate
  | .noPersona => none

/-- The SCM dimension a persona foregrounds (Nerdy Competence, Chill Warmth). -/
def personaDimension : PersonaCondition → Option SocialDimension
  | .nerdy     => some .competence
  | .chill     => some .warmth
  | .noPersona => none

/-- Production and comprehension cohere: the precision mode a persona favors
    positively indexes the dimension that persona foregrounds. -/
theorem bidirectionality
    (p : PersonaCondition) (d : SocialDimension) (v : PrecisionMode)
    (hd : personaDimension p = some d) (hv : personaPrecision p = some v) :
    precisionField.indexes v d := by
  cases p with
  | nerdy =>
    simp only [personaDimension, personaPrecision, Option.some.injEq] at hd hv
    subst hd; subst hv; show (1 : ℚ) > 0; norm_num
  | chill =>
    simp only [personaDimension, personaPrecision, Option.some.injEq] at hd hv
    subst hd; subst hv; show (1 : ℚ) > 0; norm_num
  | noPersona => simp [personaDimension] at hd

theorem scm_coherence_nerdy : precisionField.indexes .exact .competence :=
  bidirectionality .nerdy .competence .exact rfl rfl

theorem scm_coherence_chill : precisionField.indexes .approximate .warmth :=
  bidirectionality .chill .warmth .approximate rfl rfl

/-- Exact and approximate index opposite ways on every dimension. -/
theorem opposite_directions (d : SocialDimension) :
    precisionField.association .exact d = - precisionField.association .approximate d := by
  cases d <;> simp [precisionField]

/-- The precision field as a [burnett-2019] grounded field over the SCM space. -/
def precisionGroundedField : GroundedField PrecisionMode scmSpace :=
  fromIndexicalField precisionField

/-- Precise speech indexes {competent, cold, antiSolidary}. -/
theorem exact_scmProperties :
    precisionGroundedField.indexedProperties .exact = {.competent, .cold, .antiSolidary} := by
  decide

/-- Approximate speech indexes {incompetent, warm, solidary}. -/
theorem approx_scmProperties :
    precisionGroundedField.indexedProperties .approximate = {.incompetent, .warm, .solidary} := by
  decide

/-! ### The precision shift

A persona's precision mode induces a shift on the *reject-the-imprecise-reading*
scale: precise interpretation pushes toward rejection (`+1`), tolerant
interpretation toward acceptance (`-1`). The shift is derived from
`personaPrecision`, not stipulated per persona. -/

/-- A precision mode's directional pull on the rejection scale. -/
def precisionShift : PrecisionMode → SignType
  | .exact       =>  1   -- precise reading → reject imprecise descriptions
  | .approximate => -1   -- tolerant reading → accept them

/-- A persona's shift on the rejection scale, derived from its precision mode;
    the baseline persona is neutral. -/
def personaShift (p : PersonaCondition) : SignType :=
  (personaPrecision p).elim 0 precisionShift

/-- Nerdy and Chill pull in exactly opposite directions. -/
theorem nerdy_chill_opposite_shift : personaShift .nerdy = - personaShift .chill := by
  decide

/-! ### Task asymmetry from the prejudiciality of rejection

The pivot (§7): a *rejection* response is socially prejudicial in a Truth-Value
Judgment (it blames the speaker, [fricker-2007]) but not in a Covered-Screen
inference (it merely posits a different referent). A persona's shift manifests
unless it is a rejection-shift in a prejudicial task — which suppresses Nerdy
strictness in the TVJ while leaving Chill tolerance untouched. -/

/-- Whether a "reject" response in this task is socially prejudicial. -/
def RejectionPrejudicial : TaskType → Prop
  | .coveredScreen      => False
  | .truthValueJudgment => True

instance : DecidablePred RejectionPrejudicial
  | .coveredScreen      => .isFalse id
  | .truthValueJudgment => .isTrue trivial

/-- The shift that actually manifests in a task: a persona's `personaShift`,
    suppressed to neutral exactly when it points toward rejection (`+1`) in a
    task where rejection is prejudicial. -/
def predictedShift (p : PersonaCondition) (t : TaskType) : SignType :=
  if personaShift p = 1 ∧ RejectionPrejudicial t then 0 else personaShift p

/-- Inference task: rejection is not prejudicial, so both shifts manifest. -/
theorem predictedShift_coveredScreen :
    predictedShift .nerdy .coveredScreen = 1 ∧
    predictedShift .chill .coveredScreen = -1 := by decide

/-- Judgment task: the Nerdy rejection-shift is blocked; the Chill
    acceptance-shift survives. -/
theorem predictedShift_truthValueJudgment :
    predictedShift .nerdy .truthValueJudgment = 0 ∧
    predictedShift .chill .truthValueJudgment = -1 := by decide

/-- The Nerdy effect is task-dependent: present in inference, absent in judgment. -/
theorem nerdy_effect_is_task_dependent :
    predictedShift .nerdy .coveredScreen ≠ predictedShift .nerdy .truthValueJudgment := by
  decide

/-- The Chill (acceptance) effect is task-invariant: never blocked. -/
theorem acceptance_shift_never_blocked (t : TaskType) :
    predictedShift .chill t = personaShift .chill := by
  cases t <;> decide

/-- The blocking is structural: a shift is suppressed to neutral exactly when the
    persona is neutral, or its shift points toward rejection in a prejudicial
    task. The asymmetry follows from this, not from stipulated per-cell values. -/
theorem shift_blocked_iff (p : PersonaCondition) (t : TaskType) :
    predictedShift p t = 0 ↔
      personaShift p = 0 ∨ (personaShift p = 1 ∧ RejectionPrejudicial t) := by
  cases p <;> cases t <;> decide

/-! ### Roundness gating

Persona effects only have something to act on when the numeral is round enough
to carry an imprecise reading: `$200` does, `$207` does not
([krifka-2007]; `Semantics.Numerals.Precision`). -/

/-- The round numeral uttered in the illustrated stimulus (§2, Figure 1). -/
def statedAmount : Nat := 200

/-- The close-but-not-exact amount shown on the Imprecise screen (Figure 1). -/
def displayedAmount : Nat := 207

/-- A numeral supports an imprecise reading. -/
def impreciseReadingAvailable (n : Nat) : Prop :=
  inferPrecisionMode n = .approximate

instance (n : Nat) : Decidable (impreciseReadingAvailable n) :=
  inferInstanceAs (Decidable (inferPrecisionMode n = .approximate))

/-- Any multiple of 10 carries an imprecise reading — the substrate lemma
    `inferPrecisionMode_eq_approximate_of_ten_dvd` under this file's naming. -/
theorem div10_enables_imprecision (n : ℕ) (h10 : 10 ∣ n) :
    impreciseReadingAvailable n :=
  inferPrecisionMode_eq_approximate_of_ten_dvd h10

/-- Roundness gates the persona effect: the round numeral supports imprecision,
    the displayed value does not. -/
theorem roundness_gates_persona :
    impreciseReadingAvailable statedAmount ∧ ¬ impreciseReadingAvailable displayedAmount :=
  ⟨div10_enables_imprecision statedAmount (by decide), by decide⟩

/-- [beltrama-solt-burnett-2023]'s round stimulus (50) is the same kind of
    object: a round numeral whose precision resolution is under study. -/
theorem bsb_stim_also_round :
    impreciseReadingAvailable BeltramaSoltBurnett2022.stimRound :=
  div10_enables_imprecision BeltramaSoltBurnett2022.stimRound (by decide)

/-! ### Speaker-modulated halo

`speakerModulatedHalo` widens or narrows a numeral's pragmatic halo by a
speaker-specific multiplier; Chill speakers get a wider halo than Nerdy
ones. -/

/-- Speaker-conditioned pragmatic halo width: scales the substrate
    `haloWidth` by a speaker's tolerance multiplier. -/
def speakerModulatedHalo (multiplier : ℚ) (n : Nat) : ℚ :=
  multiplier * haloWidth n

/-- A larger multiplier yields a wider halo — the monotonicity that ties the
    Competence/Warmth ordering to tolerance width. -/
theorem wider_halo_of_larger_multiplier (m₁ m₂ : ℚ) (n : Nat)
    (hm : m₁ < m₂) (hn : 0 < haloWidth n) :
    speakerModulatedHalo m₁ n < speakerModulatedHalo m₂ n := by
  unfold speakerModulatedHalo
  exact mul_lt_mul_of_pos_right hm hn

/-- The round numeral has positive halo width, so speaker modulation bites. -/
theorem round_has_positive_halo : 0 < haloWidth statedAmount := by
  have hs : Semantics.Numerals.Roundness.roundnessScore 200 = 6 := by decide
  unfold haloWidth statedAmount
  rw [hs]; norm_num

/-! ### Data: predicted shift matches observed direction

The structural `predictedShift` is checked against the text-reported observed
rejection direction in every persona × task cell of the illustrated stimulus. -/

/-- A text-reported rejection direction as a sign on the rejection scale. -/
def observedDirection (s : String) : SignType :=
  if s == "higher" then 1 else if s == "lower" then -1 else 0

private def parsePersona : String → Option PersonaCondition
  | "nerdy"     => some .nerdy
  | "chill"     => some .chill
  | "noPersona" => some .noPersona
  | _           => none

private def parseTask : String → Option TaskType
  | "coveredScreen"      => some .coveredScreen
  | "truthValueJudgment" => some .truthValueJudgment
  | _                    => none

/-- The predicted shift equals the observed direction for a data row. -/
def rowConfirmsPrediction (e : LinguisticExample) : Bool :=
  match e.paperFeatures.lookup "persona" |>.bind parsePersona,
        e.paperFeatures.lookup "task" |>.bind parseTask,
        e.paperFeatures.lookup "rejectionVsBaseline" with
  | some p, some t, some dir => decide (predictedShift p t = observedDirection dir)
  | _, _, _ => false

-- Build-checked: every persona × task cell's predicted shift matches the
-- text-reported observed direction (§4.5, §5.3, §6).
#guard Examples.all.all rowConfirmsPrediction

end BeltramaSchwarz2024
