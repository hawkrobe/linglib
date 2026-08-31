import Linglib.Semantics.Quantification.Numerals.Roundness
import Linglib.Semantics.Quantification.Numerals.Precision
import Linglib.Pragmatics.SocialMeaning.IndexicalField
import Linglib.Pragmatics.SocialMeaning.SCM
import Linglib.Pragmatics.SocialMeaning.EckertMontague
import Linglib.Studies.BeltramaSoltBurnett2023
import Linglib.Data.Examples.BeltramaSchwarz2024
import Mathlib.Data.Sign.Defs
import Mathlib.Tactic.NormNum

/-!
# Social stereotypes and imprecision resolution

Formalization of [beltrama-schwarz-2024]: comprehenders interpret a round numeral more
strictly when its speaker is described as Nerdy and more tolerantly when Chill, but the
Nerdy effect appears only in the Covered-Screen inference task (Experiment 1), not in
the Truth-Value Judgment task (Experiment 2). The asymmetry is derived here from one
mechanism: a persona scales the pragmatic halo, the sign of the scaling is its rejection
shift, and rejection shifts are suppressed in tasks where rejection is prejudicial —
blames the speaker (§7, [fricker-2007]). The paper offers the gate tentatively, noting
it would also predict globally more charitable TVJ responses, which is not observed.

## Main definitions

* `precisionField` — [beltrama-solt-burnett-2023]'s measured indexical field pulled back
  (`IndexicalField.comap`) to the two `PrecisionMode`s manipulated here.
* `speakerHalo`, `personaShift` — the persona-scaled halo and the rejection shift,
  the sign of the halo narrowing relative to baseline.
* `RejectionPrejudicial`, `predictedShift` — the task gate suppressing rejection shifts.

## Main results

* `bidirectionality`, `haloMultiplier_coheres` — persona, precision mode, and tolerance
  multiplier cohere in the inherited field.
* `margin_resolved_by_persona`, `no_shift_on_sharp` — the $207 screen falls inside the
  default halo of "$200" but outside the Nerdy-narrowed one; a sharp numeral has zero
  halo, hence zero shift.
* `predictedShift_coveredScreen`, `predictedShift_truthValueJudgment`,
  `shift_blocked_iff` — the task asymmetry, derived from prejudiciality.

Experiment 1 (n = 282, §4.5): COVERED rates in the Imprecise cell were higher for Nerdy
(z = 6.62) and lower for Chill (z = 7.61) than baseline. Experiment 2 (n = 244, §5.3):
WRONG rates were lower for Chill (z = 8.43); no Nerdy difference (z = 0.15, p = .87).
Pooled (§6): a Nerdy × Task interaction (β = 0.62, p = .04) — the Nerdy effect is
present in the Covered-Screen task (z = 4.40), absent in the TVJ (z = 1.51). The
stimulus and observed directions are the rows of `Data.Examples.BeltramaSchwarz2024`.

## References

* [beltrama-schwarz-2024] — the paper.
* [beltrama-2018], [beltrama-solt-burnett-2023] — the precision stereotypes.
* [eckert-2008], [fiske-cuddy-glick-2007], [burnett-2019] — indexical fields, the
  Stereotype Content Model, the grounded-field lift.
* [donofrio-2018] — the persona-label paradigm; [fricker-2007] — testimonial injustice;
  [krifka-2007] — round-number imprecision.
-/

namespace BeltramaSchwarz2024

open SocialMeaning.IndexicalField
open SocialMeaning.SCM
open SocialMeaning.EckertMontague
open Semantics.Numerals.Precision
open Data.Examples (LinguisticExample)

/-! ### Conditions -/

/-- The two stereotype personae (§4.1). -/
inductive Persona where
  | nerdy
  | chill
  deriving DecidableEq, Repr

/-- Speaker persona condition (between-subjects, §4.1): a stereotype, or the
    no-description baseline. -/
abbrev PersonaCondition := Option Persona

/-- Experimental task: inferring the speaker's referent from a round numeral (§4) vs.
    judging an utterance against a known value (§5). -/
inductive TaskType where
  | coveredScreen
  | truthValueJudgment
  deriving DecidableEq, Repr

/-- Trait descriptors made explicit to participants (§4.1). -/
def Persona.descriptors : Persona → List String
  | .nerdy => ["studious", "articulate", "introverted", "uptight"]
  | .chill => ["laid-back", "sociable", "extroverted", "care-free"]

/-! ### The precision field, inherited from the measured one -/

/-- The two-way precision contrast embeds into [beltrama-solt-burnett-2023]'s three-way
    variant space. -/
def toVariant : PrecisionMode → BeltramaSoltBurnett2023.Variant
  | .exact       => .precise
  | .approximate => .approximate

/-- The indexical field for numeral precision: [beltrama-solt-burnett-2023]'s measured
    field pulled back along `toVariant` — grounded by construction, not by a stipulated
    twin. -/
def precisionField : IndexicalField PrecisionMode SocialDimension :=
  BeltramaSoltBurnett2023.bsbField.comap toVariant

/-- Exact and approximate index opposite ways on every dimension, inherited along the
    pullback. -/
theorem opposite_directions : precisionField.Antipodal .exact .approximate :=
  BeltramaSoltBurnett2023.opposite_directions

/-- The precision mode a persona favors (§2). -/
def Persona.precision : Persona → PrecisionMode
  | .nerdy => .exact
  | .chill => .approximate

/-- The SCM dimension a persona foregrounds (§2). -/
def Persona.dimension : Persona → SocialDimension
  | .nerdy => .competence
  | .chill => .warmth

/-- Production and comprehension cohere: the mode a persona favors positively indexes
    the dimension it foregrounds. -/
theorem bidirectionality (p : Persona) :
    precisionField.indexes p.precision p.dimension := by
  cases p <;> exact one_pos

/-- The precision field as a [burnett-2019] grounded field over the SCM space. -/
def precisionGroundedField : GroundedField PrecisionMode scmSpace :=
  fromIndexicalField precisionField

/-- Precise speech indexes {competent, cold, antiSolidary}. -/
theorem exact_scmProperties :
    precisionGroundedField.indexedProperties .exact =
      {.competent, .cold, .antiSolidary} := by
  decide

/-- Approximate speech indexes {incompetent, warm, solidary}. -/
theorem approx_scmProperties :
    precisionGroundedField.indexedProperties .approximate =
      {.incompetent, .warm, .solidary} := by
  decide

/-! ### Roundness gating -/

/-- The round numeral of the illustrated stimulus (§2, Figure 1). -/
def statedAmount : Nat := 200

/-- The close-but-not-exact amount on the Imprecise screen (Figure 1). -/
def displayedAmount : Nat := 207

/-- A numeral supports an imprecise reading ([krifka-2007]). -/
def impreciseReadingAvailable (n : Nat) : Prop :=
  inferPrecisionMode n = .approximate

instance (n : Nat) : Decidable (impreciseReadingAvailable n) :=
  inferInstanceAs (Decidable (inferPrecisionMode n = .approximate))

/-- The round numeral supports an imprecise reading
    (`inferPrecisionMode_eq_approximate_of_ten_dvd`); the displayed value does not. -/
theorem roundness_gates_persona :
    impreciseReadingAvailable statedAmount ∧
      ¬ impreciseReadingAvailable displayedAmount :=
  ⟨inferPrecisionMode_eq_approximate_of_ten_dvd ⟨20, rfl⟩, by decide⟩

/-! ### The speaker-scaled halo -/

/-- A persona's halo multiplier: Nerdy narrows, Chill widens. Only the ordering
    (Nerdy < baseline 1 < Chill) does any work below; the magnitudes are conventional. -/
def Persona.haloMultiplier : Persona → ℚ
  | .nerdy => 1/2
  | .chill => 2

/-- A persona narrows the halo exactly when its favored mode indexes away from Warmth
    in the inherited field. -/
theorem haloMultiplier_coheres (p : Persona) :
    p.haloMultiplier < 1 ↔ precisionField.association p.precision .warmth < 0 := by
  cases p <;>
    norm_num [Persona.haloMultiplier, precisionField, IndexicalField.comap, toVariant,
      Persona.precision, BeltramaSoltBurnett2023.bsbField, Function.comp]

/-- Speaker-conditioned halo width: the substrate `haloWidth` scaled by the condition's
    tolerance multiplier (baseline `1`). -/
def speakerHalo (c : PersonaCondition) (n : Nat) : ℚ :=
  c.elim 1 Persona.haloMultiplier * haloWidth n

/-- The stimulus numeral's default halo: `haloWidth 200 = 10`. -/
theorem haloWidth_stated : haloWidth statedAmount = 10 := by
  have hs : Semantics.Numerals.Roundness.roundnessScore 200 = 6 := by decide
  unfold haloWidth statedAmount
  rw [hs]; norm_num

/-- The margin is live: $207 falls within the default halo of "$200" (§4.1's 5–18%
    band), so the Imprecise cell is genuinely contested. -/
theorem displayed_within_default_halo :
    withinHalo statedAmount (displayedAmount : ℚ) := by
  unfold withinHalo
  rw [haloWidth_stated]
  norm_num [statedAmount, displayedAmount]

/-- The margin is resolved by persona: the Nerdy-narrowed halo excludes $207; the
    Chill-widened one includes it. -/
theorem margin_resolved_by_persona :
    ¬ |(displayedAmount : ℚ) - statedAmount| ≤ speakerHalo (some .nerdy) statedAmount ∧
      |(displayedAmount : ℚ) - statedAmount| ≤ speakerHalo (some .chill) statedAmount := by
  constructor <;>
    · simp only [speakerHalo, Option.elim, Persona.haloMultiplier, haloWidth_stated]
      norm_num [statedAmount, displayedAmount]

/-! ### The rejection shift, derived -/

/-- A condition's shift on the reject-the-imprecise-reading scale: the sign of its halo
    narrowing relative to baseline. A narrower halo excludes more values. -/
def personaShift (c : PersonaCondition) (n : Nat) : SignType :=
  SignType.sign (haloWidth n - speakerHalo c n)

/-- The shifts at the stimulus numeral: Nerdy `+1`, Chill `-1`, baseline `0`. -/
theorem personaShift_stated :
    personaShift (some .nerdy) statedAmount = 1 ∧
      personaShift (some .chill) statedAmount = -1 ∧
        personaShift none statedAmount = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [personaShift, speakerHalo, Option.elim, Persona.haloMultiplier,
      haloWidth_stated]
    norm_num [sign_pos]
  · simp only [personaShift, speakerHalo, Option.elim, Persona.haloMultiplier,
      haloWidth_stated]
    norm_num [sign_neg]
  · simp only [personaShift, speakerHalo, Option.elim, haloWidth_stated]
    norm_num [sign_zero]

/-- A sharp numeral has zero halo, so every condition's shift vanishes on it: the
    persona effect needs a round numeral to act on. -/
theorem no_shift_on_sharp (c : PersonaCondition) :
    personaShift c displayedAmount = 0 := by
  have h0 : haloWidth displayedAmount = 0 := by
    have hs : Semantics.Numerals.Roundness.roundnessScore 207 = 0 := by decide
    unfold haloWidth displayedAmount
    rw [hs]; norm_num
  rcases c with _ | p <;> simp [personaShift, speakerHalo, h0, sign_zero]

/-- Nerdy and Chill pull in exactly opposite directions on any numeral. -/
theorem nerdy_chill_opposite_shift (n : Nat) :
    personaShift (some .nerdy) n = - personaShift (some .chill) n := by
  rcases (haloWidth_nonneg n).eq_or_lt with h | h
  · simp [personaShift, speakerHalo, Option.elim, Persona.haloMultiplier, ← h, sign_zero]
  · have h1 : (0 : ℚ) < haloWidth n - 1 / 2 * haloWidth n := by linarith
    have h2 : haloWidth n - 2 * haloWidth n < 0 := by linarith
    simp only [personaShift, speakerHalo, Option.elim, Persona.haloMultiplier]
    rw [sign_pos h1, sign_neg h2, neg_neg]

/-! ### Task asymmetry from the prejudiciality of rejection -/

/-- Rejection is socially prejudicial in a Truth-Value Judgment — "wrong" blames the
    speaker ([fricker-2007]) — but not in Covered-Screen inference (§7). -/
def RejectionPrejudicial : TaskType → Prop := (· = .truthValueJudgment)

instance : DecidablePred RejectionPrejudicial := fun t =>
  inferInstanceAs (Decidable (t = .truthValueJudgment))

/-- The shift that manifests in a task: `personaShift` at the stimulus numeral,
    suppressed exactly when it points toward rejection in a prejudicial task. -/
def predictedShift (c : PersonaCondition) (t : TaskType) : SignType :=
  if 0 < personaShift c statedAmount ∧ RejectionPrejudicial t then 0
  else personaShift c statedAmount

/-- Inference task: rejection is not prejudicial, so both shifts manifest. -/
theorem predictedShift_coveredScreen :
    predictedShift (some .nerdy) .coveredScreen = 1 ∧
      predictedShift (some .chill) .coveredScreen = -1 := by
  refine ⟨?_, ?_⟩
  · simp only [predictedShift, personaShift_stated.1]; decide
  · simp only [predictedShift, personaShift_stated.2.1]; decide

/-- Judgment task: the Nerdy rejection shift is blocked; the Chill acceptance shift
    survives. -/
theorem predictedShift_truthValueJudgment :
    predictedShift (some .nerdy) .truthValueJudgment = 0 ∧
      predictedShift (some .chill) .truthValueJudgment = -1 := by
  refine ⟨?_, ?_⟩
  · simp only [predictedShift, personaShift_stated.1]; decide
  · simp only [predictedShift, personaShift_stated.2.1]; decide

/-- The Chill (acceptance) shift is task-invariant: never blocked. -/
theorem acceptance_shift_never_blocked (t : TaskType) :
    predictedShift (some .chill) t = personaShift (some .chill) statedAmount := by
  cases t <;>
    · simp only [predictedShift, personaShift_stated.2.1]
      decide

/-- The Nerdy effect is task-dependent: present in inference, absent in judgment. -/
theorem nerdy_effect_is_task_dependent :
    predictedShift (some .nerdy) .coveredScreen ≠
      predictedShift (some .nerdy) .truthValueJudgment := by
  simp only [predictedShift, personaShift_stated.1]
  decide

/-- Blocking is structural: a shift is suppressed to neutral exactly when the condition
    is already neutral or points toward rejection in a prejudicial task. -/
theorem shift_blocked_iff (c : PersonaCondition) (t : TaskType) :
    predictedShift c t = 0 ↔
      personaShift c statedAmount = 0 ∨
        (0 < personaShift c statedAmount ∧ RejectionPrejudicial t) := by
  have key : ∀ (s : SignType) (u : TaskType),
      (if 0 < s ∧ RejectionPrejudicial u then 0 else s) = 0 ↔
        s = 0 ∨ (0 < s ∧ RejectionPrejudicial u) := by
    intro s u
    cases s <;> cases u <;> decide
  exact key _ t

/-- `predictedShift`, tabulated over its six cells. -/
private theorem predictedShift_eq_ite (c : PersonaCondition) (t : TaskType) :
    predictedShift c t =
      if c = some .nerdy ∧ t = .coveredScreen then 1
        else if c = some .chill then -1 else 0 := by
  rcases c with _ | p
  · simp only [predictedShift, personaShift_stated.2.2]
    cases t <;> decide
  · cases p
    · simp only [predictedShift, personaShift_stated.1]
      cases t <;> decide
    · simp only [predictedShift, personaShift_stated.2.1]
      cases t <;> decide

/-! ### Data: predicted shift vs. observed direction -/

/-- A text-reported rejection direction as a sign on the rejection scale. -/
def observedDirection (s : String) : SignType :=
  if s == "higher" then 1 else if s == "lower" then -1 else 0

private def parsePersona : String → Option PersonaCondition
  | "nerdy"     => some (some .nerdy)
  | "chill"     => some (some .chill)
  | "noPersona" => some none
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

-- Every persona × task cell's predicted shift matches the text-reported observed
-- direction (§4.5, §5.3, §6). Routed through the tabulated form: kernel `decide`
-- cannot reduce the ℚ halo arithmetic inside `personaShift`.
example : ∀ e ∈ Examples.all, rowConfirmsPrediction e := by
  simp only [rowConfirmsPrediction, predictedShift_eq_ite]
  decide

end BeltramaSchwarz2024
