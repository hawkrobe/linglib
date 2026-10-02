module

public import Linglib.Semantics.Quantification.Numerals.Roundness
public import Linglib.Pragmatics.SocialMeaning.IndexicalField
public import Linglib.Pragmatics.SocialMeaning.Dimension
public import Linglib.Pragmatics.SocialMeaning.Persona
public import Linglib.Studies.BeltramaSoltBurnett2023
public import Linglib.Data.Examples.BeltramaSchwarz2024
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Social stereotypes and imprecision resolution

Beltrama and Schwarz find that comprehenders interpret a round numeral more strictly when its
speaker is described as Nerdy and more tolerantly when Chill, but that the Nerdy effect appears
only in a Covered-Screen inference task, not in a Truth-Value Judgment task. Here the asymmetry
follows from one mechanism: a persona scales the pragmatic halo, the sign of the scaling is its
rejection shift, and a rejection shift is suppressed where rejection is prejudicial, blaming the
speaker (§7). The paper offers this gate tentatively, noting that it would also predict globally
more charitable judgments, which are not observed.

## Main definitions

* `precisionField`: Beltrama, Solt and Burnett's measured indexical field over their precision
  variants, of which the precise and approximate ones are at issue here.
* `haloWidth`, `withinHalo`: the pragmatic halo of a numeral, growing with its roundness.
* `speakerHalo`, `personaShift`: the persona-scaled halo and the rejection shift.
* `RejectionPrejudicial`, `predictedShift`: the task gate suppressing rejection shifts.

## Main results

* `bidirectionality`, `haloMultiplier_coheres`: persona, precision variant and tolerance
  multiplier cohere in the inherited field.
* `margin_resolved_by_persona`, `no_shift_on_sharp`: the $207 screen falls inside the default
  halo of *$200* but outside the Nerdy-narrowed one, and a sharp numeral has no halo to shift.
* `predictedShift_coveredScreen`, `predictedShift_truthValueJudgment`, `shift_blocked_iff`: the
  task asymmetry, derived from prejudiciality.

## Implementation notes

In Experiment 1 (n = 282, §4.5) COVERED rates in the Imprecise cell were higher for Nerdy and
lower for Chill than baseline; in Experiment 2 (n = 244, §5.3) WRONG rates were lower for Chill
with no Nerdy difference, and the pooled analysis (§6) shows a Nerdy × Task interaction. The
stimulus and observed directions are the rows of `Data.Examples.BeltramaSchwarz2024`. The halo
magnitudes and the roundness gate, a multiple of ten, are conventional.

## References

* [beltrama-schwarz-2024]
* [beltrama-2018]
* [beltrama-solt-burnett-2023]
* [eckert-2008]
* [fiske-cuddy-glick-2007]
* [burnett-2019]
* [donofrio-2018]
* [fricker-2007]
* [krifka-2007]
* [lasersohn-1999]
* [woodin-etal-2024]
-/

@[expose] public section

namespace BeltramaSchwarz2024

open SocialMeaning

/-! ### Conditions -/

/-- The two stereotype personae (§4.1). -/
inductive Persona where
  | nerdy
  | chill
  deriving DecidableEq, Repr

/-- A speaker persona condition, varied between subjects (§4.1), is a stereotype or the
no-description baseline. -/
abbrev PersonaCondition := Option Persona

/-- The experimental task is inferring the speaker's referent from a round numeral (§4) or judging
an utterance against a known value (§5). -/
inductive TaskType where
  | coveredScreen
  | truthValueJudgment
  deriving DecidableEq, Repr

/-- Trait descriptors made explicit to participants (§4.1). -/
def Persona.descriptors : Persona → List String
  | .nerdy => ["studious", "articulate", "introverted", "uptight"]
  | .chill => ["laid-back", "sociable", "extroverted", "care-free"]

/-! ### The precision field, inherited from the measured one -/

/-- The indexical field for numeral precision is [beltrama-solt-burnett-2023]'s measured field,
inherited rather than restipulated. -/
def precisionField : AssociationField BeltramaSoltBurnett2023.Variant Dimension SignType :=
  BeltramaSoltBurnett2023.bsbField

/-- The precision variant a persona favors (§2). -/
def Persona.precision : Persona → BeltramaSoltBurnett2023.Variant
  | .nerdy => .precise
  | .chill => .approximate

/-- The SCM dimension a persona foregrounds (§2). -/
def Persona.dimension : Persona → Dimension
  | .nerdy => .competence
  | .chill => .warmth

/-- Production and comprehension cohere: the mode a persona favors positively indexes
    the dimension it foregrounds. -/
theorem bidirectionality (p : Persona) :
    precisionField.Indexes p.precision p.dimension := by
  cases p <;> decide +kernel

/-- The precision field as a [burnett-2019] grounded field over the SCM space. -/
def precisionGroundedField : GroundedField BeltramaSoltBurnett2023.Variant Pole.incompatible :=
  precisionField.ground

/-- Precise speech indexes {competent, cold, antiSolidary}. -/
theorem exact_scmProperties :
    precisionGroundedField.indexes .precise =
      {.competent, .cold, .antiSolidary} := by
  decide +kernel

/-- Approximate speech indexes {incompetent, warm, solidary}. -/
theorem approx_scmProperties :
    precisionGroundedField.indexes .approximate =
      {.incompetent, .warm, .solidary} := by
  decide +kernel

/-! ### Roundness gating -/

/-- The round numeral of the illustrated stimulus (§2, Figure 1). -/
def statedAmount : Nat := 200

/-- The close-but-not-exact amount on the Imprecise screen (Figure 1). -/
def displayedAmount : Nat := 207

/-- A numeral supports an imprecise reading when it is round, a multiple of ten and so a point of
the coarser decimal scale ([krifka-2007]). -/
def impreciseReadingAvailable (n : Nat) : Prop := 10 ∣ n

instance (n : Nat) : Decidable (impreciseReadingAvailable n) :=
  inferInstanceAs (Decidable (10 ∣ n))

/-- The round numeral supports an imprecise reading
    and the displayed value does not. -/
theorem roundness_gates_persona :
    impreciseReadingAvailable statedAmount ∧
      ¬ impreciseReadingAvailable displayedAmount :=
  ⟨⟨20, rfl⟩, by decide⟩

/-! ### The pragmatic halo

[lasersohn-1999]'s halo of a numeral, the values close enough to count as its value, here grows
with the numeral's roundness score; only that monotone relationship is motivated, by
[woodin-etal-2024]'s corpus finding, and the magnitude factors are conventional. -/

/-- The halo width of a numeral grows with its roundness score, scaled by its magnitude. -/
def haloWidth (n : Nat) : ℚ :=
  let magnitudeFactor : ℚ :=
    if n ≥ 1000 then 50 else if n ≥ 100 then 10 else if n ≥ 10 then 5 else 1
  magnitudeFactor * Numerals.Roundness.roundnessScore n / 6

/-- A value lies within a numeral's halo when it is no farther from the numeral than the halo
width. -/
def withinHalo (n : Nat) (q : ℚ) : Prop := |q - (n : ℚ)| ≤ haloWidth n

theorem haloWidth_nonneg (n : Nat) : 0 ≤ haloWidth n := by
  have h : (0 : ℚ) ≤ (Numerals.Roundness.roundnessScore n : ℚ) := Nat.cast_nonneg _
  simp only [haloWidth]
  split_ifs <;> exact div_nonneg (mul_nonneg (by norm_num) h) (by norm_num)

/-! ### The speaker-scaled halo -/

/-- A persona's halo multiplier narrows the halo for Nerdy and widens it for Chill. Only the
ordering, Nerdy below the baseline `1` below Chill, does any work below; the magnitudes are
conventional. -/
def Persona.haloMultiplier : Persona → ℚ
  | .nerdy => 1/2
  | .chill => 2

/-- A persona narrows the halo exactly when its favored mode indexes away from Warmth
    in the inherited field. -/
theorem haloMultiplier_coheres (p : Persona) :
    p.haloMultiplier < 1 ↔ precisionField p.precision .warmth < 0 := by
  cases p <;> decide +kernel

/-- The speaker-conditioned halo width is `haloWidth` scaled by the condition's tolerance
multiplier, `1` at baseline. -/
def speakerHalo (c : PersonaCondition) (n : Nat) : ℚ :=
  c.elim 1 Persona.haloMultiplier * haloWidth n

/-- The stimulus numeral's default halo has width `haloWidth 200 = 10`. -/
theorem haloWidth_stated : haloWidth statedAmount = 10 := by
  have hs : Numerals.Roundness.roundnessScore 200 = 6 := by decide
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

/-- A condition's shift on the reject-the-imprecise-reading scale is the sign of its halo narrowing
relative to baseline, since a narrower halo excludes more values. -/
def personaShift (c : PersonaCondition) (n : Nat) : SignType :=
  SignType.sign (haloWidth n - speakerHalo c n)

/-- At the stimulus numeral the shifts are `+1` for Nerdy, `-1` for Chill and `0` at baseline. -/
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
    have hs : Numerals.Roundness.roundnessScore 207 = 0 := by decide
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

/-- The shift that manifests in a task is `personaShift` at the stimulus numeral, suppressed exactly
when it points toward rejection in a prejudicial task. -/
def predictedShift (c : PersonaCondition) (t : TaskType) : SignType :=
  if 0 < personaShift c statedAmount ∧ RejectionPrejudicial t then 0
  else personaShift c statedAmount

/-- In the inference task rejection is not prejudicial, so both shifts manifest. -/
theorem predictedShift_coveredScreen :
    predictedShift (some .nerdy) .coveredScreen = 1 ∧
      predictedShift (some .chill) .coveredScreen = -1 := by
  refine ⟨?_, ?_⟩
  · simp only [predictedShift, personaShift_stated.1]; decide
  · simp only [predictedShift, personaShift_stated.2.1]; decide

/-- In the judgment task the Nerdy rejection shift is blocked and the Chill acceptance shift
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

def parsePersona : String → Option PersonaCondition
  | "nerdy"     => some (some .nerdy)
  | "chill"     => some (some .chill)
  | "noPersona" => some none
  | _           => none

def parseTask : String → Option TaskType
  | "coveredScreen"      => some .coveredScreen
  | "truthValueJudgment" => some .truthValueJudgment
  | _                    => none

/-- The predicted shift equals the observed direction for a data row. -/
def rowConfirmsPrediction (e : Datum) : Bool :=
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
