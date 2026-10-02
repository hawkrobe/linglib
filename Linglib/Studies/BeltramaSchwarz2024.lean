module

public import Linglib.Semantics.Degree.Granularity
public import Mathlib.Data.Rat.Floor
public import Linglib.Pragmatics.SocialMeaning.IndexicalField
public import Linglib.Pragmatics.SocialMeaning.Dimension
public import Linglib.Pragmatics.SocialMeaning.Persona
public import Linglib.Studies.BeltramaSoltBurnett2023
public import Linglib.Data.Examples.BeltramaSchwarz2024
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Tactic.NormNum

/-!
# Social stereotypes and imprecision resolution

Beltrama and Schwarz find that comprehenders interpret a round numeral more strictly when its
speaker is described as Nerdy and more tolerantly when Chill, but that the Nerdy effect appears
only in a Covered-Screen inference task, not in a Truth-Value Judgment task. A numeral denotes the
cell of its value at the comprehender's precision level, and a persona moves that level toward
strictness when the precision variant it favors indexes Competence, Hypothesis 1 grounded in the
bidirectionality of social meaning. A shift toward rejection is suppressed where rejection is
prejudicial, blaming the speaker (§7); the paper offers this gate tentatively, noting that it
would also predict globally more charitable judgments, which are not observed.

## Main definitions

* `precisionField`: Beltrama, Solt and Burnett's measured indexical field over their precision
  variants, of which the precise and approximate ones are at issue here.
* `personaShift`, `level`: the strictness shift a persona induces, read off the field, and the
  precision level it sets.
* `Covered`: a covered-screen response, the displayed value outside the numeral's extension.
* `RejectionPrejudicial`, `predictedShift`: the task gate suppressing rejection shifts.

## Main results

* `Covered.of_le`: Hypothesis 1, a covered response under a more liberal condition is one under a
  stricter condition.
* `personaShift_nerdy_eq_neg_chill`, `personaShift_eq_neg_warmth`: the personas pull in opposite
  directions, and the Competence and Warmth clusters predict the same shift.
* `predictedShift_coveredScreen`, `predictedShift_truthValueJudgment`, `shift_blocked_iff`: the
  task asymmetry, derived from prejudiciality.

## Implementation notes

The extension of a numeral at a precision level is its cell in `Degree.Granularity`, as the
paper's "a lower level of precision … includes the value displayed on the visible screen in the
numeral's extension" (§4.1) suggests, and a persona moves the level by one halving step. The
paper's 5–18% deviations are a stimulus design leaving participants on the fence, not a level;
the illustration with a twenty-dollar baseline grain is conventional. In Experiment 1 (§4.5)
covered responses in the Imprecise cell were more frequent for Nerdy and less for Chill than at
baseline; in Experiment 2 (§5.3) rejections were less frequent for Chill with no Nerdy difference;
the rows of `Data.Examples.BeltramaSchwarz2024` record the directions.

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
* [sauerland-stateva-2011]
-/

@[expose] public section

namespace BeltramaSchwarz2024

open SocialMeaning Degree.Granularity

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

/-- Production and comprehension cohere: the mode a persona favors positively indexes the dimension
it foregrounds. -/
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

/-- The round numeral supports an imprecise reading and the displayed value does not. -/
theorem roundness_gates_persona :
    impreciseReadingAvailable statedAmount ∧
      ¬ impreciseReadingAvailable displayedAmount :=
  ⟨⟨20, rfl⟩, by decide⟩

/-! ### The precision level

A numeral denotes the cell of its value in the grain of the comprehender's precision level, so a
less precise interpretation, at a coarser grain, takes more values into the numeral's extension
(§4.1). A persona moves the precision level by one step of halving or doubling, [krifka-2007]'s
optimal refinement, toward strictness when its favored variant indexes Competence: Hypothesis 1,
grounded in the bidirectionality of social meaning (§3). -/

/-- The shift of a persona condition toward a stricter interpretation is the sign with which its
favored variant indexes Competence, and `0` at baseline. -/
def personaShift : PersonaCondition → SignType
  | none => 0
  | some p => precisionField p.precision .competence

@[simp] theorem personaShift_none : personaShift none = 0 := rfl

theorem personaShift_nerdy : personaShift (some .nerdy) = 1 := by decide +kernel

theorem personaShift_chill : personaShift (some .chill) = -1 := by decide +kernel

/-- Nerdy and Chill pull in opposite directions, since their favored variants are antipodal in the
field. -/
theorem personaShift_nerdy_eq_neg_chill :
    personaShift (some .nerdy) = -personaShift (some .chill) :=
  congrFun BeltramaSoltBurnett2023.opposite_directions .competence

/-- The Competence and the Warmth clusters predict the same shift, so the sign field cannot tell
apart the two sources of the effect that §3 distinguishes. -/
theorem personaShift_eq_neg_warmth (p : Persona) :
    personaShift (some p) = -precisionField p.precision .warmth := by
  cases p <;> decide +kernel

/-- The precision level of a persona condition is the baseline grain width `w` halved once per
step toward strictness. -/
def level (w : ℚ) (c : PersonaCondition) : ℚ := w / 2 ^ (personaShift c : ℤ)

@[simp] theorem level_none (w : ℚ) : level w none = w := by simp [level, personaShift]

@[simp] theorem level_nerdy (w : ℚ) : level w (some .nerdy) = w / 2 := by
  simp [level, personaShift_nerdy]

@[simp] theorem level_chill (w : ℚ) : level w (some .chill) = 2 * w := by
  simp [level, personaShift_chill, div_eq_mul_inv, mul_comm]

/-- A comprehender picks the covered screen when the displayed value `d` lies outside the
extension of the uttered numeral `n` at their precision level. -/
def Covered (w : ℚ) (c : PersonaCondition) (n d : ℚ) : Prop := d ∉ (grain (level w c)).cell n

/-- Around a numeral that is a point of both precision levels, a covered response under a more
liberal condition is a covered response under a stricter one, Hypothesis 1. -/
theorem Covered.of_le {w n d : ℚ} (hw : 0 < w) {c c' : PersonaCondition}
    (h : personaShift c ≤ personaShift c') (hn : n ∈ AddSubgroup.zmultiples (level w c))
    (hn' : n ∈ AddSubgroup.zmultiples (level w c')) (hd : Covered w c n d) :
    Covered w c' n d := fun hd' ↦ by
  have hle : level w c' ≤ level w c := by
    rcases c with _ | _ | _ <;> rcases c' with _ | _ | _ <;>
      simp only [personaShift_none, personaShift_nerdy, personaShift_chill] at h <;>
      first
        | (simp only [level_none, level_nerdy, level_chill]; linarith)
        | exact absurd h (by decide)
  have hpos : 0 < level w c' := by
    rcases c' with _ | _ | _ <;> simp only [level_none, level_nerdy, level_chill] <;> positivity
  exact hd (cell_subset_cell hpos hle hn' hn hd')

/-- With a baseline grain of twenty dollars the $207 screen lies inside the extension of *$200* at
baseline and for Chill, and outside it for Nerdy. -/
example : Covered 20 (some .nerdy) 200 207 ∧ ¬ Covered 20 none 200 207 ∧
    ¬ Covered 20 (some .chill) 200 207 := by
  have h (k : ℤ) (ε : ℚ) (hk : (k : ℚ) * ε = 200) (hε : 0 < ε) :
      (grain ε).cell 200 = Set.Ico (200 - ε / 2) (200 + ε / 2) := by
    rw [cell_grain hε, representative_eq_self_of_mem_zmultiples hε.ne'
      (AddSubgroup.mem_zmultiples_iff.2 ⟨k, by rw [zsmul_eq_mul, hk]⟩)]
  simp only [Covered, level_nerdy, level_none, level_chill, not_not]
  refine ⟨?_, ?_, ?_⟩
  · rw [h 20 _ (by norm_num) (by norm_num)]; norm_num
  · rw [h 10 _ (by norm_num) (by norm_num)]; norm_num
  · rw [h 5 _ (by norm_num) (by norm_num)]; norm_num

/-! ### Task asymmetry from the prejudiciality of rejection -/

/-- Rejection is socially prejudicial in a Truth-Value Judgment — "wrong" blames the speaker
([fricker-2007]) — but not in Covered-Screen inference (§7). -/
def RejectionPrejudicial : TaskType → Prop := (· = .truthValueJudgment)

instance : DecidablePred RejectionPrejudicial := fun t =>
  inferInstanceAs (Decidable (t = .truthValueJudgment))

/-- The shift that manifests in a task is `personaShift`, suppressed exactly when it points toward
rejection in a prejudicial task. -/
def predictedShift (c : PersonaCondition) (t : TaskType) : SignType :=
  if 0 < personaShift c ∧ RejectionPrejudicial t then 0 else personaShift c

/-- In the inference task rejection is not prejudicial, so both shifts manifest. -/
theorem predictedShift_coveredScreen :
    predictedShift (some .nerdy) .coveredScreen = 1 ∧
      predictedShift (some .chill) .coveredScreen = -1 := by
  decide +kernel

/-- In the judgment task the Nerdy rejection shift is blocked and the Chill acceptance shift
survives. -/
theorem predictedShift_truthValueJudgment :
    predictedShift (some .nerdy) .truthValueJudgment = 0 ∧
      predictedShift (some .chill) .truthValueJudgment = -1 := by
  decide +kernel

/-- The Chill (acceptance) shift is task-invariant: never blocked. -/
theorem acceptance_shift_never_blocked (t : TaskType) :
    predictedShift (some .chill) t = personaShift (some .chill) := by
  cases t <;> decide +kernel

/-- The Nerdy effect is task-dependent: present in inference, absent in judgment. -/
theorem nerdy_effect_is_task_dependent :
    predictedShift (some .nerdy) .coveredScreen ≠
      predictedShift (some .nerdy) .truthValueJudgment := by
  decide +kernel

/-- Blocking is structural: a shift is suppressed to neutral exactly when the condition is already
neutral or points toward rejection in a prejudicial task. -/
theorem shift_blocked_iff (c : PersonaCondition) (t : TaskType) :
    predictedShift c t = 0 ↔
      personaShift c = 0 ∨
        (0 < personaShift c ∧ RejectionPrejudicial t) := by
  have key : ∀ (s : SignType) (u : TaskType),
      (if 0 < s ∧ RejectionPrejudicial u then 0 else s) = 0 ↔
        s = 0 ∨ (0 < s ∧ RejectionPrejudicial u) := by
    intro s u
    cases s <;> cases u <;> decide
  exact key _ t

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
-- direction (§4.5, §5.3, §6).
example : ∀ e ∈ Examples.all, rowConfirmsPrediction e := by
  decide +kernel

end BeltramaSchwarz2024
