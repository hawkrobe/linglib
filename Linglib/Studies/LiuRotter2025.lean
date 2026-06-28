import Linglib.Semantics.Modality.ModalTypes
import Linglib.Fragments.English.Auxiliaries
import Linglib.Data.Examples.LiuRotter2025
import Mathlib.Data.Sign.Defs
import Mathlib.Algebra.Order.Field.Rat

/-!
# [liu-rotter-2025]: Linguistic and Social Meaning Match — modal concord

Modal concord (MC) doubles two modal elements of the same force and flavor
(*may possibly*, *must certainly*). The semantic-vacuity account
([zeijlstra-2007]) treats one element as uninterpretable, so MC and the single
modal (SM) should be truth-conditionally identical. [liu-rotter-2025] tests this
in one 2×2 (FORCE × NUMBER) Latin-square experiment (93 of 104 US-English
participants, Prolific) and finds MC is **not** vacuous: doubling *strengthens*
speaker commitment for necessity but *weakens* it for possibility — a
FORCE × NUMBER crossover (interaction β̂ = −1.85, χ²(1) = 41.51, p < .001;
necessity sub-effect β̂ = +1.50, possibility β̂ = −0.35). The concord effect is
thus a **sign indexed by force**, supporting the modal-spread analysis
([giannakidou-mari-2018]).

This file formalizes that structure, not the regression tables: the effect of
concord as a force-indexed `SignType`, the crossover as the property that
distinguishes the spread account from vacuity, and the data as a sign-prediction
target.

## Main definitions
* `spreadEffect` — [giannakidou-mari-2018]'s account: the force-indexed sign of
  the concord effect on commitment (+ for necessity, − for possibility).
* `vacuityEffect` — [zeijlstra-2007]'s rival: the null effect, force-blind.
* `warmthEffect` — the force-blind MC warmth penalty (a second, distinct profile).
* `ShiftObservation`, `accountErrs` — score an account against the observed
  MC − SM shift in `Data.Examples.LiuRotter2025`.

## Main results
* `spread_crossover` — the FORCE × NUMBER interaction as a sign reversal.
* `spread_nonvacuous`, `spread_refutes_vacuity` — MC is non-vacuous; a sign that
  reverses with force cannot be the agreement account's force-blind null.
* `warmth_ne_spread` — the warmth penalty is constant across force, so it is a
  NUMBER main effect, not the commitment crossover.
* `vacuity_errs_on_shift` — vacuity errs on every cell with a real shift.

## Implementation notes
The effect of concord is a `SignType` (the magnitude is a model estimate, not a
formal commitment); the rival accounts are `ModalForce → SignType`. Cell means
live in `Data.Examples.LiuRotter2025` (×100, on the 1–7 scale); they do not
reduce in the kernel (string-keyed `paperFeatures`, `ℚ` comparison), so concrete
shifts are *computed* via `#eval` while the kernel-checkable content is each
account's systematic error.
-/

namespace LiuRotter2025

open Semantics.Modality (ModalForce ModalItem)
open English.Auxiliaries
open Data.Examples (LinguisticExample)

/-! ### The concord effect as a force-indexed sign -/

/-- The modal-spread account ([giannakidou-mari-2018]): the modal adverb in an MC
    construction is not vacuous; doubling reinforces the force, raising speaker
    commitment for necessity (∀) and lowering it for possibility (∃). -/
def spreadEffect : ModalForce → SignType
  | .necessity     => 1
  | .weakNecessity => 1
  | .possibility   => -1

/-- The semantic-vacuity / syntactic-agreement account ([zeijlstra-2007]): one
    modal carries an uninterpretable feature and contributes no operator at LF,
    so MC and SM are truth-conditionally identical — concord has no commitment
    effect, whatever the force. -/
def vacuityEffect : ModalForce → SignType := fun _ => 0

@[simp] theorem spreadEffect_necessity : spreadEffect .necessity = 1 := rfl
@[simp] theorem spreadEffect_possibility : spreadEffect .possibility = -1 := rfl
@[simp] theorem vacuityEffect_apply (f : ModalForce) : vacuityEffect f = 0 := rfl

/-- The FORCE × NUMBER interaction: the concord effect reverses sign with force. -/
theorem spread_crossover : spreadEffect .necessity ≠ spreadEffect .possibility := by decide

/-- MC is semantically non-vacuous: concord shifts commitment under both forces. -/
theorem spread_nonvacuous :
    spreadEffect .necessity ≠ 0 ∧ spreadEffect .possibility ≠ 0 := by decide

/-- Vacuity predicts no interaction: the (null) effect is the same for every force. -/
theorem vacuity_no_interaction (f g : ModalForce) : vacuityEffect f = vacuityEffect g := rfl

/-- The crossover refutes vacuity: the spread effect disagrees with the
    agreement account's force-blind null already at necessity (+1 vs 0). -/
theorem spread_refutes_vacuity : spreadEffect ≠ vacuityEffect :=
  fun h => absurd (congrFun h .necessity) (by decide)

/-! ### A second profile: the warmth penalty

Beyond commitment, the social-meaning measures split in two ([liu-rotter-2025]
Table 5). Confidence — and, for necessity, formality — *tracks commitment*,
showing the same force-indexed crossover (the "match" of the title: meaning
strength and social perception move together). Friendliness, warmth, and
coolness instead show a force-blind main effect of NUMBER: MC is rated lower
than SM regardless of force, a uniform social cost of doubling. -/

/-- The warmth profile: a force-blind penalty. MC is perceived as less warm
    (friendly, warm, cool) than SM under both forces — a NUMBER main effect with
    no interaction, distinct from the commitment crossover. -/
def warmthEffect : ModalForce → SignType := fun _ => -1

theorem warmth_no_interaction (f g : ModalForce) : warmthEffect f = warmthEffect g := rfl

theorem warmth_real_cost (f : ModalForce) : warmthEffect f ≠ 0 := by
  show (-1 : SignType) ≠ 0; decide

/-- The warmth penalty is not the commitment crossover: it disagrees with the
    spread effect at necessity (−1 vs +1), being constant where spread reverses. -/
theorem warmth_ne_spread : warmthEffect ≠ spreadEffect :=
  fun h => absurd (congrFun h .necessity) (by decide)

/-! ### The concord precondition in the fragment

Both MC stimulus pairs share concord-compatible force — the structural
precondition for concord ([zeijlstra-2007]). The auxiliaries carry
uninterpretable features in the fragment, so the agreement account's vacuous
element is `must`/`may`; the crossover overturns its prediction that this
element contributes nothing. -/

/-- *must* + *certainly* (the necessity MC stimulus) share necessity-type force. -/
theorem must_certainly_share :
    must.toModalItem.sharesConcordForce certainly.toModalItem = true := by decide

/-- *may* + *possibly* (the possibility MC stimulus) share possibility force. -/
theorem may_possibly_share :
    may.toModalItem.sharesConcordForce possibly.toModalItem = true := by decide

/-- Zeijlstra's vacuous element: the modal auxiliaries are uninterpretable in
    the fragment, so under the agreement account they contribute no operator. -/
theorem stimulus_auxiliaries_uninterpretable :
    must.interpretability = some .uninterpretable ∧
    may.interpretability = some .uninterpretable := ⟨rfl, rfl⟩

/-! ### Predicting against the data

The four condition cells (`Data.Examples.LiuRotter2025`) carry the Table 1 means
(×100, on the 1–7 Likert scale) for every measure. An account predicts the
*sign* of the concord shift MC − SM per force; the observed sign is read off the
cell means. -/

/-- An observed concord shift for one measure under one force: the MC and SM
    cell means. -/
structure ShiftObservation where
  force  : ModalForce
  mcMean : ℚ
  smMean : ℚ

/-- The observed sign of the concord shift (MC − SM). -/
def ShiftObservation.observedSign (o : ShiftObservation) : SignType :=
  SignType.sign (o.mcMean - o.smMean)

/-- An account errs on an observation when its predicted sign disagrees with the
    observed shift sign. -/
def accountErrs (acc : ModalForce → SignType) (o : ShiftObservation) : Prop :=
  acc o.force ≠ o.observedSign

/-- The agreement account errs on every cell with a real shift: predicting a
    null effect, it cannot match any nonzero MC − SM difference. -/
theorem vacuity_errs_on_shift (o : ShiftObservation) (h : o.mcMean ≠ o.smMean) :
    accountErrs vacuityEffect o := by
  show (0 : SignType) ≠ SignType.sign (o.mcMean - o.smMean)
  exact (sign_ne_zero.mpr (sub_ne_zero.mpr h)).symm

/-- When the observed shift carries the sign the spread account predicts, the
    account does not err — the content the agreement account cannot deliver. -/
theorem spread_correct_of_match (o : ShiftObservation)
    (h : o.observedSign = spreadEffect o.force) : ¬ accountErrs spreadEffect o := by
  simp only [accountErrs, not_not]; exact h.symm

/-! ### The observed shifts

`forceKey`/`findCell`/`observedShift` join the MC and SM cells of `Examples.all`
to read the observed sign for any measure. The `#eval`s exhibit the paper's
findings: the spread sign predicts both commitment and confidence (the
crossover, ±1 by force), while warmth is a uniform penalty (−1 under both
forces). Means do not reduce in the kernel, so these are computed, not proved. -/

/-- The `paperFeatures` `force` value for a modal force. -/
def forceKey : ModalForce → String
  | .necessity     => "necessity"
  | .weakNecessity => "necessity"
  | .possibility   => "possibility"

/-- The cell with the given force and number (`"MC"`/`"SM"`) values. -/
def findCell (force number : String) : Option LinguisticExample :=
  Examples.all.find? fun e =>
    e.paperFeatures.lookup "force" == some force &&
    e.paperFeatures.lookup "number" == some number

/-- Read a Likert mean (stored ×100) for `measure` from a cell's features. -/
def cellMean (measure : String) (e : LinguisticExample) : Option ℚ :=
  (e.paperFeatures.lookup measure).bind fun s => s.toNat?.map fun n => (n : ℚ) / 100

/-- The observed MC − SM shift for `measure` under `force`, joining the cells. -/
def observedShift (measure : String) (force : ModalForce) : Option ShiftObservation := do
  let mc ← findCell (forceKey force) "MC"
  let sm ← findCell (forceKey force) "SM"
  let mcv ← cellMean measure mc
  let smv ← cellMean measure sm
  pure { force := force, mcMean := mcv, smMean := smv }

-- Commitment: necessity MC strengthens (+1), possibility MC weakens (−1).
#eval (observedShift "commitment" .necessity).map fun o => (o.observedSign : ℤ)   -- some 1
#eval (observedShift "commitment" .possibility).map fun o => (o.observedSign : ℤ) -- some -1
-- Confidence tracks commitment — the "match".
#eval (observedShift "confidence" .necessity).map fun o => (o.observedSign : ℤ)   -- some 1
#eval (observedShift "confidence" .possibility).map fun o => (o.observedSign : ℤ) -- some -1
-- Warmth: a uniform penalty, −1 under both forces.
#eval (observedShift "warmth" .necessity).map fun o => (o.observedSign : ℤ)       -- some -1
#eval (observedShift "warmth" .possibility).map fun o => (o.observedSign : ℤ)     -- some -1

end LiuRotter2025
