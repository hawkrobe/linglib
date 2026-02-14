import Linglib.Core.Empirical
import Linglib.Theories.DynamicSemantics.Effects.Epistemic.Basic

/-!
# Khoo (2015): Modal Disagreements

Empirical data from Khoo's experiment on epistemic modal disagreements.
The key finding: speakers reject might-claims (high rejection rating)
without judging them false (low falsity rating). This dissociation
between rejection and falsity judgments is predicted by Rudin's (2025)
Neo-Stalnakerian Framework, which derives it from the fact that truth
depends on the *assertor's* information while rejection depends on the
*rejector's* information.

## Experimental Design

- 60 participants on Amazon Mechanical Turk
- 2 × 2 between-subjects: {Control, Modal} × {False, Rejection}
- 7-point Likert scale (1 = completely disagree, 7 = completely agree)
- Control vignette: non-modal assertion ("Jim is at home right now")
- Modal vignette: epistemic might ("Fat Tony might be dead")
- False condition: "Do you agree that what [speaker] said is false?"
- Rejection condition: "Would you respond by saying 'No, ...'?"

## Key Finding: The Difference Observation

When presented with **Modal**, ordinary speakers are strongly inclined to
reject Smith's assertion (M = 5.03) but are also strongly inclined to
*disagree* that what Smith said is false (M = 2.42). This dissociation
is absent in **Control**, where rejection and falsity ratings are similar.

## Reference

Khoo, J. (2015). Modal Disagreements. *Inquiry*, 58(5), 511-534.
-/

namespace Phenomena.Modality.Studies.Khoo2015

open Phenomena
open DynamicSemantics.NeoStalnakerian

/-- Citation for this study. -/
def citation : String :=
  "Khoo, J. (2015). Modal Disagreements. Inquiry, 58(5), 511-534."

/-- Likert measure (1-7 scale). -/
def likertMeasure : MeasureSpec :=
  { scale := .ordinal, task := .acceptabilityRating, unit := "Likert 1-7" }

/-! ## Experimental Conditions -/

/-- Sentence type: control (non-modal) vs modal (epistemic might). -/
inductive SentenceType where
  | control  -- "Jim is at home right now" (non-modal assertion)
  | modal    -- "Fat Tony might be dead" (epistemic might)
  deriving DecidableEq, BEq, Repr

/-- Response type: falsity judgment vs rejection inclination. -/
inductive ResponseType where
  | false_     -- "Do you agree that what [speaker] said is false?"
  | rejection  -- "Would you respond by saying 'No, ...'?"
  deriving DecidableEq, BEq, Repr

/-- An experimental condition is a sentence × response pair. -/
structure Condition where
  sentence : SentenceType
  response : ResponseType
  deriving DecidableEq, BEq, Repr

/-- Mean Likert rating for each condition. -/
def meanRating : Condition → Float
  | ⟨.control, .false_⟩    => 6.10
  | ⟨.control, .rejection⟩ => 5.60
  | ⟨.modal,   .false_⟩    => 2.42
  | ⟨.modal,   .rejection⟩ => 5.03

/-- Standard deviation for each condition. -/
def sdRating : Condition → Float
  | ⟨.control, .false_⟩    => 1.35
  | ⟨.control, .rejection⟩ => 1.13
  | ⟨.modal,   .false_⟩    => 1.61
  | ⟨.modal,   .rejection⟩ => 1.77

/-! ## The Difference Observation

The crucial finding: for modal sentences, rejection is high but falsity
is low. For control sentences, both are high. -/

/-- Modal rejection is high (above midpoint 4). -/
theorem modal_rejection_high :
    meanRating ⟨.modal, .rejection⟩ > 4.0 := by native_decide

/-- Modal falsity is low (below midpoint 4). -/
theorem modal_falsity_low :
    meanRating ⟨.modal, .false_⟩ < 4.0 := by native_decide

/-- The dissociation: modal rejection exceeds modal falsity. -/
theorem modal_rejection_exceeds_falsity :
    meanRating ⟨.modal, .rejection⟩ > meanRating ⟨.modal, .false_⟩ := by native_decide

/-- Control shows no dissociation: falsity ≥ rejection. -/
theorem control_no_dissociation :
    meanRating ⟨.control, .false_⟩ ≥ meanRating ⟨.control, .rejection⟩ := by native_decide

/-- The rejection–falsity gap is large for modal (> 2 points). -/
theorem modal_gap_large :
    meanRating ⟨.modal, .rejection⟩ - meanRating ⟨.modal, .false_⟩ > 2.0 := by native_decide

/-- The rejection–falsity gap is small for control (< 1 point). -/
theorem control_gap_small :
    meanRating ⟨.control, .false_⟩ - meanRating ⟨.control, .rejection⟩ < 1.0 := by native_decide

/-! ## Bridge to Rudin (2025) NSF

Rudin's NSF predicts this dissociation via `might_truth_acceptance_dissociate`:
the assertor's might-claim can be true (she has p-worlds) while the rejector
is simultaneously licensed to reject (he has no p-worlds). This is because
truth depends on the assertor's information parameter while rejection depends
on the rejector's. -/

/-- The Mobster scenario has the structure predicted by the NSF:
    Smith (assertor) has examined evidence consistent with Fat Tony being dead,
    so his epistemic state contains p-worlds (p = "Fat Tony is dead").
    Beth (rejector) knows Fat Tony is alive, so her epistemic state has no p-worlds.

    The NSF predicts:
    1. Smith's assertion is true (his state is in MI(might-p))
    2. Beth's rejection is licensed (her state is not might-p-compatible)

    This matches Khoo's finding: speakers reject the might-claim without
    judging it false. -/
theorem nsf_predicts_khoo_pattern
    {W : Type*} (p : BProp W) (smith beth : List W)
    (h_smith : smith.any p = true)
    (h_beth : beth.any p = false) :
    MI (mightSimple p) smith ∧ rejectionLicensed (mightSimple p) beth :=
  might_truth_acceptance_dissociate p smith beth h_smith h_beth

end Phenomena.Modality.Studies.Khoo2015
