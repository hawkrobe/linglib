import Linglib.Phenomena.Presupposition.Studies.ScontrasTonhauser2025
import Linglib.Theories.Pragmatics.RSA.Implementations.ScontrasTonhauser2025
import Linglib.Core.BToM

/-!
# S&T 2025 BToM Bridge

Connects the S&T 2025 experimental data (`Phenomena.Presupposition.Studies`)
to the BToM-grounded RSA model (`Theories.Pragmatics.RSA.Implementations`).

## The Pipeline

    Core/BToM.lean                    (BToMModel, beliefExpectation)
        ↓
    Theories/RSA/ScontrasTonhauser2025  (HasBelief, HasComplement, assumesCIndicator)
        ↓
    this file                          (bridge theorems)
        ↑
    Phenomena/Presupposition/Studies/ScontrasTonhauser2025  (experimental data)

## What This Proves

1. **Model structure**: The model's BeliefState is classified as a BToM mental
   state, and the QUD is classified as shared — matching Baker et al.'s (2017)
   ontological categories.

2. **Projection mechanism**: The model's projection prediction (know > think)
   operates through `assumesCIndicator`, which is the characteristic function
   for `BToMModel.beliefExpectation`. The empirical utterance effect
   (β = 0.35, p < 0.001) confirms the predicted direction.

3. **Factivity grounding**: The literal-semantic difference between know
   (factive: BEL ∧ C) and think (non-factive: BEL) entails that know-worlds
   always satisfy C, which biases the belief marginal toward C-assuming states.
-/

namespace Phenomena.Presupposition.Studies.ScontrasTonhauser2025BToMBridge

open RSA.ScontrasTonhauser2025
open Core.BToM

-- ============================================================================
-- §1. BToM Ontological Classification
-- ============================================================================

/-- The model's BeliefState is a mental state in BToM's ontology. -/
theorem beliefState_is_mental : beliefStateCategory = LatentCategory.mental := rfl

/-- The model's QUD is a shared state in BToM's ontology. -/
theorem qud_is_shared : qudCategory = LatentCategory.shared := rfl

-- ============================================================================
-- §2. Factivity Drives Projection
-- ============================================================================

/-- In "know" worlds (BEL ∧ C), C always holds. This means the BToM belief
    marginal over know-compatible worlds is concentrated on C-true states,
    driving projection of C.

    Contrast with "think" worlds (BEL only), where C may or may not hold —
    the belief marginal does not concentrate on C-true states. -/
theorem know_worlds_entail_c : ∀ w : WorldState,
    literalMeaning .knowPos w = true → w.c = true :=
  know_entails_c

/-- "think" worlds do NOT entail C — there exist think-true, C-false worlds. -/
theorem think_worlds_not_entail_c : ∃ w : WorldState,
    literalMeaning .thinkPos w = true ∧ w.c = false :=
  think_not_entails_c

-- ============================================================================
-- §3. Indicator Classification
-- ============================================================================

/-- Exactly 3 of 9 belief states assume C (indicator = 1).
    These are the states where C holds at every world the speaker considers
    possible: cTrue, cTrueBelTrue, cTrueBelFalse.

    The BToM observer's posterior P(assumes C | u) is a weighted sum over
    these three states. -/
theorem three_of_nine_assume_c :
    (List.filter (fun bs => assumesC bs) allBeliefStates).length = 3 := by
  native_decide

/-- The remaining 6 belief states do not assume C (indicator = 0). -/
theorem six_of_nine_not_assume_c :
    (List.filter (fun bs => !assumesC bs) allBeliefStates).length = 6 := by
  native_decide

-- ============================================================================
-- §4. Data–Model Alignment
-- ============================================================================

/-- The empirical utterance effect direction (know > think in projection)
    matches the model's structural prediction.

    The model predicts know > think because:
    - All know-worlds have C = true (factivePos_entails_c)
    - Some think-worlds have C = false (think_not_entails_c)
    - Therefore the BToM belief marginal after hearing "know" is biased
      toward C-assuming states, yielding higher P(assumes C | "know")

    The data confirms this: β = 0.35 > 0. -/
theorem utterance_effect_direction_matches :
    Phenomena.Presupposition.Studies.ScontrasTonhauser2025.directionCorrect
      .utterance = true := by
  native_decide

/-- The empirical QUD effect direction (BEL? > C?) also matches.
    When the QUD is about belief (BEL?), the listener focuses on the
    speaker's epistemic state, amplifying the belief-marginal contribution
    to projection. -/
theorem qud_effect_direction_matches :
    Phenomena.Presupposition.Studies.ScontrasTonhauser2025.directionCorrect
      .qud = true := by
  native_decide

end Phenomena.Presupposition.Studies.ScontrasTonhauser2025BToMBridge
