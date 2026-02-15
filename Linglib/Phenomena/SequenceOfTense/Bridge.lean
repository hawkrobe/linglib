import Linglib.Phenomena.SequenceOfTense.Data
import Linglib.Theories.TruthConditional.Sentence.Tense.SequenceOfTense

/-!
# Sequence of Tense: Bridge Theorems

Connects the empirical data in `Data.lean` (Reichenbach frames for SOT examples)
to the theoretical analysis in `SequenceOfTense.lean` (perspective shifting,
available readings, embedded frames).

## Bridge Structure

1. **Frame verification**: Data frames satisfy the expected tenses via `satisfiesTense`
2. **Constructor matching**: `simultaneousFrame`/`shiftedFrame` reproduce the data frames
3. **SOT parameter**: English (`.relative`) vs Japanese (`.absolute`) reading availability
4. **composeTense derivation**: Past-under-past yields overall past for both readings

## References

- Ogihara, T. (1989/1996). Tense, Attitudes, and Scope. Kluwer.
- Von Stechow, A. (2009). Tenses in compositional semantics.
-/

namespace Phenomena.SequenceOfTense.Bridge

open Core.Reichenbach
open TruthConditional.Sentence.Tense (satisfiesTense SOTParameter)
open TruthConditional.Sentence.Tense.SequenceOfTense
open Phenomena.SequenceOfTense


-- ════════════════════════════════════════════════════════════════
-- § Frame Verification via satisfiesTense
-- ════════════════════════════════════════════════════════════════

/-- The matrix "said" frame satisfies PAST. -/
theorem matrixSaid_is_past :
    satisfiesTense .past matrixSaid = true := by native_decide

/-- The simultaneous embedded frame satisfies PRESENT relative to embedded P
    (R' = P' = E_matrix). -/
theorem simultaneous_satisfies_present :
    satisfiesTense .present embeddedSickSimultaneous = true := by native_decide

/-- The shifted embedded frame satisfies PAST relative to embedded P
    (R' < P' = E_matrix). -/
theorem shifted_satisfies_past :
    satisfiesTense .past embeddedSickShifted = true := by native_decide

/-- The present-under-past frame satisfies PRESENT relative to embedded P. -/
theorem presentUnderPast_satisfies_present :
    satisfiesTense .present embeddedSickPresent = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § Constructor Matching
-- ════════════════════════════════════════════════════════════════

/-- The `simultaneousFrame` constructor reproduces the hand-built
    simultaneous data frame. -/
theorem simultaneousFrame_matches :
    simultaneousFrame matrixSaid (-2) = embeddedSickSimultaneous := by rfl

/-- The `shiftedFrame` constructor reproduces the hand-built
    shifted data frame. -/
theorem shiftedFrame_matches :
    shiftedFrame matrixSaid (-5) (-5) = embeddedSickShifted := by rfl


-- ════════════════════════════════════════════════════════════════
-- § SOT Parameter Bridge
-- ════════════════════════════════════════════════════════════════

/-- English has the simultaneous reading (SOT language). -/
theorem english_simultaneous_available :
    .simultaneous ∈ availableReadings .relative :=
  sot_simultaneous_available

/-- Japanese lacks the simultaneous reading (non-SOT language). -/
theorem japanese_no_simultaneous :
    .simultaneous ∉ availableReadings .absolute :=
  nonSOT_no_simultaneous

/-- Japanese only has the shifted reading. -/
theorem japanese_only_shifted :
    availableReadings .absolute = [.shifted] :=
  nonSOT_only_shifted


-- ════════════════════════════════════════════════════════════════
-- § composeTense Derivation
-- ════════════════════════════════════════════════════════════════

/-- Both readings yield overall past relative to speech time.
    The simultaneous reading's R' = -2 < 0 = S, and the shifted
    reading's R' = -5 < 0 = S. Both are PAST relative to S.
    This matches `composeTense .past .past = .past`. -/
theorem both_readings_overall_past :
    satisfiesTense .past
      { speechTime := (0 : ℤ), perspectiveTime := 0,
        referenceTime := embeddedSickSimultaneous.referenceTime,
        eventTime := embeddedSickSimultaneous.eventTime } = true ∧
    satisfiesTense .past
      { speechTime := (0 : ℤ), perspectiveTime := 0,
        referenceTime := embeddedSickShifted.referenceTime,
        eventTime := embeddedSickShifted.eventTime } = true := by
  constructor <;> native_decide


end Phenomena.SequenceOfTense.Bridge
