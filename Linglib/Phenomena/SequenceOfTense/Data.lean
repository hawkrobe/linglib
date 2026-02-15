import Linglib.Core.Reichenbach
import Linglib.Core.Time

/-!
# Sequence of Tense: Empirical Data

Pure empirical data for sequence-of-tense phenomena: Reichenbach frames
encoding the temporal structure of attested SOT examples.

No theoretical commitments — these are just temporal facts about sentences.
Bridge theorems connecting this data to the SOT analysis are in `Bridge.lean`.

## English SOT (SOTParameter = .relative)

1. "John said that Mary was sick" — SIMULTANEOUS reading
   Mary's being sick overlaps with John's saying.
   Matrix: Past(say), Embedded: Past(sick).
   Reading: sick-time = say-time.

2. "John said that Mary was sick" — SHIFTED reading
   Mary's being sick precedes John's saying.
   Matrix: Past(say), Embedded: Past(sick).
   Reading: sick-time < say-time.

3. "John said that Mary is sick" — PRESENT under PAST
   Mary's being sick holds at speech time (double-access reading).
   Matrix: Past(say), Embedded: Pres(sick).

## Japanese non-SOT (SOTParameter = .absolute)

4. "Taroo-wa Mary-ga byooki-da to itta" — Present under Past
   "Taro said that Mary is sick."
   Embedded present = absolute present (at speech time).

5. "Taroo-wa Mary-ga byooki-datta to itta" — Past under Past
   "Taro said that Mary was sick (before the saying)."
   Only shifted reading (no simultaneous reading in Japanese).

## References

- Ogihara, T. (1989/1996). Tense, Attitudes, and Scope. Kluwer.
- Von Stechow, A. (2009). Tenses in compositional semantics.
- Kusumoto, K. (2005). On the quantification over times in natural language.
-/

namespace Phenomena.SequenceOfTense

open Core.Reichenbach


-- ════════════════════════════════════════════════════════════════
-- § Concrete Frames (ℤ times, S = 0)
-- ════════════════════════════════════════════════════════════════

/-- Matrix frame for "John said ..." (past tense, perfective).
    Speech time S = 0, saying event at t = -2. -/
def matrixSaid : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- root clause: P = S
  referenceTime := -2     -- PAST: R < P
  eventTime := -2         -- perfective: E = R

/-- Embedded frame for "Mary was sick" — SIMULTANEOUS reading.
    Embedded P = matrix E = -2, R' = E_matrix = -2.
    Mary is sick at the time of the saying. -/
def embeddedSickSimultaneous : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -2     -- simultaneous: R' = E_matrix
  eventTime := -2         -- sick-time = say-time

/-- Embedded frame for "Mary was sick" — SHIFTED reading.
    Embedded P = matrix E = -2, R' = -5 < E_matrix.
    Mary was sick before the saying. -/
def embeddedSickShifted : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -5     -- shifted: R' < E_matrix
  eventTime := -5         -- sick-time before say-time

/-- Embedded frame for "Mary is sick" — PRESENT under PAST.
    Embedded present in SOT language: R' = P' = E_matrix.
    Double-access reading: Mary is sick now (at speech time) AND
    the sickness is relevant at the time of saying. -/
def embeddedSickPresent : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -2     -- R' = P' (present relative to matrix)
  eventTime := 0          -- sick at speech time (double-access)

/-- Japanese matrix frame: "Taroo-ga ... to itta" (Taro said ...).
    Same temporal structure as English matrix. -/
def matrixItta : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2
  eventTime := -2

/-- Japanese embedded: "Mary-ga byooki-datta" (Mary was sick) — absolute past.
    In non-SOT Japanese, embedded past is absolute (relative to S, not E).
    Only the shifted reading: sick-time < say-time. -/
def embeddedByookiDatta : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- non-SOT: P = S (absolute, not shifted)
  referenceTime := -5     -- PAST relative to S: R < S
  eventTime := -5


-- ════════════════════════════════════════════════════════════════
-- § Theory-Neutral Temporal Facts
-- ════════════════════════════════════════════════════════════════

/-- The matrix "said" is past: R < P. -/
theorem matrixSaid_R_lt_P :
    matrixSaid.referenceTime < matrixSaid.perspectiveTime := by native_decide

/-- The matrix frame is a root clause: P = S. -/
theorem matrixSaid_root :
    matrixSaid.perspectiveTime = matrixSaid.speechTime := by native_decide

/-- Simultaneous reading: embedded R = matrix E. -/
theorem simultaneous_R_eq_matrix_E :
    embeddedSickSimultaneous.referenceTime = matrixSaid.eventTime := by native_decide

/-- Shifted reading: embedded R < matrix E. -/
theorem shifted_R_lt_matrix_E :
    embeddedSickShifted.referenceTime < matrixSaid.eventTime := by native_decide

/-- Simultaneous: sick-time = say-time. -/
theorem simultaneous_sick_at_say_time :
    embeddedSickSimultaneous.eventTime = matrixSaid.eventTime := by native_decide

/-- Shifted: sick-time < say-time. -/
theorem shifted_sick_before_say :
    embeddedSickShifted.eventTime < matrixSaid.eventTime := by native_decide

/-- Japanese: embedded P = S (absolute, not shifted to matrix E). -/
theorem japanese_absolute_perspective :
    embeddedByookiDatta.perspectiveTime = embeddedByookiDatta.speechTime := by native_decide

/-- English simultaneous: embedded P = matrix E (perspective shifted). -/
theorem english_simultaneous_perspective_shifted :
    embeddedSickSimultaneous.perspectiveTime = matrixSaid.eventTime := by native_decide

/-- English shifted: embedded P = matrix E (perspective shifted). -/
theorem english_shifted_perspective_shifted :
    embeddedSickShifted.perspectiveTime = matrixSaid.eventTime := by native_decide


/-- Hypothetical forward-shifted frame (for gap demonstration).
    If past-under-past allowed forward shift, R' > E_matrix.
    This frame is PREDICTED NOT TO EXIST as a reading. -/
def embeddedSickForwardShifted : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -1     -- R' = -1 > E_matrix = -2 (forward shifted!)
  eventTime := -1         -- sick AFTER the saying

/-- Forward-shifted: R' > matrix E (theory-neutral temporal fact). -/
theorem forwardShifted_R_gt_matrix_E :
    embeddedSickForwardShifted.referenceTime > matrixSaid.eventTime := by native_decide

/-- Double access reading (Abusch 1997): present-under-past requires
    overlap with BOTH matrix event time AND speech time.
    Our frame: E' = 0 = S (sick at speech time), P' = -2 = E_matrix. -/
theorem double_access_overlaps_speech :
    embeddedSickPresent.eventTime = embeddedSickPresent.speechTime := by native_decide


end Phenomena.SequenceOfTense
