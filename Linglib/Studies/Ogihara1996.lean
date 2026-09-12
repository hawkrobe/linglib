import Linglib.Semantics.Tense.Embedding
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.Ogihara1996

/-!
# Ogihara (1996): Tense, Attitudes, and Scope

This file formalizes the ambiguity thesis of [ogihara-1996], developing [ogihara-1989]:
an embedded past tense is ambiguous between a genuine past, contributing temporal
precedence, and a zero tense, a bound variable that receives the matrix event time. The
simultaneous reading is the zero-tense reading (`ogihara_derives_simultaneous`) and the
shifted reading the genuine-past reading (`ogihara_derives_shifted`), against
[kratzer-1998], for whom the past is never ambiguous and the simultaneous reading arises
from deletion at logical form, and [klecha-2016], for whom it arises from the composition
of modal base and tense. Japanese is a pure relative-tense language, every tense being
interpreted in the scope of the structurally higher tenses, so an embedded past is anterior
to the matrix event and *Taroo-wa Hanako-ga byookidat-ta to it-ta* has only the shifted
reading (`embeddedByookiDatta`, `byookiDatta_shifted`), the simultaneous reading requiring
the embedded present; the English past perfect under a past matrix is built against the
same matrix frame (`pluperfectShifted`, `pluperfect_is_past`).

## Implementation notes

The frames are Reichenbach frames over the integers, with the embedded perspective time
set to the matrix event time. The Japanese example with an embedded present under a past
matrix, whose simultaneous reading places the event at the matrix event time while the
morphology says present, is not encoded, since a single reference and event time cannot
carry both the morphological tense and the divergent event location.

## References

* [ogihara-1996]
* [ogihara-1989]
* [kratzer-1998]
* [klecha-2016]
-/

namespace Ogihara1996

open Tense

/-- The two readings of embedded past morphology: a genuine past, contributing temporal
precedence, and a zero tense, a bound variable with no temporal content of its own. -/
inductive PastReading where
  | genuinePast
  | zeroTense
  deriving DecidableEq

/-- [ogihara-1996] derives the simultaneous reading via the zero
    tense reading of past: the bound variable receives `E_matrix`. The
    derivation chain is `zeroTense_receives_binder_time` (substrate) →
    `embeddedR = matrixFrame.eventTime` → `embeddedFrame.isPresent`. -/
theorem ogihara_derives_simultaneous {T : Type*}
    (matrixFrame : ReichenbachFrame T) (g : TemporalAssignment T) (n : ℕ) :
    let embeddedR := interpTense n (updateTemporal g n matrixFrame.eventTime)
    (embeddedFrame matrixFrame embeddedR embeddedR).isPresent := by
  simp only [zeroTense_receives_binder_time, embeddedFrame,
    ReichenbachFrame.isPresent]

/-- [ogihara-1996] derives the shifted reading via the
    genuine-past reading: the past tense contributes temporal
    precedence. -/
theorem ogihara_derives_shifted {T : Type*} [LinearOrder T]
    (matrixFrame : ReichenbachFrame T) (embeddedR embeddedE : T)
    (hPast : embeddedR < matrixFrame.eventTime) :
    (embeddedFrame matrixFrame embeddedR embeddedE).isPast := by
  simp only [embeddedFrame, ReichenbachFrame.isPast_def]
  exact hPast

/-- The matrix frame *Taroo-wa … to it-ta*, past and perfective: the speech and perspective
times at the origin, the reference and event times two units earlier. -/
def matrixItta : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2
  eventTime := -2

/-- The embedded *Hanako-ga byookidat-ta*: a past under a past, interpreted relative to the
matrix event, so its perspective time is the matrix event time and its reference time lies
before it. -/
def embeddedByookiDatta : ReichenbachFrame ℤ := embeddedFrame matrixItta (-5) (-5)

/-- The English past perfect under a past matrix, *he said that Mary had been reading books
yesterday*: past relative to the embedded perspective, and perfect. -/
def pluperfectShifted : ReichenbachFrame ℤ := embeddedFrame matrixItta (-4) (-5)

/-- The embedded Japanese past is evaluated from the matrix event, not the speech time. -/
theorem japanese_relative_perspective :
    embeddedByookiDatta.perspectiveTime = matrixItta.eventTime := rfl

/-- The embedded Japanese past has only the shifted reading. -/
theorem byookiDatta_shifted : embeddedByookiDatta.isPast := by
  simp only [ReichenbachFrame.isPast_def, embeddedByookiDatta, embeddedFrame, matrixItta]; omega

/-- The past perfect is perfect: its event precedes its reference time. -/
theorem pluperfect_is_perfect : pluperfectShifted.isPerfect := by
  simp only [ReichenbachFrame.isPerfect, pluperfectShifted, embeddedFrame, matrixItta]; omega

/-- The past perfect is past relative to the embedded perspective. -/
theorem pluperfect_is_past : pluperfectShifted.isPast := by
  simp only [ReichenbachFrame.isPast_def, pluperfectShifted, embeddedFrame, matrixItta]; omega

end Ogihara1996
