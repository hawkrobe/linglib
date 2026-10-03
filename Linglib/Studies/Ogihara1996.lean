module

public import Linglib.Semantics.Tense.Embedding
public import Linglib.Semantics.Tense.Pronoun
public import Linglib.Semantics.Tense.Reichenbach
public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Ogihara1996

/-!
# Ogihara (1996): Tense, Attitudes, and Scope

This file formalizes the ambiguity thesis of [ogihara-1996], developing [ogihara-1989]:
an embedded past tense is ambiguous between a genuine past, contributing temporal
precedence, and a zero tense, a bound variable that receives the matrix event time. The
simultaneous reading is the zero-tense reading (`zeroTense_simultaneous`) and the shifted reading
the genuine-past reading (`genuinePast_shifted`), against
[kratzer-1998], for whom the past is never ambiguous and the simultaneous reading arises
from deletion at logical form, and [klecha-2016], for whom it arises from the composition
of modal base and tense. Japanese is a pure relative-tense language, every tense being
interpreted in the scope of the structurally higher tenses, so an embedded past is anterior
to the matrix event and *Taroo-wa Hanako-ga byookidat-ta to it-ta* has only the shifted
reading (`embeddedByookiDatta`, `byookiDatta_shifted`), a reading of a language without the
Sequence of Tense rule (`byookiDatta_mem`), the simultaneous reading requiring
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

@[expose] public section

namespace Ogihara1996

open Tense Semantics

/-- The frame of a clause embedded under an attitude verb takes the matrix event time as its
perspective time, so the embedded tense locates its reference time against the attitude holder's
now. -/
@[simps] def embeddedFrame {T : Type*} (matrixFrame : ReichenbachFrame T)
    (embeddedR embeddedE : T) : ReichenbachFrame T :=
  ⟨matrixFrame.speechTime, matrixFrame.eventTime, embeddedR, embeddedE⟩

/-- The simultaneous reading is the zero-tense reading: a zero tense bound by the attitude
receives its now, so it coincides with it. -/
theorem zeroTense_simultaneous {T : Type*} [LinearOrder T] (g : TemporalAssignment T) (n : ℕ)
    (now : T) : compare (interpTense n (updateTemporal g n now)) now = .eq := by
  rw [zeroTense_receives_binder_time, compare_eq_iff_eq]

/-- The shifted reading is the genuine-past reading: a pronoun under the past cell whose
presupposition holds precedes its evaluation time. -/
theorem genuinePast_shifted {T : Type*} [LinearOrder T] (tp : TensePronoun)
    (hc : tp.constraint = ⟦past⟧) (g : TemporalAssignment T) (h : tp.fullPresupposition g) :
    compare (tp.resolve g) (tp.evalTime g) = .lt := by
  simpa [TensePronoun.fullPresupposition, hc, compare_lt_iff_lt] using h

/-- The matrix frame *Taroo-wa … to it-ta*, past and perfective: the speech and perspective
times at the origin, the reference and event times two units earlier. -/
def matrixItta : ReichenbachFrame ℤ := .root 0 (-2) (-2)

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
theorem byookiDatta_shifted : embeddedByookiDatta.referencePosition = .lt := by decide

/-- The Japanese past under a past takes a position open to a language without the Sequence of
Tense rule. -/
theorem byookiDatta_mem : embeddedByookiDatta.referencePosition ∈ pastUnderPast False := by
  decide

/-- The past perfect is perfect: its event precedes its reference time. -/
theorem pluperfect_is_perfect : pluperfectShifted.eventPosition = .lt := by decide

/-- The past perfect is past relative to the embedded perspective. -/
theorem pluperfect_is_past : pluperfectShifted.referencePosition = .lt := by decide

end Ogihara1996
