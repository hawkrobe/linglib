module

public import Linglib.Semantics.Tense.Pronoun
public import Linglib.Semantics.Tense.Reichenbach

/-!
# Embedded tense: frames under attitude verbs

A clause embedded under an attitude verb is evaluated from the attitude holder's now: its frame
takes the matrix event time as its perspective time (`embeddedFrame`), so the embedded tense
locates its reference time against that now rather than the speech time. The simultaneous reading
places the embedded reference time at the matrix event time, so its reference position is `.eq`;
the shifted reading places it earlier. Whether a language allows both readings of a past under a
past is its sequence-of-tense parameter (`SOTParameter`, `availableReadings`). Abusch's Upper
Limit Constraint, in the presuppositional construal Heim gives it, bars the embedded reference
time from following the matrix event time (`upperLimitConstraint`).

## Main definitions

* `Tense.embeddedFrame`: the frame of an embedded clause.
* `Tense.SOTParameter`, `Tense.EmbeddedTenseReading`, `Tense.availableReadings`: the readings of
  a past under a past.
* `Tense.upperLimitConstraint`: the Upper Limit Constraint.
* `Tense.DoubleAccess`: the double access reading of a present under a past.

## References

* [abusch-1997]
* [heim-1994-comments]
* [ogihara-1989]
-/

@[expose] public section

open Tense

namespace Tense

open Semantics

variable {T : Type*}

/-! ### Embedded frames -/

/-- The Reichenbach frame of a clause embedded under an attitude verb:
    embedded perspective time P′ = matrix event time E, so the embedded
    tense locates its R′ relative to the attitude holder's now, not
    speech time. `embeddedR` and `embeddedE` are the embedded clause's
    reference and event times, determined by its tense and aspect. -/
@[simps] def embeddedFrame (matrixFrame : ReichenbachFrame T)
    (embeddedR embeddedE : T) : ReichenbachFrame T where
  speechTime := matrixFrame.speechTime
  perspectiveTime := matrixFrame.eventTime
  referenceTime := embeddedR
  eventTime := embeddedE

/-! ### Embedded tense readings -/

/-- Sequence-of-tense parameter: whether embedded tense is interpreted
    relative to the matrix (SOT languages, English) or absolutely, against
    utterance time (non-SOT languages, Japanese). -/
inductive SOTParameter where
  /-- Embedded tense relative to matrix (English). -/
  | relative
  /-- Embedded tense absolute, against utterance time (Japanese). -/
  | absolute
  deriving DecidableEq, Repr

/-- The two readings of past under a past attitude verb: **shifted**
    (embedded event before the matrix event, R′ < P′) or **simultaneous**
    (embedded event at the matrix event time, R′ = P′, via SOT deletion —
    [ogihara-1989] §11.2 (83)). -/
inductive EmbeddedTenseReading where
  /-- Embedded event before the matrix event (back-shifted). -/
  | shifted
  /-- Embedded event at the matrix event time (SOT deletion). -/
  | simultaneous
  deriving DecidableEq, Repr, Inhabited

/-- The readings a language's `SOTParameter` licenses for past-under-past:
    SOT (`relative`, English) languages have both; non-SOT (`absolute`,
    Japanese) languages only the shifted reading. -/
def availableReadings : SOTParameter → List EmbeddedTenseReading
  | .relative => [.shifted, .simultaneous]
  | .absolute => [.shifted]

/-! ### Upper Limit Constraint

[abusch-1997] §7 (p. 25): "the now of an epistemic alternative is an
upper limit for the denotation of tenses" — at the now of an intensional
context, future branches diverge across epistemic alternatives, so
forward reference past the now is unsupported. The presuppositional
construal (ULC as a definedness constraint, projecting via
Karttunen-Heim) is due to [heim-1994-comments]; [abusch-1997] fn 20
endorses it. The value-level reduction `embeddedR ≤ matrixE` strips the
modal-alternative quantification of Abusch's formulation (the "now of an
epistemic alternative" quantifies over doxastic alternatives); a
modal-layer formulation would be more faithful. -/

/-- The Upper Limit Constraint ([abusch-1997] §7, presuppositional
    construal per [heim-1994-comments]): the embedded reference time may
    not exceed the matrix event time (= the embedded perspective). -/
abbrev upperLimitConstraint [LE T] (embeddedR matrixE : T) : Prop :=
  embeddedR ≤ matrixE

/-- The shifted reading satisfies the ULC. -/
theorem shifted_satisfies_ulc [Preorder T] (embeddedR matrixE : T)
    (h : embeddedR < matrixE) : upperLimitConstraint embeddedR matrixE :=
  le_of_lt h

/-- The simultaneous reading satisfies the ULC. -/
theorem simultaneous_satisfies_ulc [Preorder T] (embeddedR matrixE : T)
    (h : embeddedR = matrixE) : upperLimitConstraint embeddedR matrixE :=
  le_of_eq h

/-- The double access reading of a present tense under a past attitude: the denotation of the
present tense overlaps both the believing time and the utterance time. A condition on the
tense's reference, not on the truth of the complement at either time. -/
def DoubleAccess (I : Set T) (believing utterance : T) : Prop :=
  believing ∈ I ∧ utterance ∈ I

end Tense
