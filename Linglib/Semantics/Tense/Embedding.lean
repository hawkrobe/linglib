import Linglib.Semantics.Tense.Pronoun
import Linglib.Semantics.Tense.Reichenbach

/-!
# Embedded tense: frames under attitude verbs
[abusch-1997] [heim-1994-comments] [ogihara-1989]

The frame of a clause embedded under an attitude verb: `embeddedFrame`
re-anchors the embedded perspective time to the matrix event time
(P′ = E_matrix), so embedded tense locates R′ against the attitude
holder's now rather than speech time. `simultaneousFrame` pins R′ to the
matrix event time (the SOT-deletion reading); the shifted reading is
`embeddedFrame` with `R′ < E_matrix` as a hypothesis at use sites.
`EmbeddedTenseReading` and `availableReadings` parameterize the
shifted/simultaneous split by a language's `SOTParameter`, and
`upperLimitConstraint` is [abusch-1997]'s ULC in [heim-1994-comments]'s
presuppositional construal.
-/

open Time

namespace Tense

variable {Time : Type*}

/-! ### Embedded frames -/

/-- The Reichenbach frame of a clause embedded under an attitude verb:
    embedded perspective time P′ = matrix event time E, so the embedded
    tense locates its R′ relative to the attitude holder's now, not
    speech time. `embeddedR` and `embeddedE` are the embedded clause's
    reference and event times, determined by its tense and aspect. -/
def embeddedFrame (matrixFrame : ReichenbachFrame Time)
    (embeddedR embeddedE : Time) : ReichenbachFrame Time where
  speechTime := matrixFrame.speechTime
  perspectiveTime := matrixFrame.eventTime
  referenceTime := embeddedR
  eventTime := embeddedE

/-- The simultaneous reading's frame: embedded R′ = matrix E ("John said
    Mary was sick" — sick at the saying time), so embedded tense is
    PRESENT relative to the embedded perspective
    (`simultaneousFrame_isPresent`). -/
def simultaneousFrame (matrixFrame : ReichenbachFrame Time)
    (embeddedE : Time) : ReichenbachFrame Time :=
  embeddedFrame matrixFrame matrixFrame.eventTime embeddedE

/-- The simultaneous frame satisfies PRESENT (R = P) relative to the
    embedded perspective. -/
theorem simultaneousFrame_isPresent (matrixFrame : ReichenbachFrame Time)
    (embeddedE : Time) :
    (simultaneousFrame matrixFrame embeddedE).isPresent := rfl

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
abbrev upperLimitConstraint [LE Time] (embeddedR matrixE : Time) : Prop :=
  embeddedR ≤ matrixE

/-- The shifted reading satisfies the ULC. -/
theorem shifted_satisfies_ulc [Preorder Time] (embeddedR matrixE : Time)
    (h : embeddedR < matrixE) : upperLimitConstraint embeddedR matrixE :=
  le_of_lt h

/-- The simultaneous reading satisfies the ULC. -/
theorem simultaneous_satisfies_ulc [Preorder Time] (embeddedR matrixE : Time)
    (h : embeddedR = matrixE) : upperLimitConstraint embeddedR matrixE :=
  le_of_eq h

/-! ### Pronoun resolution into frames -/

/-- Assemble the Reichenbach frame a resolved tense pronoun determines:
    R = the pronoun's referent under `g`, with perspective, speech, and
    event times supplied by the embedding context. -/
def TensePronoun.toFrame (tp : TensePronoun)
    (g : TemporalAssignment Time)
    (speechTime perspectiveTime eventTime : Time) :
    ReichenbachFrame Time where
  speechTime := speechTime
  perspectiveTime := perspectiveTime
  referenceTime := tp.resolve g
  eventTime := eventTime

/-- A present-constraint bound tense under binding gives R = P — the
    simultaneous reading as pronoun resolution: binding the variable to
    the perspective time yields a PRESENT frame. -/
theorem TensePronoun.bound_present_simultaneous
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (speechTime perspTime eventTime : Time)
    (hBind : tp.resolve g = perspTime)
    (_hPres : tp.constraint = present) :
    (tp.toFrame g speechTime perspTime eventTime).isPresent := by
  simp only [TensePronoun.toFrame, ReichenbachFrame.isPresent]
  exact hBind

/-- Double-access: present-under-past requires the complement to hold at
    BOTH speech time (indexical rigidity) AND matrix event time (attitude
    accessibility). -/
def doubleAccess (p : Time → Prop)
    (speechTime matrixEventTime : Time) : Prop :=
  p speechTime ∧ p matrixEventTime

end Tense
