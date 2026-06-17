import Linglib.Semantics.Tense.GramTense
import Linglib.Semantics.Tense.Reichenbach

/-!
# Tense Theory Infrastructure: Shared Types
[abusch-1997] [heim-1994-comments] [ogihara-1989] [partee-1973]

Shared embedding infrastructure for the tense theories: embedded
Reichenbach frames, the shifted/simultaneous reading split, the upper
limit constraint, and the projections connecting `TensePronoun` to the
SOT frame constructors.

## Main declarations

- `embeddedFrame`: the frame of a clause embedded under an attitude verb
  (P' = matrix E); `simultaneousFrame` and `shiftedFrame` specialize it
- `EmbeddedTenseReading`, `availableReadings`: the SOT-parameterized
  shifted/simultaneous split
- `upperLimitConstraint`: [abusch-1997]'s ULC, presuppositional construal
- `AttitudeTemporalSemantics`: how an attitude verb shifts eval time
-/

open Time

namespace Tense

/-! ### AttitudeTemporalSemantics -/

/-- How an attitude verb shifts the evaluation time for its complement.

    All six theories agree that attitude verbs modify the temporal
    evaluation context of their complement. They differ in the
    formal mechanism (eval time shift, feature checking, deletion,
    binding). This structure captures the shared interface. -/
structure AttitudeTemporalSemantics (Time : Type*) where
  /-- Given a matrix Reichenbach frame, compute the eval time for
      the embedded clause. Typically = matrix event time. -/
  shiftEvalTime : ReichenbachFrame Time → Time
  /-- The temporal constraint imposed on the embedded clause:
      embeddedRefTime must stand in this relation to the shifted eval time. -/
  embeddedConstraint : Time → Time → Prop

/-- The two available readings for embedded past under past.

    When past tense appears in the complement of a past-tense attitude verb,
    the embedded past can be interpreted as:
    - **shifted**: the embedded event occurred BEFORE the matrix event
      (R' < P' = E_matrix)
    - **simultaneous**: the embedded event occurred AT the matrix event time
      (R' = P' = E_matrix), via SOT deletion ([ogihara-1989], §11.2 (83)) -/
inductive EmbeddedTenseReading where
  | shifted       -- embedded event BEFORE matrix event (back-shifted)
  | simultaneous  -- embedded event AT matrix event time (SOT deletion)
  deriving DecidableEq, Repr, Inhabited


/-- Standard eval time shift: embedded eval time = matrix event time.
    This is the default across all six theories. -/
def standardShift {Time : Type*} : AttitudeTemporalSemantics Time where
  shiftEvalTime := λ f => f.eventTime
  embeddedConstraint := λ _embR _evalT => True


/-! ### Embedded Frames -/

/-- Construct the Reichenbach frame for an embedded clause under an attitude verb.

    The key operation: embedded perspective time P' = matrix event time E.
    The embedded clause's tense locates its R' relative to P' = E_matrix,
    not relative to S (speech time).

    `embeddedR` and `embeddedE` are the embedded clause's reference and event
    times, determined by its tense and aspect. -/
def embeddedFrame {Time : Type*} (matrixFrame : ReichenbachFrame Time)
    (embeddedR embeddedE : Time) : ReichenbachFrame Time where
  speechTime := matrixFrame.speechTime
  perspectiveTime := matrixFrame.eventTime  -- KEY: P' = E_matrix
  referenceTime := embeddedR
  eventTime := embeddedE


/-! ### Embedded Tense Readings -/

/-- Available readings depend on the SOT parameter of the language.

    SOT languages (English): both shifted and simultaneous readings.
    Non-SOT languages (Japanese): only shifted (absolute tense). -/
def availableReadings (param : SOTParameter) : List EmbeddedTenseReading :=
  match param with
  | .relative => [.shifted, .simultaneous]
  | .absolute => [.shifted]


/-! ### Reading-Specific Frames -/

/-- The simultaneous reading: embedded R = matrix E.

    "John said Mary was sick" (she was sick AT THE TIME of saying).
    The embedded reference time equals the matrix event time,
    so embedded tense = PRESENT relative to embedded P.
    `embeddedFrame` with R' = E_matrix. -/
def simultaneousFrame {Time : Type*} (matrixFrame : ReichenbachFrame Time)
    (embeddedE : Time) : ReichenbachFrame Time :=
  embeddedFrame matrixFrame matrixFrame.eventTime embeddedE

/-- The shifted reading: embedded R < matrix E.

    "John said Mary had been sick" (she was sick BEFORE the saying).
    The embedded reference time precedes the matrix event time,
    so embedded tense = PAST relative to embedded P.
    Definitionally `embeddedFrame`; the inequality R' < E_matrix is a
    hypothesis at use sites, not enforced by the constructor. -/
def shiftedFrame {Time : Type*} (matrixFrame : ReichenbachFrame Time)
    (embeddedR embeddedE : Time) : ReichenbachFrame Time :=
  embeddedFrame matrixFrame embeddedR embeddedE


/-! ### Perspective Shift Derivations -/

/-- In a past-under-past configuration with the shifted reading,
    the embedded reference time is past relative to speech time.

    Derivation: R' < E_matrix ≤ R_matrix < P_matrix = S
    Therefore R' < S, which is PAST relative to speech time. -/
theorem past_under_past_shifted_is_past {Time : Type*} [LinearOrder Time]
    (S P R E : Time)
    (R' : Time)
    (h_root : P = S)
    (h_matrix_past : R < P)
    (h_perfective : E ≤ R)
    (h_shifted : R' < E) :
    R' < S := by
  calc R' < E := h_shifted
    _ ≤ R := h_perfective
    _ < P := h_matrix_past
    _ = S := h_root

/-- In a past-under-past configuration with the simultaneous reading,
    the embedded reference time is still past relative to speech time.

    Derivation: R' = E_matrix ≤ R_matrix < P_matrix = S
    Therefore R' < S. -/
theorem past_under_past_simultaneous_is_past {Time : Type*} [LinearOrder Time]
    (S P R E : Time)
    (R' : Time)
    (h_root : P = S)
    (h_matrix_past : R < P)
    (h_perfective : E ≤ R)
    (h_simultaneous : R' = E) :
    R' < S := by
  calc R' = E := h_simultaneous
    _ ≤ R := h_perfective
    _ < P := h_matrix_past
    _ = S := h_root

/-- The simultaneous frame satisfies PRESENT (R = P) relative to embedded P. -/
theorem simultaneousFrame_isPresent {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time) :
    (simultaneousFrame matrixFrame embeddedE).isPresent := rfl


/-! ### Available Readings Theorems -/

/-- In SOT languages, the simultaneous reading is available. -/
theorem sot_simultaneous_available :
    .simultaneous ∈ availableReadings .relative := by
  simp [availableReadings]

/-- In SOT languages, the shifted reading is available. -/
theorem sot_shifted_available :
    .shifted ∈ availableReadings .relative := by
  simp [availableReadings]

/-- In non-SOT languages, only the shifted reading is available. -/
theorem nonSOT_only_shifted :
    availableReadings .absolute = [.shifted] := by
  rfl

/-- Non-SOT languages do not have the simultaneous reading. -/
theorem nonSOT_no_simultaneous :
    .simultaneous ∉ availableReadings .absolute := by
  simp [availableReadings]


/-!
### Upper Limit Constraint ([abusch-1997])

The Upper Limit Constraint is stated by [abusch-1997] §7
(p. 25): "the now of an epistemic alternative is an upper limit for
the denotation of tenses". The motivation is branching futures: at
the now of an intensional context, future branches diverge across
epistemic alternatives, so forward reference past the now is
unsupported. The presuppositional construal — ULC as a constraint on
definedness of semantic values, projecting via Karttunen-Heim — is
due to [heim-1994-comments]; [abusch-1997] fn 20 endorses
this construal.

ULC: embedded R' ≤ matrix E (= embedded P).

**Note on faithfulness:** the value-level reduction `embeddedR ≤ matrixE`
strips the modal-alternative quantification Abusch's formulation
carries (the "now of an epistemic alternative" quantifies over
doxastic alternatives). A modal-layer formulation (over `HistoricalAlternatives
W Time`, à la [klecha-2016]'s `actualHistoryBase`) would be more
faithful to the original; deferred future work.
-/

/-- The Upper Limit Constraint.

    Stated by [abusch-1997] §7 ("the now of an epistemic
    alternative is an upper limit for the denotation of tenses");
    presuppositional construal due to [heim-1994-comments],
    endorsed by Abusch 1997 fn 20. The current value-level reduction is
    `embeddedR ≤ matrixE` against bare `[LE Time]`. -/
abbrev upperLimitConstraint {Time : Type*} [LE Time]
    (embeddedR : Time) (matrixE : Time) : Prop :=
  embeddedR ≤ matrixE

/-- The ULC blocks the forward-shifted reading.
    If embedded R' must satisfy R' ≤ E_matrix (ULC) AND R' > E_matrix
    (forward shift), contradiction. -/
theorem ulc_blocks_forward_shift {Time : Type*} [LinearOrder Time]
    (embeddedR matrixE : Time)
    (h_ulc : upperLimitConstraint embeddedR matrixE)
    (h_forward : embeddedR > matrixE) : False :=
  not_lt.mpr h_ulc h_forward

/-- Shifted reading satisfies ULC: R' < E_matrix → R' ≤ E_matrix. -/
theorem shifted_satisfies_ulc {Time : Type*} [Preorder Time]
    (embeddedR matrixE : Time) (h : embeddedR < matrixE) :
    upperLimitConstraint embeddedR matrixE :=
  le_of_lt h

/-- Simultaneous reading satisfies ULC: R' = E_matrix → R' ≤ E_matrix. -/
theorem simultaneous_satisfies_ulc {Time : Type*} [Preorder Time]
    (embeddedR matrixE : Time) (h : embeddedR = matrixE) :
    upperLimitConstraint embeddedR matrixE :=
  le_of_eq h


/-!
### TensePronoun Projections onto SOT Frames

The `TensePronoun` type in `Tense` unifies the five views of tense.
The following theorems show that `simultaneousFrame` and `shiftedFrame`
are projections of specific tense pronouns — a bound present pronoun gives
the simultaneous reading; a free past pronoun gives the shifted reading.
-/

/-- The simultaneous reading = bound present tense pronoun.
    A present-constraint tense pronoun whose variable resolves to P
    (the matrix event time) produces a simultaneousFrame. -/
theorem simultaneousFrame_from_tense_pronoun {Time : Type*}
    (matrixFrame : ReichenbachFrame Time)
    (g : TemporalAssignment Time) (n : ℕ) (embeddedE : Time)
    (tp : TensePronoun)
    (hIdx : tp.varIndex = n)
    (_hPres : tp.constraint = .present)
    (hResolve : interpTense n g = matrixFrame.eventTime) :
    tp.toFrame g matrixFrame.speechTime matrixFrame.eventTime embeddedE =
    simultaneousFrame matrixFrame embeddedE := by
  simp [TensePronoun.toFrame, TensePronoun.resolve, simultaneousFrame, embeddedFrame,
        hIdx, hResolve]

/-- The shifted reading = free past tense pronoun.
    A past-constraint tense pronoun whose variable resolves to some R' < P
    produces a shiftedFrame. -/
theorem shiftedFrame_from_tense_pronoun {Time : Type*}
    (matrixFrame : ReichenbachFrame Time)
    (g : TemporalAssignment Time) (n : ℕ)
    (embeddedR embeddedE : Time)
    (tp : TensePronoun)
    (hIdx : tp.varIndex = n)
    (_hPast : tp.constraint = .past)
    (hResolve : interpTense n g = embeddedR) :
    tp.toFrame g matrixFrame.speechTime matrixFrame.eventTime embeddedE =
    shiftedFrame matrixFrame embeddedR embeddedE := by
  simp [TensePronoun.toFrame, TensePronoun.resolve, shiftedFrame, embeddedFrame,
        hIdx, hResolve]

/-- Double-access: present-under-past requires the complement
    to hold at BOTH speech time AND matrix event time.

    This bridges the `doubleAccess` definition from `Tense` to the
    SOT analysis: the present-under-past frame's R = P (simultaneous),
    and the speech time is independently accessible via indexical rigidity. -/
theorem doubleAccess_present_under_past {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (_embeddedE : Time)
    (p : Time → Prop)
    (h_simul : p matrixFrame.eventTime)
    (h_speech : p matrixFrame.speechTime) :
    doubleAccess p matrixFrame.speechTime matrixFrame.eventTime :=
  ⟨h_speech, h_simul⟩

/-- Ogihara's synthesis: bound tense (zero tense) + attitude binding =
    simultaneous reading. The zero tense variable receives the matrix event
    time via lambda abstraction; the Reichenbach frame has R = P. -/
theorem bound_tense_simultaneous {Time : Type*} [LinearOrder Time]
    (g : TemporalAssignment Time) (n : ℕ)
    (matrixFrame : ReichenbachFrame Time) :
    interpTense n (updateTemporal g n matrixFrame.eventTime) = matrixFrame.eventTime ∧
    (simultaneousFrame matrixFrame matrixFrame.eventTime).isPresent :=
  ⟨zeroTense_receives_binder_time g n matrixFrame.eventTime, rfl⟩


/-! ### ThenAdverb -/

/-- A "then"-type temporal adverb.
    Cross-linguistically, "then" shifts the perspective time P away
    from the speech time S ([zhao-2025], [tsilia-zhao-2026]). -/
structure ThenAdverb where
  /-- Language name -/
  language : String
  /-- Surface form -/
  form : String
  /-- English gloss -/
  gloss : String
  /-- "then" shifts P away from S: P ≠ S after "then" applies. -/
  shiftsPerspective : Bool
  deriving Repr, DecidableEq


end Tense
