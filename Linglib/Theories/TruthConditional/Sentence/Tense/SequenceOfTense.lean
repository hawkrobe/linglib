import Linglib.Theories.TruthConditional.Sentence.Tense.Basic
import Linglib.Theories.IntensionalSemantics.Attitude.SituationDependent

/-!
# Sequence of Tense

Connects tense operators to attitude embedding: when a tense appears in the
complement of an attitude verb, its perspective time shifts from speech time
to the matrix event time.

## Core Mechanism (Von Stechow 2009)

In root clauses, tense locates R relative to P = S (speech time).
Under attitude embedding, P shifts to the matrix event time E:
  - **Embedded P = Matrix E**: the embedded tense is relative to the
    matrix event, not the utterance

This yields two readings for past-under-past ("John said Mary was sick"):
  1. **Shifted**: embedded event BEFORE matrix event (R' < E_matrix)
  2. **Simultaneous**: embedded event AT matrix event time (R' = E_matrix)
     — available only in SOT languages via "SOT deletion" (Ogihara 1989)

## SOT vs Non-SOT Languages

- **SOT languages** (English, French): Both readings available.
  Past morphology in the embedded clause is ambiguous between shifted
  and simultaneous (SOT deletion applies optionally).

- **Non-SOT languages** (Japanese, Mandarin): Only shifted reading.
  Embedded tense is absolute (relative to S, not E_matrix), so
  embedded past always means "before the saying."

## References

- Reichenbach, H. (1947). Elements of Symbolic Logic.
- Ogihara, T. (1989/1996). Tense, Attitudes, and Scope. Kluwer.
- Abusch, D. (1994/1997). Sequence of Tense Revisited.
- Kratzer, A. (1998). More Structural Analogies Between Pronouns and Tenses.
- Kiparsky, P. (2002). Event structure and the perfect.
- Von Stechow, A. (2009). Tenses in compositional semantics. In Klein & Li (eds.),
  The Expression of Time, 129–166.
-/

namespace TruthConditional.Sentence.Tense.SequenceOfTense

open Core.Reichenbach
open TruthConditional.Sentence.Tense (GramTense SOTParameter composeTense applyTense satisfiesTense)


-- ════════════════════════════════════════════════════════════════
-- § Embedded Frames
-- ════════════════════════════════════════════════════════════════

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


-- ════════════════════════════════════════════════════════════════
-- § Embedded Tense Readings
-- ════════════════════════════════════════════════════════════════

/-- The two available readings for embedded past under past.

    When past tense appears in the complement of a past-tense attitude verb,
    the embedded past can be interpreted as:
    - **shifted**: the embedded event occurred BEFORE the matrix event
      (R' < P' = E_matrix)
    - **simultaneous**: the embedded event occurred AT the matrix event time
      (R' = P' = E_matrix), via SOT deletion (Ogihara 1989, §11.2 (83)) -/
inductive EmbeddedTenseReading where
  | shifted       -- embedded event BEFORE matrix event (back-shifted)
  | simultaneous  -- embedded event AT matrix event time (SOT deletion)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Available readings depend on the SOT parameter of the language.

    SOT languages (English): both shifted and simultaneous readings.
    Non-SOT languages (Japanese): only shifted (absolute tense). -/
def availableReadings (param : SOTParameter) : List EmbeddedTenseReading :=
  match param with
  | .relative => [.shifted, .simultaneous]
  | .absolute => [.shifted]


-- ════════════════════════════════════════════════════════════════
-- § Reading-Specific Frames
-- ════════════════════════════════════════════════════════════════

/-- The simultaneous reading: embedded R = matrix E.

    "John said Mary was sick" (she was sick AT THE TIME of saying).
    The embedded reference time equals the matrix event time,
    so embedded tense = PRESENT relative to embedded P. -/
def simultaneousFrame {Time : Type*} (matrixFrame : ReichenbachFrame Time)
    (embeddedE : Time) : ReichenbachFrame Time where
  speechTime := matrixFrame.speechTime
  perspectiveTime := matrixFrame.eventTime
  referenceTime := matrixFrame.eventTime  -- R' = P' = E_matrix
  eventTime := embeddedE

/-- The shifted reading: embedded R < matrix E.

    "John said Mary had been sick" (she was sick BEFORE the saying).
    The embedded reference time precedes the matrix event time,
    so embedded tense = PAST relative to embedded P. -/
def shiftedFrame {Time : Type*} (matrixFrame : ReichenbachFrame Time)
    (embeddedR embeddedE : Time) : ReichenbachFrame Time where
  speechTime := matrixFrame.speechTime
  perspectiveTime := matrixFrame.eventTime
  referenceTime := embeddedR  -- R' < P' = E_matrix for shifted
  eventTime := embeddedE


-- ════════════════════════════════════════════════════════════════
-- § Bridge: composeTense ↔ Perspective Shifting
-- ════════════════════════════════════════════════════════════════

/-!
### Connecting `composeTense` to the Derived Analysis

The stipulative `composeTense` function in `Tense/Basic.lean` defines how
surface tenses compose: `composeTense .past .past = .past`. The SOT analysis
*derives* this: past-under-past yields a result that is past relative to S
because the embedded R is either at or before the matrix E, which is itself
before S.

The following theorems prove this derivation, connecting the stipulative
function to the Reichenbach analysis with perspective shifting.
-/

/-- In a past-under-past configuration with the shifted reading,
    the embedded reference time is past relative to speech time.

    Derivation: R' < E_matrix ≤ R_matrix < P_matrix = S
    Therefore R' < S, which is PAST relative to speech time.
    This matches `composeTense .past .past = .past`. -/
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
    Therefore R' < S.
    This also matches `composeTense .past .past = .past`. -/
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

/-- Present-under-past with the simultaneous reading: embedded R = matrix E.
    The embedded present "survives" as present relative to the matrix event.

    "John said Mary is sick" — double-access reading in SOT languages.
    The embedded reference time equals the matrix event time. -/
theorem present_under_past_simultaneous {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) :
    (simultaneousFrame matrixFrame matrixFrame.eventTime).referenceTime =
    (simultaneousFrame matrixFrame matrixFrame.eventTime).perspectiveTime := by
  rfl

/-- The simultaneous frame satisfies PRESENT (R = P) relative to embedded P. -/
theorem simultaneousFrame_is_present {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time) :
    (simultaneousFrame matrixFrame embeddedE).isPresent := by
  unfold ReichenbachFrame.isPresent simultaneousFrame
  rfl


-- ════════════════════════════════════════════════════════════════
-- § Bridge: applyTense + embeddedFrame
-- ════════════════════════════════════════════════════════════════

/-- Applying embedded PAST to the embedded frame means R' < E_matrix.

    The shifted reading: the embedded tense really is PAST relative
    to the shifted perspective (matrix event time). -/
theorem embeddedPast_means_before_matrix {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time) :
    applyTense .past (embeddedFrame matrixFrame embeddedR embeddedE) ↔
    embeddedR < matrixFrame.eventTime := by
  simp [applyTense, embeddedFrame]

/-- Applying embedded PRESENT to the embedded frame means R' = E_matrix.

    The simultaneous reading: the embedded tense is PRESENT relative
    to the shifted perspective. -/
theorem embeddedPresent_means_at_matrix {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time) :
    applyTense .present (embeddedFrame matrixFrame embeddedR embeddedE) ↔
    embeddedR = matrixFrame.eventTime := by
  simp [applyTense, embeddedFrame]


-- ════════════════════════════════════════════════════════════════
-- § Available Readings Theorems
-- ════════════════════════════════════════════════════════════════

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


-- ════════════════════════════════════════════════════════════════
-- § Upper Limit Constraint (Abusch 1997)
-- ════════════════════════════════════════════════════════════════

/-!
### Abusch's (1997) Upper Limit Constraint

In intensional contexts, tense reference cannot exceed the local
evaluation time. From branching futures: at the attitude event time,
future branches diverge, so no time beyond the attitude time is
accessible across all doxastic alternatives.

ULC: embedded R' ≤ matrix E (= embedded P).
-/

/-- Abusch's (1997) Upper Limit Constraint.
    In intensional contexts, the tense reference cannot exceed the
    local evaluation time. -/
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


-- ════════════════════════════════════════════════════════════════
-- § Bridge: Attitude Accessibility ↔ Reichenbach (Ogihara 1989)
-- ════════════════════════════════════════════════════════════════

/-!
### Connecting Attitude Accessibility to Reichenbach Frames

The attitude side (`SituationDependent.temporallyBound`) and the tense side
(`simultaneousFrame`) describe the same empirical phenomenon — the simultaneous
reading — using different formal vocabularies. The following theorems prove
their equivalence, completing the missing edge in the dependency graph.

Ogihara (1989): the bound (zero) tense variable receives the matrix event
time via lambda abstraction. The Reichenbach frame has R = P (simultaneous).
The situation-semantic formulation imposes time-equality on accessible
situations. All three descriptions collapse to the same truth condition.
-/

open IntensionalSemantics.Attitude.SituationDependent (temporallyBound)
open Core.Time (Situation)

/-- Temporal binding extracts a time-equality constraint from situation
    accessibility. This is the situation-semantic formulation of "the
    embedded tense receives the matrix event time." -/
theorem temporallyBound_forces_time_eq {W Time E : Type*} [DecidableEq Time]
    (R : Core.ModalLogic.AgentAccessRel W E) (agent : E)
    (s₁ s₂ : Situation W Time)
    (h : temporallyBound R agent s₁ s₂ = true) :
    s₂.time = s₁.time := by
  simp only [temporallyBound, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- The time-equality from temporallyBound corresponds to the Reichenbach
    PRESENT relation (R = P) in the embedded frame — i.e., the simultaneous
    reading.

    This connects the attitude-side formalization (SituationDependent.temporallyBound)
    to the tense-side formalization (SequenceOfTense.simultaneousFrame). -/
theorem temporallyBound_gives_simultaneous {W Time E : Type*} [LinearOrder Time]
    (R : Core.ModalLogic.AgentAccessRel W E) (agent : E)
    (s₁ s₂ : Situation W Time) (speechTime : Time)
    (h : temporallyBound R agent s₁ s₂ = true) :
    let embeddedFrame : ReichenbachFrame Time :=
      { speechTime, perspectiveTime := s₁.time,
        referenceTime := s₂.time, eventTime := s₂.time }
    embeddedFrame.isPresent := by
  simp only [ReichenbachFrame.isPresent]
  exact temporallyBound_forces_time_eq R agent s₁ s₂ h

/-- Conversely, the simultaneousFrame from the Reichenbach analysis satisfies
    the time-equality that temporallyBound imposes. -/
theorem simultaneousFrame_satisfies_time_eq {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time) :
    (simultaneousFrame matrixFrame embeddedE).referenceTime =
    (simultaneousFrame matrixFrame embeddedE).perspectiveTime := by rfl

/-- Ogihara's synthesis: bound tense (zero tense) + attitude binding =
    simultaneous reading. The zero tense variable receives the matrix event
    time via lambda abstraction; the Reichenbach frame has R = P. -/
theorem ogihara_bound_tense_simultaneous {Time : Type*} [LinearOrder Time]
    (g : TemporalAssignment Time) (n : ℕ)
    (matrixFrame : ReichenbachFrame Time) :
    interpTense n (updateTemporal g n matrixFrame.eventTime) = matrixFrame.eventTime ∧
    (simultaneousFrame matrixFrame matrixFrame.eventTime).isPresent :=
  ⟨zeroTense_receives_binder_time g n matrixFrame.eventTime, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § TensePronoun ↔ SOT Frames (Abusch 1997)
-- ════════════════════════════════════════════════════════════════

/-!
### TensePronoun Projections onto SOT Frames

The `TensePronoun` type in `Core.Tense` unifies the five views of tense.
The following theorems show that `simultaneousFrame` and `shiftedFrame`
are projections of specific tense pronouns — a bound present pronoun gives
the simultaneous reading; a free past pronoun gives the shifted reading.
-/

open Core.Tense (TensePronoun doubleAccess)

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
  simp [TensePronoun.toFrame, TensePronoun.resolve, simultaneousFrame, hIdx, hResolve]

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
  simp [TensePronoun.toFrame, TensePronoun.resolve, shiftedFrame, hIdx, hResolve]

/-- Double-access (Abusch 1997): present-under-past requires the complement
    to hold at BOTH speech time AND matrix event time.

    This bridges the `doubleAccess` definition from `Core.Tense` to the
    existing `embeddedSickPresent` data: the present-under-past frame's
    R = P (simultaneous), and the speech time is independently accessible
    via indexical rigidity. -/
theorem doubleAccess_present_under_past {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (_embeddedE : Time)
    (p : Time → Prop)
    (h_simul : p matrixFrame.eventTime)
    (h_speech : p matrixFrame.speechTime) :
    doubleAccess p matrixFrame.speechTime matrixFrame.eventTime :=
  ⟨h_speech, h_simul⟩


end TruthConditional.Sentence.Tense.SequenceOfTense
