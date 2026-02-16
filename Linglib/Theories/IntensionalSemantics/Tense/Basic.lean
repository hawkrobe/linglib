import Linglib.Core.Tense
import Linglib.Core.Time
import Linglib.Core.Reichenbach

/-!
# Tense Theory Infrastructure: Shared Types

Shared types and infrastructure for the tense theories formalized in
`IntensionalSemantics/Tense/` (Abusch 1997, Von Stechow 2009, Kratzer 1998,
Ogihara 1996, Klecha 2016, Deal 2020, Sharvit 2003) and
`Minimalism/Tense/` (Zeijlstra 2012, Wurmbrand 2014).

## Design Principle

Verdicts are **derived from compositional semantics**, not stipulated.
Each theory file proves derivation theorems for the phenomena it handles;
the comparison matrix (`Comparisons/TenseTheories.lean`) is assembled
from what's been proven. There is no `TheoryVerdict` enum — whether a
theory "handles" a phenomenon is witnessed by the existence (or absence)
of a derivation theorem in that theory's file.

## Key Types

- `TensePhenomenon`: the 23 temporal phenomena that distinguish theories
- `TenseTheory`: identity card for a theory (no verdict field)
- `AttitudeTemporalSemantics`: how an attitude verb shifts eval time

## References

- Abusch, D. (1997). Sequence of tense and temporal de re.
- Von Stechow, A. (2009). Tenses in compositional semantics.
- Kratzer, A. (1998). More structural analogies between pronouns and tenses.
- Ogihara, T. (1996). Tense, attitudes, and scope.
- Klecha, P. (2016). Modality and embedded temporal operators.
- Deal, A. R. (2020). Counterfactuals and the Upper Limit Constraint.
- Sharvit, Y. (2003). Embedded tense and universal grammar.
- Zeijlstra, H. (2012). There is only one way to agree.
- Wurmbrand, S. (2014). Tense and aspect in English infinitives.
-/

namespace IntensionalSemantics.Tense

open Core.Tense
open Core.Time
open Core.Reichenbach


-- ════════════════════════════════════════════════════════════════
-- § TensePhenomenon
-- ════════════════════════════════════════════════════════════════

/-- The 23 temporal phenomena that distinguish tense theories.

    Each phenomenon represents an empirical domain where theories
    make different predictions or use different mechanisms. The
    comparison matrix is built from which derivation theorems each
    theory proves for each phenomenon.

    The first 11 are the core comparison set. The next 7 are eventual
    targets documented with data frames. The final 5 are added for
    Zeijlstra (2012), Wurmbrand (2014), and Sharvit (2003) coverage. -/
inductive TensePhenomenon where
  -- Core comparison set (11)
  /-- "John said Mary was sick" — shifted reading (sick before saying) -/
  | pastUnderPast_shifted
  /-- "John said Mary was sick" — simultaneous reading (sick at saying) -/
  | pastUnderPast_simultaneous
  /-- "John said Mary is sick" — double-access reading -/
  | presentUnderPast_doubleAccess
  /-- "John said Mary would leave" — embedded future -/
  | futureUnderPast
  /-- English (SOT) vs Japanese (non-SOT) parametric variation -/
  | sotVsNonSOT
  /-- Abusch's upper limit constraint: no forward-shifted readings -/
  | upperLimitConstraint
  /-- "the man who was tall" — relative clause tense interpretation -/
  | relativeClauseTense
  /-- "John might have left" — modal scoping over past -/
  | modalTenseInteraction
  /-- "If John were here..." — past morphology, non-temporal -/
  | counterfactualTense
  /-- "John believed it was raining" — de re temporal reference -/
  | temporalDeRe
  /-- Kratzer (deletion) vs Ogihara (zero tense ambiguity) debate -/
  | deletionVsAmbiguity
  -- Eventual targets (7)
  /-- "John asked who was sick" — SOT in indirect questions
      (Sharvit 2003, Ogihara & Sharvit 2012) -/
  | sotInIndirectQuestions
  /-- "She walked to the window. The garden was beautiful." — FID
      perspective shift without attitude verb (Banfield 1982, Schlenker 2004) -/
  | freeIndirectDiscourse
  /-- "Napoleon enters the room. He sees..." — present tense, past reference
      (Wolfson 1979, Schiffrin 1981) -/
  | historicalPresent
  /-- "John said Mary had been sick" — pluperfect disambiguates to shifted only
      (Comrie 1985, Ogihara 1996) -/
  | perfectTenseInteraction
  /-- "John wanted/planned to leave" — future-oriented complements
      without standard SOT (Wurmbrand 2014, Grano 2017) -/
  | futureOrientedComplements
  /-- "Before John left, Mary was happy" — tense in temporal adjuncts
      (Arregui & Kusumoto 1998, Ogihara & Sharvit 2012) -/
  | adjunctClauseTense
  /-- Amharic/Zazaki: tense shifts under attitudes paralleling pronoun shift
      (Schlenker 2003, Anand & Nevins 2004) -/
  | indexicalTenseShift
  -- Additional phenomena (5) — Sharvit, Zeijlstra, Wurmbrand coverage
  /-- "John will say Mary is sick" — present under future, simultaneous
      with future saying time (Sharvit 2003) -/
  | embeddedPresentPuzzle
  /-- "Aristotle was a philosopher" — past tense ↔ subject no longer
      exists implication (Musan 1995/1997) -/
  | lifetimeEffects
  /-- "If John were taller..." — past morphology, non-past semantics
      (Iatridou 2000, beyond Deal's counterfactual tense) -/
  | fakePast
  /-- Hebrew-type optional SOT: "John said Mary {was/is} sick" —
      both possible with different readings (Sharvit 2003) -/
  | optionalSOT
  /-- Wurmbrand (2014): three-way classification of infinitival tense
      (future irrealis / propositional / restructuring) -/
  | dependentVsIndependentTense
  deriving DecidableEq, Repr, BEq, Inhabited


-- ════════════════════════════════════════════════════════════════
-- § TenseTheory
-- ════════════════════════════════════════════════════════════════

/-- A tense theory's identity card.

    This records the structural properties of each account — what
    mechanisms it posits — without encoding verdicts. Whether the
    theory handles a given phenomenon is determined by the existence
    of derivation theorems in the theory's file.

    Fields are Bool because they describe categorical properties
    of the formal system, not graded judgments. -/
structure TenseTheory where
  /-- Theory name (e.g., "Abusch 1997") -/
  name : String
  /-- Full citation -/
  citation : String
  /-- Does the theory have a temporal de re mechanism? -/
  hasTemporalDeRe : Bool
  /-- Does the theory impose an upper limit constraint? -/
  hasULC : Bool
  /-- Does the theory posit a zero tense (ambiguous past)? -/
  hasZeroTense : Bool
  /-- Does the theory use SOT deletion for the simultaneous reading? -/
  hasSOTDeletion : Bool
  /-- Does the theory use syntactic Agree for SOT (Zeijlstra 2012)? -/
  hasAgreeBasedSOT : Bool := false
  /-- How the theory derives the simultaneous reading -/
  simultaneousMechanism : String
  deriving Repr


-- ════════════════════════════════════════════════════════════════
-- § AttitudeTemporalSemantics
-- ════════════════════════════════════════════════════════════════

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

/-- Standard eval time shift: embedded eval time = matrix event time.
    This is the default across all six theories. -/
def standardShift {Time : Type*} : AttitudeTemporalSemantics Time where
  shiftEvalTime := λ f => f.eventTime
  embeddedConstraint := λ _embR _evalT => True

/-- Standard shift gives matrix event time. -/
theorem standardShift_is_eventTime {Time : Type*} (f : ReichenbachFrame Time) :
    (standardShift (Time := Time)).shiftEvalTime f = f.eventTime := rfl


-- ════════════════════════════════════════════════════════════════
-- § Phenomenon Classification
-- ════════════════════════════════════════════════════════════════

/-- A phenomenon is a core SOT phenomenon if all theories handle it. -/
def TensePhenomenon.isCoreSOT : TensePhenomenon → Bool
  | .pastUnderPast_shifted => true
  | .pastUnderPast_simultaneous => true
  | .presentUnderPast_doubleAccess => true
  | .sotVsNonSOT => true
  | _ => false

/-- A phenomenon is a distinguishing phenomenon if theories diverge on it. -/
def TensePhenomenon.isDistinguishing : TensePhenomenon → Bool
  | .relativeClauseTense => true
  | .modalTenseInteraction => true
  | .counterfactualTense => true
  | .temporalDeRe => true
  | .deletionVsAmbiguity => true
  | _ => false

/-- A phenomenon is an eventual target — documented with data but not yet
    connected to derivation theorems in the theory files. -/
def TensePhenomenon.isEventualTarget : TensePhenomenon → Bool
  | .sotInIndirectQuestions => true
  | .freeIndirectDiscourse => true
  | .historicalPresent => true
  | .perfectTenseInteraction => true
  | .futureOrientedComplements => true
  | .adjunctClauseTense => true
  | .indexicalTenseShift => true
  | _ => false

/-- A phenomenon is in the extended set added for Zeijlstra/Wurmbrand/Sharvit. -/
def TensePhenomenon.isExtended : TensePhenomenon → Bool
  | .embeddedPresentPuzzle => true
  | .lifetimeEffects => true
  | .fakePast => true
  | .optionalSOT => true
  | .dependentVsIndependentTense => true
  | _ => false

/-- Every phenomenon falls into exactly one of the five categories. -/
theorem phenomenon_coverage (p : TensePhenomenon) :
    p.isCoreSOT = true ∨ p.isDistinguishing = true ∨
    p.isEventualTarget = true ∨ p.isExtended = true ∨
    p = .futureUnderPast ∨ p = .upperLimitConstraint := by
  cases p <;> simp [TensePhenomenon.isCoreSOT, TensePhenomenon.isDistinguishing,
    TensePhenomenon.isEventualTarget, TensePhenomenon.isExtended]


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
-- § Perspective Shift Derivations
-- ════════════════════════════════════════════════════════════════

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

/-- Present-under-past with the simultaneous reading: embedded R = matrix E. -/
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

/-- The simultaneousFrame satisfies the time-equality R = P. -/
theorem simultaneousFrame_satisfies_time_eq {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time) :
    (simultaneousFrame matrixFrame embeddedE).referenceTime =
    (simultaneousFrame matrixFrame embeddedE).perspectiveTime := by rfl


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
-- § TensePronoun ↔ SOT Frames
-- ════════════════════════════════════════════════════════════════

/-!
### TensePronoun Projections onto SOT Frames

The `TensePronoun` type in `Core.Tense` unifies the five views of tense.
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


end IntensionalSemantics.Tense
