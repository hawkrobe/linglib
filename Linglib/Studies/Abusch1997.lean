import Linglib.Semantics.Tense.Basic
import Linglib.Semantics.Tense.DeRe
import Linglib.Semantics.Dynamic.PLA.Belief
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.Abusch1997

/-!
# [abusch-1997]: Sequence of Tense and Temporal de re
[abusch-1997] [sharvit-2003] [heim-1994-comments]
[lewis-1979-attitudes] [cresswell-vonstechow-1982]

[abusch-1997]'s theory: tense morphemes are temporal pronouns
(variables with presupposed constraints and binding modes). The key
innovation is **temporal de re**: tense can take wide scope over
attitude operators via res movement, just as DPs can scope out of
attitude complements.

Two derivation styles coexist in this file:

1. **Value-level shadow** (`abusch_derives_*` against `TensePronoun.fullPresupposition`):
   tense pronoun + `Core.Order.holds` + temporal assignment.
   Captures Abusch's predictions at the value level without committing
   to the centered-world architecture. Cheap, presupposition-free.

2. **Centered-world substrate** (`abusch_derives_*_via_acquaintance` /
   `_full` / `_full_metaphysical` against
   `Tense.DeRe.TemporalDeReReading`): `Intension (KContext)
   Time` time-concept + holder-context base anchor + modal-alternative
   quantification over a `Set (WorldTimeIndex W Time)`. The Abusch §3 +
   def. 13 architecture, faithful to the [lewis-1979-attitudes] /
   [cresswell-vonstechow-1982] centered-world reduction of de re.
   The two styles are bridged by
   `Tense.DeRe.TemporalDeReReading.isFelicitousWith_iff_tensePronoun_fullPresupposition`.

The substrate is modal-base-agnostic and holder-now-honest:
`holderContext.time` is the holder's now (per §7 ULC), and
`IsRigidAcrossAlternatives` takes a `Set (WorldTimeIndex)` parameter
(with `metaphysicalAlternatives` / `doxasticAlternatives` convenience
constructors). See `Tense/DeRe.lean` docstring for what's deferred
(LF rewrite operator, etc.).

## Core Mechanisms

1. **Tense as pronoun**: `TensePronoun` (in `Tense`) with
   variable index, constraint, and binding mode.
2. **Upper Limit Constraint (ULC)**: stated by [abusch-1997] §7
   ("the now of an epistemic alternative is an upper limit for the
   denotation of tenses"); presuppositional construal due to
   [heim-1994-comments], endorsed by Abusch 1997 fn 20. Lives in
   `Semantics/Tense/Basic.lean` as `upperLimitConstraint`,
   formalized at the value level as `embeddedR ≤ matrixE`. **Note:**
   this value-level reduction strips the modal-alternative
   quantification the original formulation carries; making the modal
   layer explicit (over `HistoricalAlternatives W Time` à la [klecha-2016])
   is deferred.
3. **Temporal de re**: tense variable in the res position of an
   attitude. The value-level shadow uses `TensePronoun.fullPresupposition`:
   constraint applied to (resolved time, eval time). The LF rewrite +
   acquaintance-relation machinery (Lewis 1979 / Cresswell-von Stechow
   1982) is not formalized here.
4. **Eval-time shift via attitude embedding**: the substrate primitives
   are `Tense.evalTime_shifts_under_embedding` and
   `updateTemporal`. Abusch's "relation transmission" (feature passing
   of relation variables PAST/PRES across embedding) is *not* what this
   file currently captures — we only model the value-level eval-time
   update.

## Derivation Theorems

- Shifted reading: free past variable with presupposition against eval time
- Simultaneous reading: bound variable receives matrix event time
- Double-access: indexical present + attitude binding (placeholder; the
  full Abusch derivation involves doxastic alternatives + acquaintance
  relations + the rigid-present presupposition, not formalized here)
- Temporal de re: res movement for wide-scope tense

## Limitations

- Relative clause tense: [sharvit-2003]'s challenge (the mechanism
  doesn't extend straightforwardly to relative clauses where the tense
  takes the perspective of a participant)
- Modal-tense interaction: not addressed in [abusch-1997]'s
  framework (see [klecha-2016] for a successor)
- Counterfactual tense: not addressed
- Counterpart-relation isomorphism [abusch-1997] §12 invokes for
  the double-access reading derivation (the constraint that actual
  and belief worlds be temporally isomorphic, eliminating most of the
  4 cells in the DAR diagram on p. 43): not formalized
- Modal-layer ULC formulation: see Core Mechanism 2 above

-/

open Time

namespace Abusch1997

open Tense
open Data.Examples (LinguisticExample)

-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- [abusch-1997] derives the shifted reading: a free past
    variable with presupposition checked against the (shifted) eval
    time. The past constraint gives R < evalTime = matrixE.

    Note: the proof closes via `embeddedFrame.isPast`'s definition,
    which only requires `tp.resolve g < matrixFrame.eventTime`. The
    `tp.constraint = .past` condition is what *Abusch's theory* says
    licenses this reading, but it isn't load-bearing in this proof —
    the conclusion follows for any tense pronoun whose resolution is
    below the matrix event time. A full Abusch derivation would
    project through `Core.Order.holds tp.constraint` from the binding mode. -/
theorem abusch_derives_shifted {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time)
    (hPresup : tp.resolve g < matrixFrame.eventTime) :
    (embeddedFrame matrixFrame (tp.resolve g) (tp.resolve g)).isPast := by
  simp only [embeddedFrame, ReichenbachFrame.isPast_def]
  exact hPresup

/-- [abusch-1997] derives the simultaneous reading: a bound
    variable receives the matrix event time via lambda abstraction. -/
theorem abusch_derives_simultaneous {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time)
    (hBind : tp.resolve g = matrixFrame.eventTime) :
    (embeddedFrame matrixFrame (tp.resolve g) (tp.resolve g)).isPresent := by
  simp only [embeddedFrame, ReichenbachFrame.isPresent, hBind]

/-- [abusch-1997] derives the simultaneous reading via the bound
    variable mechanism: updating the temporal assignment so the tense
    variable receives matrix E. -/
theorem abusch_derives_simultaneous_via_binding {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time) :
    tp.resolve (updateTemporal g tp.varIndex matrixFrame.eventTime) =
    matrixFrame.eventTime :=
  tp.bound_resolve_eq_binder g matrixFrame.eventTime

/-- [abusch-1997]'s double-access *placeholder*: indexical present
    requires truth at BOTH speech time (indexical rigidity) AND matrix
    event time (attitude accessibility). The full Abusch derivation
    involves doxastic alternatives + acquaintance relations + the
    rigid-present presupposition; this theorem only states the surface
    conjunction. -/
theorem abusch_derives_double_access {Time : Type*}
    (p : Time → Prop) (speechTime matrixEventTime : Time)
    (h_speech : p speechTime) (h_matrix : p matrixEventTime) :
    doubleAccess p speechTime matrixEventTime :=
  ⟨h_speech, h_matrix⟩

/-- [abusch-1997] derives temporal de re: the tense variable in
    res position is evaluated in the matrix context, giving wide-scope
    temporal reference. When the resolved referent satisfies the past
    constraint against the (matrix-shifted) eval time, the de re reading
    is felicitous.

    Value-level shadow: this theorem checks `TensePronoun.fullPresupposition`,
    not Abusch's actual centered-proposition rule (paper def. 13). The
    `g` here would, in the full account, be a temporal assignment shifted
    by the attitude verb to put the matrix event time at `tp.evalTimeIndex`. -/
theorem abusch_derives_temporal_de_re {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (hPast : tp.constraint = Tense.past)
    (hBefore : tp.resolve g < tp.evalTime g) :
    tp.fullPresupposition g := by
  simp only [TensePronoun.fullPresupposition, hPast, Tense.past, Core.Order.holds_before]
  exact hBefore


-- ════════════════════════════════════════════════════════════════
-- § Centered-World Substrate Derivations
-- ════════════════════════════════════════════════════════════════

/-- [abusch-1997]'s temporal de re via the centered-world substrate
    (`Semantics/Tense/DeRe.lean`): any `TemporalDeReReading`
    whose actual res-time precedes the holder's now satisfies the past
    constraint. Value-level felicity reduces to the actualRes ordering;
    rigidity of the concept (= acquaintance-anchored res reading) is
    not required for the value-level shadow. -/
theorem abusch_derives_temporal_de_re_via_acquaintance
    {W E P Time : Type*} [LinearOrder Time]
    (dr : Tense.DeRe.TemporalDeReReading W E P Time)
    (hBefore : dr.actualRes < dr.holderContext.time) :
    dr.isFelicitousWith Tense.past :=
  (Core.Order.holds_before dr.actualRes dr.holderContext.time).mpr hBefore

/-- [abusch-1997]'s temporal de re with **modal-alternative
    quantification** (substrate-level lift of the §3 p. 9 base-world
    condition): the time-concept identifies the same time across an
    `alternatives : Set (WorldTimeIndex W Time)`. The substrate is
    modal-base-agnostic; this theorem holds for any alternative-set
    the consumer supplies (doxastic, metaphysical, or other). The
    full `isAbuschFelicitous` predicate combines the value-level past
    constraint with this modal rigidity.

    A rigid time-concept (constant intension) discharges the modal
    rigidity automatically — Abusch's de re reading is satisfied "for
    free" when the res is identified by a name-like rigid concept. -/
theorem abusch_derives_temporal_de_re_full
    {W E P Time : Type*} [LinearOrder Time]
    (dr : Tense.DeRe.TemporalDeReReading W E P Time)
    (hRigid : Intensional.Intension.IsRigid dr.concept)
    (alternatives : Set (Intensional.WorldTimeIndex W Time))
    (hBefore : dr.actualRes < dr.holderContext.time) :
    dr.isAbuschFelicitous alternatives Tense.past := by
  refine ⟨(Core.Order.holds_before dr.actualRes dr.holderContext.time).mpr hBefore, ?_⟩
  exact Tense.DeRe.TemporalDeReReading.IsRigidAcrossAlternatives_of_concept_isRigid
    dr hRigid alternatives

/-- **Metaphysical-instantiation specialization** of
    `abusch_derives_temporal_de_re_full`. Recovers the legacy
    `HistoricalAlternatives`-based formulation as a corollary at the
    `metaphysicalAlternatives` instance, demonstrating backward
    compatibility with Klecha 2016 DOX-shaped reasoning. -/
theorem abusch_derives_temporal_de_re_full_metaphysical
    {W E P Time : Type*} [LinearOrder Time]
    (dr : Tense.DeRe.TemporalDeReReading W E P Time)
    (hRigid : Intensional.Intension.IsRigid dr.concept)
    (history : HistoricalAlternatives W Time)
    (hBefore : dr.actualRes < dr.holderContext.time) :
    dr.isAbuschFelicitous (dr.metaphysicalAlternatives history) Tense.past :=
  abusch_derives_temporal_de_re_full dr hRigid _ hBefore

/-- **PLA ↔ Abusch substrate unification**: PLA's `isAcquaintedWith`
    (entity-side, individual de re) and the polymorphic
    `Reference.Acquaintance.isAcquaintedWith` are the same predicate
    at the PLA index `Idx := Poss E`. Provable by `Iff.rfl` because
    PLA's wrapper is a definitional alias (`abbrev`) of the
    polymorphic version.

    The *content* of the theorem is structural — it shows the de re
    reading PLA proves about *individuals* and the de re reading
    `TemporalDeReReading` exposes for *times* are instantiations of
    the same acquaintance substrate, making true [abusch-1997]'s
    p. 6 prose claim ("To apply the same machinery to de re belief,
    a further constraint is required") via the `Acquaintance`
    polymorphism. -/
theorem pla_isAcquaintedWith_unifies_with_polymorphic
    {E : Type*} (individual : E)
    (C : Semantics.Dynamic.PLA.Cover E)
    (p : Semantics.Dynamic.PLA.Poss E) :
    Semantics.Dynamic.PLA.isAcquaintedWith individual C p ↔
    Semantics.Reference.Acquaintance.isAcquaintedWith individual C p :=
  Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- § Empirical Data: Abusch's SOT Diagnostic Sentences
-- ════════════════════════════════════════════════════════════════

/-! Reichenbach frames for the canonical Abusch-tradition SOT
    diagnostics: past-under-past (simultaneous + shifted), present-
    under-past (double-access), future-under-past (would), the ULC
    foil (forward-shifted), and temporal de re. Each embedded frame
    is constructed via the `embeddedFrame` / `simultaneousFrame` /
    `shiftedFrame` substrate operators (per CLAUDE.md
    "Theory-hub denotation as study-file constraint") rather than
    hand-stipulating S/P/R/E records. -/

/-- Matrix frame for "John said..." (past tense, perfective).
    Speech time S = 0, saying event at t = -2. Root clause: P = S;
    perfective: E = R. -/
def matrixSaid : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2
  eventTime := -2

/-- "Mary was sick" — SIMULTANEOUS reading. Embedded P = matrix E = -2,
    R' = E_matrix = -2: Mary is sick at the time of the saying. -/
def embeddedSickSimultaneous : ReichenbachFrame ℤ :=
  simultaneousFrame matrixSaid (-2)

/-- "Mary was sick" — SHIFTED reading. R' = -5 < E_matrix: Mary was
    sick before the saying. -/
def embeddedSickShifted : ReichenbachFrame ℤ :=
  shiftedFrame matrixSaid (-5) (-5)

/-- "Mary is sick" (present-under-past) — DOUBLE-ACCESS reading.
    Embedded P = matrix E = -2, R' = -2, E = 0 (speech time):
    Mary is sick now AND the sickness is relevant at the time of saying. -/
def embeddedSickPresent : ReichenbachFrame ℤ :=
  embeddedFrame matrixSaid (-2) 0

/-- "Mary would leave" (future-under-past). "Would" = PAST + FUTURE:
    the leaving is after the saying. R' = -1 > E_matrix. -/
def embeddedWouldLeave : ReichenbachFrame ℤ :=
  embeddedFrame matrixSaid (-1) (-1)

/-- Hypothetical FORWARD-SHIFTED frame (ULC foil, §7). R' = -1 >
    E_matrix = -2: sick AFTER the saying. **Predicted not to exist as
    a reading** per Abusch's Upper Limit Constraint. Structurally
    coincides with `embeddedWouldLeave`'s record — the Reichenbach
    encoding cannot distinguish "ULC violation" from "valid future
    reading"; only the analyst's intent and the sentence's actual
    meaning do. -/
def embeddedSickForwardShifted : ReichenbachFrame ℤ :=
  embeddedFrame matrixSaid (-1) (-1)

/-- "John believed it was raining" — TEMPORAL DE RE. The rain event
    is located at -3 via the actual world (de re), not in John's
    belief worlds (de dicto). Embedded P = -2, R = E = -3. -/
def temporalDeRe : ReichenbachFrame ℤ :=
  embeddedFrame matrixSaid (-3) (-3)


-- ════════════════════════════════════════════════════════════════
-- § Per-Datum Verifications
-- ════════════════════════════════════════════════════════════════

/-- The simultaneous frame is `isPresent` (R = P).
    Per Abusch: a bound variable receives matrix E. -/
theorem abusch_derives_embeddedSickSimultaneous :
    embeddedSickSimultaneous.isPresent := rfl

/-- The shifted frame is `isPast` (R < P).
    Per Abusch: a free past variable below the matrix event time. -/
theorem abusch_derives_embeddedSickShifted :
    embeddedSickShifted.isPast := by
  simp only [ReichenbachFrame.isPast_def, embeddedSickShifted, shiftedFrame,
    Tense.embeddedFrame, matrixSaid]; omega

/-- The matrix "said" frame is perfective (E = R). -/
theorem matrixSaid_is_perfective : matrixSaid.isPerfective := rfl

/-- The shifted embedded frame is perfective (E = R). -/
theorem embeddedShifted_is_perfective : embeddedSickShifted.isPerfective := rfl

/-- Forward-shifted reading violates ULC: R' > E_matrix is not allowed. -/
theorem forwardShifted_violates_ulc :
    ¬ upperLimitConstraint
      embeddedSickForwardShifted.referenceTime
      matrixSaid.eventTime := by decide

/-- Simultaneous reading satisfies ULC: R' ≤ E_matrix. -/
theorem simultaneous_satisfies_ulc :
    upperLimitConstraint
      embeddedSickSimultaneous.referenceTime
      matrixSaid.eventTime := by decide

/-- Shifted reading satisfies ULC: R' < E_matrix. -/
theorem shifted_satisfies_ulc :
    upperLimitConstraint
      embeddedSickShifted.referenceTime
      matrixSaid.eventTime := by decide


end Abusch1997
