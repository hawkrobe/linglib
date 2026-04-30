import Linglib.Theories.Semantics.Tense.Basic
import Linglib.Theories.Semantics.Tense.DeRe
import Linglib.Theories.Semantics.Dynamic.PLA.Belief

/-!
# @cite{abusch-1997}: Sequence of Tense and Temporal de re
@cite{abusch-1997} @cite{sharvit-2003} @cite{heim-1994-comments}
@cite{lewis-1979-attitudes} @cite{cresswell-vonstechow-1982}

@cite{abusch-1997}'s theory: tense morphemes are temporal pronouns
(variables with presupposed constraints and binding modes). The key
innovation is **temporal de re**: tense can take wide scope over
attitude operators via res movement, just as DPs can scope out of
attitude complements.

Two derivation styles coexist in this file:

1. **Value-level shadow** (`abusch_derives_*` against `TensePronoun.fullPresupposition`):
   tense pronoun + `GramTense.constrains` + temporal assignment.
   Captures Abusch's predictions at the value level without committing
   to the centered-world architecture. Cheap, presupposition-free.

2. **Centered-world substrate** (`abusch_derives_*_via_acquaintance` /
   `_full` / `_full_metaphysical` against
   `Semantics.Tense.DeRe.TemporalDeReReading`): `Intension (KContext)
   Time` time-concept + holder-context base anchor + modal-alternative
   quantification over a `Set (WorldTimeIndex W Time)`. The Abusch §3 +
   def. 13 architecture, faithful to the @cite{lewis-1979-attitudes} /
   @cite{cresswell-vonstechow-1982} centered-world reduction of de re.
   The two styles are bridged by
   `Semantics.Tense.DeRe.TemporalDeReReading.isFelicitousWith_iff_tensePronoun_fullPresupposition`.

The substrate is modal-base-agnostic and holder-now-honest:
`holderContext.time` is the holder's now (per §7 ULC), and
`IsRigidAcrossAlternatives` takes a `Set (WorldTimeIndex)` parameter
(with `metaphysicalAlternatives` / `doxasticAlternatives` convenience
constructors). See `Tense/DeRe.lean` docstring for what's deferred
(LF rewrite operator, etc.).

## Core Mechanisms

1. **Tense as pronoun**: `TensePronoun` (in `Core.Time.Tense`) with
   variable index, constraint, and binding mode.
2. **Upper Limit Constraint (ULC)**: stated by @cite{abusch-1997} §7
   ("the now of an epistemic alternative is an upper limit for the
   denotation of tenses"); presuppositional construal due to
   @cite{heim-1994-comments}, endorsed by Abusch 1997 fn 20. Lives in
   `Theories/Semantics/Tense/Basic.lean` as `upperLimitConstraint`,
   formalized at the value level as `embeddedR ≤ matrixE`. **Note:**
   this value-level reduction strips the modal-alternative
   quantification the original formulation carries; making the modal
   layer explicit (over `WorldHistory W Time` à la @cite{klecha-2016})
   is deferred.
3. **Temporal de re**: tense variable in the res position of an
   attitude. The value-level shadow uses `TensePronoun.fullPresupposition`:
   constraint applied to (resolved time, eval time). The LF rewrite +
   acquaintance-relation machinery (Lewis 1979 / Cresswell-von Stechow
   1982) is not formalized here.
4. **Eval-time shift via attitude embedding**: the substrate primitives
   are `Core.Time.Tense.evalTime_shifts_under_embedding` and
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

- Relative clause tense: @cite{sharvit-2003}'s challenge (the mechanism
  doesn't extend straightforwardly to relative clauses where the tense
  takes the perspective of a participant)
- Modal-tense interaction: not addressed in @cite{abusch-1997}'s
  framework (see @cite{klecha-2016} for a successor)
- Counterfactual tense: not addressed
- Counterpart-relation isomorphism @cite{abusch-1997} §12 invokes for
  the double-access reading derivation (the constraint that actual
  and belief worlds be temporally isomorphic, eliminating most of the
  4 cells in the DAR diagram on p. 43): not formalized
- Modal-layer ULC formulation: see Core Mechanism 2 above

-/

namespace Phenomena.TenseAspect.Studies.Abusch1997

open Core.Time.Tense
open Core.Time.Reichenbach
open Core.Time
open Semantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- @cite{abusch-1997} derives the shifted reading: a free past
    variable with presupposition checked against the (shifted) eval
    time. The past constraint gives R < evalTime = matrixE.

    Note: the proof closes via `embeddedFrame.isPast`'s definition,
    which only requires `tp.resolve g < matrixFrame.eventTime`. The
    `tp.constraint = .past` condition is what *Abusch's theory* says
    licenses this reading, but it isn't load-bearing in this proof —
    the conclusion follows for any tense pronoun whose resolution is
    below the matrix event time. A full Abusch derivation would
    project through `tp.constraint.constrains` from the binding mode. -/
theorem abusch_derives_shifted {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time)
    (hPresup : tp.resolve g < matrixFrame.eventTime) :
    (embeddedFrame matrixFrame (tp.resolve g) (tp.resolve g)).isPast := by
  simp only [embeddedFrame, ReichenbachFrame.isPast]
  exact hPresup

/-- @cite{abusch-1997} derives the simultaneous reading: a bound
    variable receives the matrix event time via lambda abstraction. -/
theorem abusch_derives_simultaneous {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time)
    (hBind : tp.resolve g = matrixFrame.eventTime) :
    (embeddedFrame matrixFrame (tp.resolve g) (tp.resolve g)).isPresent := by
  simp only [embeddedFrame, ReichenbachFrame.isPresent, hBind]

/-- @cite{abusch-1997} derives the simultaneous reading via the bound
    variable mechanism: updating the temporal assignment so the tense
    variable receives matrix E. -/
theorem abusch_derives_simultaneous_via_binding {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time) :
    tp.resolve (updateTemporal g tp.varIndex matrixFrame.eventTime) =
    matrixFrame.eventTime :=
  tp.bound_resolve_eq_binder g matrixFrame.eventTime

/-- @cite{abusch-1997}'s double-access *placeholder*: indexical present
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

/-- @cite{abusch-1997} derives temporal de re: the tense variable in
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
    (hPast : tp.constraint = .past)
    (hBefore : tp.resolve g < tp.evalTime g) :
    tp.fullPresupposition g := by
  simp only [TensePronoun.fullPresupposition, GramTense.constrains, hPast]
  exact hBefore


-- ════════════════════════════════════════════════════════════════
-- § Centered-World Substrate Derivations
-- ════════════════════════════════════════════════════════════════

/-- @cite{abusch-1997}'s temporal de re via the centered-world substrate
    (`Theories/Semantics/Tense/DeRe.lean`): any `TemporalDeReReading`
    whose actual res-time precedes the holder's now satisfies the past
    constraint. Value-level felicity reduces to the actualRes ordering;
    rigidity of the concept (= acquaintance-anchored res reading) is
    not required for the value-level shadow. -/
theorem abusch_derives_temporal_de_re_via_acquaintance
    {W E P Time : Type*} [LinearOrder Time]
    (dr : Semantics.Tense.DeRe.TemporalDeReReading W E P Time)
    (hBefore : dr.actualRes < dr.holderContext.time) :
    dr.isFelicitousWith .past := hBefore

/-- @cite{abusch-1997}'s temporal de re with **modal-alternative
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
    (dr : Semantics.Tense.DeRe.TemporalDeReReading W E P Time)
    (hRigid : Core.Intension.IsRigid dr.concept)
    (alternatives : Set (Core.WorldTimeIndex W Time))
    (hBefore : dr.actualRes < dr.holderContext.time) :
    dr.isAbuschFelicitous alternatives .past := by
  refine ⟨hBefore, ?_⟩
  exact Semantics.Tense.DeRe.TemporalDeReReading.IsRigidAcrossAlternatives_of_concept_isRigid
    dr hRigid alternatives

/-- **Metaphysical-instantiation specialization** of
    `abusch_derives_temporal_de_re_full`. Recovers the legacy
    `WorldHistory`-based formulation as a corollary at the
    `metaphysicalAlternatives` instance, demonstrating backward
    compatibility with Klecha 2016 DOX-shaped reasoning. -/
theorem abusch_derives_temporal_de_re_full_metaphysical
    {W E P Time : Type*} [LinearOrder Time]
    (dr : Semantics.Tense.DeRe.TemporalDeReReading W E P Time)
    (hRigid : Core.Intension.IsRigid dr.concept)
    (history : Core.Modality.HistoricalAlternatives.WorldHistory W Time)
    (hBefore : dr.actualRes < dr.holderContext.time) :
    dr.isAbuschFelicitous (dr.metaphysicalAlternatives history) .past :=
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
    the same acquaintance substrate, making true @cite{abusch-1997}'s
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


end Phenomena.TenseAspect.Studies.Abusch1997
