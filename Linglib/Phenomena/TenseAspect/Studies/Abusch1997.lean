import Linglib.Theories.Semantics.Tense.Basic
import Linglib.Theories.Semantics.Tense.DeRe.Defs

/-!
# @cite{abusch-1997}: Sequence of Tense and Temporal de re
@cite{abusch-1997} @cite{sharvit-2003} @cite{heim-1994-comments}

@cite{abusch-1997}'s theory: tense morphemes are temporal pronouns
(variables with presupposed constraints and binding modes). The key
innovation is **temporal de re**: tense can take wide scope over
attitude operators via res movement, just as DPs can scope out of
attitude complements.

The substrate machinery (`TemporalDeRe` structure + `isFelicitous`)
lives in `Theories/Semantics/Tense/DeRe/Defs.lean`. This Studies file
collects the @cite{abusch-1997}-anchored derivation theorems.

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
   attitude. The `TemporalDeRe` structure captures the *output* of
   res-movement (a back-shifted frame with a constraint tag); the LF
   rewrite mechanism + time-concept (acquaintance relation) machinery
   is not formalized here.
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
open Semantics.Tense.DeRe (TemporalDeRe)


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
    temporal reference. When the res referent satisfies the past
    constraint against the matrix eval time, the de re reading is
    felicitous. -/
theorem abusch_derives_temporal_de_re {Time : Type*} [LinearOrder Time]
    (dr : TemporalDeRe Time)
    (hPast : dr.constraint = .past)
    (hBefore : dr.referent < dr.evalTime) :
    dr.isFelicitous := by
  simp only [TemporalDeRe.isFelicitous, GramTense.constrains, hPast]
  exact hBefore


end Phenomena.TenseAspect.Studies.Abusch1997
