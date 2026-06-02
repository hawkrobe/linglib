/-
# Viewpoint Aspect Operators

[klein-1994] viewpoint aspect formalized as interval relations between
Topic Time (TT) and Situation Time (TSit), with compositional operators
following [knick-sharf-2026].

## Klein's Aspect Definitions (Chapter 6, p. 108)

| # | Relation | Name | Intuition |
|---|----------|------|-----------|
| 1 | TT INCL TSit | IMPERFECTIVE | TT fully inside TSit |
| 2 | TT AT TSit | PERFECTIVE | TSit within/overlapping TT |
| 3a | TT AFTER TSit | PERFECT | TT in posttime of TSit |
| 3b | TT BEFORE TSit | PROSPECTIVE | TT in pretime of TSit |

## Compositional Architecture

```
Event Time → Prop ──[IMPF/PRFV]──▷ IntervalPred ──[PERF]──▷ PointPred ──[TENSE]──▷ Prop
```

Equations (verified against the [knick-sharf-2026] proceedings PDF):

- (25) ⟦IMPF⟧^g = λP.λt.∃e[t ⊂ τ(e) ∧ P(e)]
- (28) ⟦PRFV⟧^g = λP.λt.∃e[τ(e) ⊆ t ∧ P(e)]
- (22b) standard XN: ⟦PERF⟧^g = λp_it.λt.∃t_PTS.[RB(t_PTS, t) ∧ p(t)]
- (23b) K&S revision: ⟦PERF⟧^g = λp_it.λt.∃t_PTS.∃t_LB ⊆ tᵣ
                                  [LB(t_LB, t_PTS) ∧ RB(t_PTS, t) ∧ p(t)]

Note on `p(t)` (vs the more obvious `p(t_PTS)`): the paper writes p applied
to the outer reference time t, with the convention (paper §4.2.1, sentence
following eq. 25) that "when the imperfective appears beneath the perfect,
t corresponds to the PTS." The IMPF's own λt is bound to t_PTS at composition
time, so beta-reduction yields the equivalent `∃e[t_PTS ⊂ τ(e) ∧ P(e)]` —
see (26) for K&S's own worked composition.

Note on (22b) vs (23b) labeling: both equations are labeled ⟦PERF⟧^g in the
paper. (22b) is K&S's transcription of the standard Iatridou-style XN entry
(no LB); (23b) is K&S's own revision adding an LB existential bounded by the
domain restriction t_r. The variant named `PERF_XN` here in the past was
backwards — fixed to follow K&S's own conventions.

The constraint `t_LB ⊆ t_r` (subset) was previously transcribed as `∈`
(membership). Fixed.

-/

import Linglib.Core.WorldTimeIndex
import Linglib.Core.Time.Interval.Basic
import Linglib.Features.Aktionsart
import Linglib.Semantics.Events.Basic

-- ════════════════════════════════════════════════════
-- § Main Module
-- ════════════════════════════════════════════════════

namespace Semantics.Aspect

open _root_.Core (WorldTimeIndex)
open Core.Time
open Features

-- ════════════════════════════════════════════════════
-- § Core Types
-- ════════════════════════════════════════════════════

/-! Event predicates and the `Event` type are imported from
    `Semantics/Events/Basic.lean` — the unified event ontology.
    Tense-aspect code uses `Event Time` and `W → Event Time → Prop` without
    referencing `.sort` (the field exists for Krifka-style consumers but
    is irrelevant for Klein-style tense composition). -/

/-- Predicate over time intervals (output of IMPF/PRFV). -/
abbrev IntervalPred (W Time : Type*) [LinearOrder Time] := W → Interval Time → Prop

/-- Predicate over time points (output of PERF, input to TENSE).
    Defined as `WorldTimeIndex W Time → Prop` to make the situation structure
    explicit in the tense-aspect pipeline, connecting directly to
    situation semantics (Elbourne, Percus, Kratzer). -/
abbrev PointPred (W Time : Type*) := WorldTimeIndex W Time → Prop

-- ════════════════════════════════════════════════════
-- § Klein's Viewpoint Classification
-- ════════════════════════════════════════════════════

/-- Viewpoint aspect types. [klein-1994] identified imperfective,
    perfective, perfect, and prospective. [smith-1997] added the
    neutral viewpoint (default in the absence of overt aspect morphology). -/
inductive ViewpointType where
  | imperfective  -- TT INCL TSit
  | perfective    -- TT AT TSit
  | perfect       -- TT AFTER TSit
  | prospective   -- TT BEFORE TSit
  | neutral       -- Smith 1997: initial endpoint + internal stages visible, F(e) not visible
  deriving DecidableEq, Repr, Inhabited

/-- Bool-level viewpoint aspect, capturing the perfective/imperfective distinction
    without the full interval-based `Event Time → Prop`/`IntervalPred` machinery.

    Used by `Modal/Ability.lean` (actuality inferences) and
    `Phenomena/ActualityInferences/Data.lean` where the key insight is simply
    "perfective requires actualization, imperfective doesn't." -/
inductive ViewpointAspectB where
  | perfective
  | imperfective
  deriving DecidableEq, Repr, Inhabited

/-- Project `ViewpointType` to the coarser perfective/imperfective distinction.
    Returns `none` for `perfect` and `prospective` (neither is simply perf/impf). -/
def ViewpointType.toBoolAspect : ViewpointType → Option ViewpointAspectB
  | .perfective => some .perfective
  | .imperfective => some .imperfective
  | .perfect | .prospective | .neutral => none

/-- Embed `ViewpointAspectB` back into Klein's full classification. -/
def ViewpointAspectB.toKleinViewpoint : ViewpointAspectB → ViewpointType
  | .perfective => .perfective
  | .imperfective => .imperfective

/-- Roundtrip: embedding then projecting is the identity. -/
theorem toBoolAspect_toKleinViewpoint (a : ViewpointAspectB) :
    a.toKleinViewpoint.toBoolAspect = some a := by cases a <;> rfl

/-- The TT↔TSit interval relation for each viewpoint ([klein-1994]: 108). -/
def ViewpointType.ttTSitRelation {Time : Type*} [LinearOrder Time]
    (v : ViewpointType) (tt tsit : Interval Time) : Prop :=
  match v with
  | .imperfective => tt.properSubinterval tsit
  | .perfective   => tsit.subinterval tt
  | .perfect      => tt.isAfter tsit
  | .prospective  => tt.isBefore tsit
  | .neutral      => tt.initialOverlap tsit

-- ════════════════════════════════════════════════════
-- § Aspect Operators
-- ════════════════════════════════════════════════════

variable {Time : Type*} [LinearOrder Time] {W : Type*}

/-- **IMPERFECTIVE**: reference time properly contained in event runtime.
    [klein-1994]: TT INCL TSit. [knick-sharf-2026] eq. 25. -/
def IMPF (P : W → Event Time → Prop) : IntervalPred W Time :=
  λ w t => ∃ e : Event Time, t.properSubinterval e.τ ∧ P w e

/-- **PERFECTIVE**: event runtime contained in reference time.
    [klein-1994]: TT AT TSit (simplified to TSit ⊆ TT, following [smith-1997]).
    [knick-sharf-2026] eq. 28. -/
def PRFV (P : W → Event Time → Prop) : IntervalPred W Time :=
  λ w t => ∃ e : Event Time, e.τ.subinterval t ∧ P w e

/-- **PROSPECTIVE**: reference time before situation time.
    [klein-1994]: TT BEFORE TSit. -/
def PROSP (P : W → Event Time → Prop) : IntervalPred W Time :=
  λ w t => ∃ e : Event Time, t.isBefore e.τ ∧ P w e

/-- **INIT_OVERLAP**: initial overlap between reference time and event runtime.
    [pancheva-2003] eq. 7b: ⟦NEUTRAL⟧ = λP.λi.∃e[i ∂τ(e) & P(e)]
    The beginning of the eventuality is in the reference interval,
    but the end may extend beyond. Derives experiential perfect readings.

    Renamed from `NEUTRAL` to avoid collision with [smith-1997]'s
    neutral viewpoint (`ViewpointType.neutral`), which is a different concept.
    Pancheva's operator is an inner Asp₂ head; Smith's neutral viewpoint is
    a default viewpoint type. -/
def INIT_OVERLAP (P : W → Event Time → Prop) : IntervalPred W Time :=
  λ w t => ∃ e : Event Time, t.initialOverlap e.τ ∧ P w e


-- ════════════════════════════════════════════════════
-- § Perfect Time Span / Extended Now
-- ════════════════════════════════════════════════════

/-- Right Boundary: PTS finishes at reference time point t. -/
def RB (pts : Interval Time) (t : Time) : Prop := pts.finish = t

/-- Left Boundary: PTS starts at time tLB. -/
def LB (tLB : Time) (pts : Interval Time) : Prop := pts.start = tLB

/-- **PERFECT**: introduces Perfect Time Span.
    [knick-sharf-2026] eq. 22b — the standard XN-theoretic entry
    that K&S start from. Verified against the proceedings PDF.

    K&S notation: `λp_it.λt.∃t_PTS.[RB(t_PTS, t) ∧ p(t)]`. The `p(t)` is
    written by K&S as application to the outer reference time, with the
    composition convention that `t` is bound to `t_PTS` when IMPF appears
    below PERF (paper §4.2.1, sentence after eq. 25). The implementation
    here applies p to `pts` directly (the post-composition meaning), which
    matches K&S's worked composition in their (26). -/
def PERF (p : IntervalPred W Time) : PointPred W Time :=
  λ s => ∃ pts : Interval Time, RB pts s.time ∧ p s.world pts

/-- **PERFECT with Extended Now** (K&S's revision: domain-restricted left
    boundary). [knick-sharf-2026] eq. 23b. Verified against the
    proceedings PDF.

    K&S notation: `λp_it.λt.∃t_PTS.∃t_LB ⊆ tᵣ. [LB(t_LB, t_PTS) ∧
    RB(t_PTS, t) ∧ p(t)]`. The domain restriction tᵣ constrains where the
    LB can be placed; narrow focus on BEEN generates alternatives over tᵣ.

    K&S's (23b) is *not* the standard XN entry — that's their (22b),
    realized here as `PERF`. (23b) is K&S's own revision adding an LB
    existential bounded by the domain restriction. The legacy name
    `PERF_XN` predates this clarification; both `PERF` and `PERF_XN` are
    XN-theoretic, the difference being the LB+domain-restriction.

    Type-level simplification: K&S's `t_LB` is an *initial subinterval* of
    t_PTS (per their 23a), and `t_LB ⊆ t_r` compares two interval-sets.
    The implementation here uses `tLB : Time` (a single point) with
    `∃ tLB ∈ tᵣ` (membership), simplifying K&S's set-theoretic LB to a
    single time witness inside the domain-restriction set. The simpler
    typing is sufficient for the empirical predictions K&S draw and
    avoids carrying intervals at every level. -/
def PERF_XN (p : IntervalPred W Time) (tᵣ : Set Time) : PointPred W Time :=
  λ s => ∃ pts : Interval Time, ∃ tLB ∈ tᵣ,
    LB tLB pts ∧ RB pts s.time ∧ p s.world pts

-- ════════════════════════════════════════════════════
-- § Klein Correspondence
-- ════════════════════════════════════════════════════

/-- IMPF matches Klein's IMPERFECTIVE: ∃e where TT ⊂ TSit. -/
theorem impf_is_klein_imperfective (P : W → Event Time → Prop) (w : W) (t : Interval Time) :
    IMPF P w t ↔ ∃ e, ViewpointType.ttTSitRelation .imperfective t e.τ ∧ P w e := by
  simp only [IMPF, ViewpointType.ttTSitRelation, Event.τ]

/-- PRFV matches Klein's PERFECTIVE: ∃e where TSit ⊆ TT. -/
theorem prfv_is_klein_perfective (P : W → Event Time → Prop) (w : W) (t : Interval Time) :
    PRFV P w t ↔ ∃ e, ViewpointType.ttTSitRelation .perfective t e.τ ∧ P w e := by
  simp only [PRFV, ViewpointType.ttTSitRelation, Event.τ]

-- ════════════════════════════════════════════════════
-- § Compositional Stacking
-- ════════════════════════════════════════════════════

/-- "has been V-ing" = PERF(IMPF(V)). -/
abbrev perfProg (P : W → Event Time → Prop) : PointPred W Time :=
  PERF (IMPF P)

/-- "has V-ed" = PERF(PRFV(V)). -/
abbrev perfSimple (P : W → Event Time → Prop) : PointPred W Time :=
  PERF (PRFV P)

/-- PERF(IMPF(P)) unfolds: ∃ PTS and event, with PTS right-bounded at t,
    the PTS properly inside the event, and P holds of the event. -/
theorem perf_impf_unfold (P : W → Event Time → Prop) (w : W) (t : Time) :
    perfProg P ⟨w, t⟩ ↔
    ∃ pts : Interval Time, ∃ e : Event Time,
      RB pts t ∧ pts.properSubinterval e.τ ∧ P w e := by
  constructor
  · intro ⟨pts, hRB, e, hSub, hP⟩
    exact ⟨pts, e, hRB, hSub, hP⟩
  · intro ⟨pts, e, hRB, hSub, hP⟩
    exact ⟨pts, hRB, e, hSub, hP⟩

/-- PERF(PRFV(P)) unfolds: ∃ PTS and event, with PTS right-bounded at t,
    the event inside the PTS, and P holds of the event. -/
theorem perf_prfv_unfold (P : W → Event Time → Prop) (w : W) (t : Time) :
    perfSimple P ⟨w, t⟩ ↔
    ∃ pts : Interval Time, ∃ e : Event Time,
      RB pts t ∧ e.τ.subinterval pts ∧ P w e := by
  constructor
  · intro ⟨pts, hRB, e, hSub, hP⟩
    exact ⟨pts, e, hRB, hSub, hP⟩
  · intro ⟨pts, e, hRB, hSub, hP⟩
    exact ⟨pts, hRB, e, hSub, hP⟩

-- ════════════════════════════════════════════════════
-- § PERF_XN ↔ PERF
-- ════════════════════════════════════════════════════

/-- Extended Now entails basic perfect (PERF_XN is stronger). -/
theorem perf_xn_entails_perf (p : IntervalPred W Time) (tᵣ : Set Time)
    (w : W) (t : Time) :
    PERF_XN p tᵣ ⟨w, t⟩ → PERF p ⟨w, t⟩ := by
  intro ⟨pts, _tLB, _hmem, _hLB, hRB, hp⟩
  exact ⟨pts, hRB, hp⟩

/-- With maximal domain (Set.univ), PERF_XN collapses to PERF. -/
theorem perf_xn_univ_iff_perf (p : IntervalPred W Time) (w : W) (t : Time) :
    PERF_XN p Set.univ ⟨w, t⟩ ↔ PERF p ⟨w, t⟩ := by
  constructor
  · exact perf_xn_entails_perf p Set.univ w t
  · intro ⟨pts, hRB, hp⟩
    exact ⟨pts, pts.start, Set.mem_univ _, rfl, hRB, hp⟩

/-- Narrower domain restriction is stronger (monotone in tᵣ). -/
theorem perf_xn_monotone (p : IntervalPred W Time) (tᵣ₁ tᵣ₂ : Set Time)
    (hSub : tᵣ₁ ⊆ tᵣ₂) (w : W) (t : Time) :
    PERF_XN p tᵣ₁ ⟨w, t⟩ → PERF_XN p tᵣ₂ ⟨w, t⟩ := by
  intro ⟨pts, tLB, hmem, hLB, hRB, hp⟩
  exact ⟨pts, tLB, hSub hmem, hLB, hRB, hp⟩

-- ════════════════════════════════════════════════════
-- § Entailment Properties
-- ════════════════════════════════════════════════════

/-- IMPF entails an event exists. -/
theorem impf_entails_event (P : W → Event Time → Prop) (w : W) (t : Interval Time) :
    IMPF P w t → ∃ e, P w e :=
  λ ⟨e, _, hP⟩ => ⟨e, hP⟩

/-- PRFV entails an event exists. -/
theorem prfv_entails_event (P : W → Event Time → Prop) (w : W) (t : Interval Time) :
    PRFV P w t → ∃ e, P w e :=
  λ ⟨e, _, hP⟩ => ⟨e, hP⟩

/-- PERF is monotone: p ⊆ q → PERF(p) ⊆ PERF(q). -/
theorem perf_monotone (p q : IntervalPred W Time)
    (h : ∀ w t, p w t → q w t) (w : W) (t : Time) :
    PERF p ⟨w, t⟩ → PERF q ⟨w, t⟩ :=
  λ ⟨pts, hRB, hp⟩ => ⟨pts, hRB, h w pts hp⟩

/-- IMPF and PRFV impose opposite containment directions.
    IMPF: reference ⊂ event runtime. PRFV: event runtime ⊆ reference. -/
theorem impf_prfv_opposite_containment (P : W → Event Time → Prop) (w : W) (t : Interval Time) :
    (IMPF P w t → ∃ e, P w e ∧ t.properSubinterval e.τ) ∧
    (PRFV P w t → ∃ e, P w e ∧ e.τ.subinterval t) :=
  ⟨λ ⟨e, hSub, hP⟩ => ⟨e, hP, hSub⟩,
   λ ⟨e, hSub, hP⟩ => ⟨e, hP, hSub⟩⟩

-- ════════════════════════════════════════════════════
-- § [pancheva-2003]: Higher Aspect and Perfect Types
-- ════════════════════════════════════════════════════

/-! [pancheva-2003] decomposes perfect participles into two aspect heads:
    [T [Asp₁=PERFECT [Asp₂=VIEWPOINT [vP]]]]. The inner Asp₂ (UNBOUNDED,
    INIT_OVERLAP, or BOUNDED) determines the perfect type (universal, experiential,
    or resultative). The outer Asp₁ = PERFECT introduces the PTS via a
    **final subinterval** relation rather than a point-based right boundary. -/

/-- Pancheva's UNBOUNDED (Asp₂): non-strict ⊆ variant of IMPF.
    ⟦UNBOUNDED⟧ = λP.λi.∃e[i ⊆ τ(e) & P(e)] ([pancheva-2003]: 282, eq. 7b).
    Differs from IMPF in using non-strict ⊆ rather than strict ⊂. -/
def UNBOUNDED (P : W → Event Time → Prop) : IntervalPred W Time :=
  λ w t => ∃ e : Event Time, t.subinterval e.τ ∧ P w e

/-- Pancheva's BOUNDED (Asp₂): strict ⊂ variant of PRFV.
    ⟦BOUNDED⟧ = λP.λi.∃e[τ(e) ⊂ i & P(e)] ([pancheva-2003]: 282, eq. 7b).
    Differs from PRFV in using strict ⊂ rather than non-strict ⊆. -/
def BOUNDED (P : W → Event Time → Prop) : IntervalPred W Time :=
  λ w t => ∃ e : Event Time, e.τ.properSubinterval t ∧ P w e

/-- IMPF (strict ⊂) entails UNBOUNDED (non-strict ⊆). -/
theorem impf_entails_unbounded (P : W → Event Time → Prop) (w : W) (t : Interval Time) :
    IMPF P w t → UNBOUNDED P w t :=
  λ ⟨e, hSub, hP⟩ => ⟨e, hSub.1, hP⟩

/-- BOUNDED (strict ⊂) entails PRFV (non-strict ⊆). -/
theorem bounded_entails_prfv (P : W → Event Time → Prop) (w : W) (t : Interval Time) :
    BOUNDED P w t → PRFV P w t :=
  λ ⟨e, hSub, hP⟩ => ⟨e, hSub.1, hP⟩

/-- Pancheva-style interval-level PERFECT (Asp₁).
    ⟦PERFECT⟧ = λp.λi.∃i'[PTS(i', i) & p(i')] ([pancheva-2003]: 284, eq. 9b).
    PTS(i', i) iff i is a final subinterval of i': i ⊆ i' ∧ i.finish = i'.finish. -/
def PERF_P (p : IntervalPred W Time) : IntervalPred W Time :=
  λ w i => ∃ pts : Interval Time, i.finalSubinterval pts ∧ p w pts

/-- Point-based PERF is the special case of interval-based PERF_P
    where the reference interval degenerates to a point [t, t]. -/
theorem perf_p_at_point_iff_perf (p : IntervalPred W Time) (w : W) (t : Time) :
    PERF_P p w (Interval.point t) ↔ PERF p ⟨w, t⟩ := by
  constructor
  · intro ⟨pts, hFin, hp⟩
    exact ⟨pts, hFin.2.symm, hp⟩
  · intro ⟨pts, hRB, hp⟩
    exact ⟨pts, ⟨⟨le_trans pts.valid (le_of_eq hRB), le_of_eq hRB.symm⟩, hRB.symm⟩, hp⟩

/-- PERF_P is monotone: if p entails q, then PERF_P(p) entails PERF_P(q). -/
theorem perf_p_monotone (p q : IntervalPred W Time)
    (h : ∀ w t, p w t → q w t) (w : W) (i : Interval Time) :
    PERF_P p w i → PERF_P q w i :=
  λ ⟨pts, hFin, hp⟩ => ⟨pts, hFin, h w pts hp⟩

/-- [pancheva-2003] perfect type classification.
    The embedded Asp₂ determines the perfect reading:
    - universal = PERFECT(UNBOUNDED): event ongoing throughout PTS
    - experiential = PERFECT(NEUTRAL): event began within PTS
    - resultative = PERFECT(BOUNDED): event completed within PTS
    Note: Pancheva's resultative properly involves a result state relation;
    BOUNDED is a simplification sufficient for the temporal structure. -/
inductive PerfectType where
  | universal     -- PERFECT(UNBOUNDED): ongoing through PTS
  | experiential  -- PERFECT(INIT_OVERLAP): began within PTS
  | resultative   -- PERFECT(BOUNDED): completed within PTS (simplified)
  deriving DecidableEq, Repr

/-- Universal perfect: PERF_P(UNBOUNDED(V)).
    "has been running" — event ongoing throughout PTS.
    [pancheva-2003]: explains why universal reading requires imperfective. -/
abbrev universalPerfect (P : W → Event Time → Prop) : IntervalPred W Time :=
  PERF_P (UNBOUNDED P)

/-- Experiential perfect: PERF_P(INIT_OVERLAP(V)).
    "has visited Paris" — event began within PTS.
    [pancheva-2003]: initial-overlap aspect allows event to extend beyond PTS. -/
abbrev experientialPerfect (P : W → Event Time → Prop) : IntervalPred W Time :=
  PERF_P (INIT_OVERLAP P)

/-- Resultative perfect: PERF_P(BOUNDED(V)).
    "has broken the vase" — event completed within PTS.
    Simplified: properly involves result state ([pancheva-2003]: 288). -/
abbrev resultativePerfect (P : W → Event Time → Prop) : IntervalPred W Time :=
  PERF_P (BOUNDED P)

/-- perfProg at a point entails universalPerfect at that point.
    Since IMPF (strict ⊂) entails UNBOUNDED (non-strict ⊆),
    PERF(IMPF(V)) entails PERF(UNBOUNDED(V)) = universalPerfect. -/
theorem perf_prog_entails_universal_at_point (P : W → Event Time → Prop) (w : W) (t : Time) :
    perfProg P ⟨w, t⟩ → universalPerfect P w (Interval.point t) :=
  λ h => (perf_p_at_point_iff_perf (UNBOUNDED P) w t).mpr
    (perf_monotone (IMPF P) (UNBOUNDED P) (impf_entails_unbounded P) w t h)

-- ════════════════════════════════════════════════════
-- § Bridge to Situation Semantics
-- ════════════════════════════════════════════════════

/-- Evaluate an interval predicate at a point (trivial interval [t, t]).
    Bridge for non-perfect forms. -/
def IntervalPred.atPoint (p : IntervalPred W Time) : PointPred W Time :=
  λ s => p s.world (Interval.point s.time)

end Semantics.Aspect
