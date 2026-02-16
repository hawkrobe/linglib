/-
# Viewpoint Aspect Operators

Klein (1994) viewpoint aspect formalized as interval relations between
Topic Time (TT) and Situation Time (TSit), with compositional operators
following Knick & Sharf (2026).

## Klein's Aspect Definitions (Chapter 6, p. 108)

| # | Relation | Name | Intuition |
|---|----------|------|-----------|
| 1 | TT INCL TSit | IMPERFECTIVE | TT fully inside TSit |
| 2 | TT AT TSit | PERFECTIVE | TSit within/overlapping TT |
| 3a | TT AFTER TSit | PERFECT | TT in posttime of TSit |
| 3b | TT BEFORE TSit | PROSPECTIVE | TT in pretime of TSit |

## Compositional Architecture (Knick & Sharf 2026)

```
EventPred ──[IMPF/PRFV]──▷ IntervalPred ──[PERF]──▷ PointPred ──[TENSE]──▷ Prop
```

Equations (Knick & Sharf 2026):
- (25) ⟦IMPF⟧ = λP.λt.∃e[t ⊂ τ(e) ∧ P(e)]
- (28) ⟦PRFV⟧ = λP.λt.∃e[τ(e) ⊆ t ∧ P(e)]
- (22b) ⟦PERF⟧ = λp.λt.∃tPTS[RB(tPTS, t) ∧ p(tPTS)]
- (23b) ⟦PERF_XN⟧ = λp.λt.∃tPTS.∃tLB ∈ tᵣ[LB(tLB,tPTS) ∧ RB(tPTS,t) ∧ p(tPTS)]

## References

- Klein, W. (1994). Time in Language. Chapter 6.
- Knick, A. & Sharf, M. (2026). On focus and the perfect aspect.
- Smith, C. (1991). The Parameter of Aspect.
- Iatridou, S., Anagnostopoulou, E. & Izvorski, R. (2001).
  Observations about the form and meaning of the Perfect.
- Pancheva, R. (2003). The aspectual makeup of perfect participles.
-/

import Linglib.Core.Time
import Linglib.Theories.Semantics.Lexical.Verb.Aspect

-- ════════════════════════════════════════════════════
-- § Interval Extensions (added to Interval namespace for dot notation)
-- ════════════════════════════════════════════════════

namespace Core.Time.Interval

variable {Time : Type*} [LinearOrder Time]

/-- Proper subinterval: i₁ ⊆ i₂ with at least one strict boundary.
    Required for IMPF: reference time PROPERLY inside event runtime. -/
def properSubinterval (i₁ i₂ : Interval Time) : Prop :=
  i₁.subinterval i₂ ∧ (i₂.start < i₁.start ∨ i₁.finish < i₂.finish)

/-- i₁ is entirely after i₂ (i₁ starts at or after i₂ finishes). -/
def isAfter (i₁ i₂ : Interval Time) : Prop :=
  i₂.finish ≤ i₁.start

/-- i₁ is entirely before i₂. -/
def isBefore (i₁ i₂ : Interval Time) : Prop :=
  i₁.finish ≤ i₂.start

theorem properSub_implies_sub (i₁ i₂ : Interval Time)
    (h : i₁.properSubinterval i₂) : i₁.subinterval i₂ :=
  h.1

theorem subinterval_refl (i : Interval Time) : i.subinterval i :=
  ⟨le_refl _, le_refl _⟩

/-- No interval is properly contained in itself. -/
theorem properSubinterval_irrefl (i : Interval Time) :
    ¬ i.properSubinterval i := by
  intro ⟨_, h⟩
  cases h with
  | inl h => exact lt_irrefl _ h
  | inr h => exact lt_irrefl _ h

theorem isAfter_iff_isBefore (i₁ i₂ : Interval Time) :
    i₁.isAfter i₂ ↔ i₂.isBefore i₁ :=
  Iff.rfl

/-- Final subinterval: i₁ ⊆ i₂ and they share the same right endpoint.
    Pancheva (2003): PTS(i', i) iff i is a final subinterval of i'. -/
def finalSubinterval (i₁ i₂ : Interval Time) : Prop :=
  i₁.subinterval i₂ ∧ i₁.finish = i₂.finish

/-- Initial overlap (∂): i₁ and i₂ overlap, and the start of i₂ is in i₁.
    Pancheva (2003): i ∂τ(e) — the beginning of the eventuality is included
    in the reference interval but the end may not be.
    Used for NEUTRAL viewpoint aspect. -/
def initialOverlap (i₁ i₂ : Interval Time) : Prop :=
  i₁.overlaps i₂ ∧ i₁.contains i₂.start

/-- Final subinterval implies subinterval. -/
theorem finalSub_implies_sub (i₁ i₂ : Interval Time)
    (h : i₁.finalSubinterval i₂) : i₁.subinterval i₂ :=
  h.1

/-- Every interval is a final subinterval of itself. -/
theorem finalSubinterval_refl (i : Interval Time) : i.finalSubinterval i :=
  ⟨subinterval_refl i, rfl⟩

end Core.Time.Interval

-- ════════════════════════════════════════════════════
-- § Main Module
-- ════════════════════════════════════════════════════

namespace Semantics.Lexical.Verb.ViewpointAspect

open Core.Time
open Semantics.Lexical.Verb.Aspect

-- ════════════════════════════════════════════════════
-- § Core Types
-- ════════════════════════════════════════════════════

/-- An eventuality with interval-valued runtime (Davidson 1967, Krifka 1989).
    Unlike `Situation` (point-valued τ), eventualities occupy temporal intervals. -/
structure Eventuality (Time : Type*) [LE Time] where
  /-- The temporal extent of this eventuality -/
  runtime : Interval Time

/-- Temporal trace: the runtime interval of an eventuality. -/
@[simp]
def Eventuality.τ {Time : Type*} [LE Time] (e : Eventuality Time) : Interval Time :=
  e.runtime

/-- Predicate over eventualities (VP denotations). -/
abbrev EventPred (W Time : Type*) [LE Time] := W → Eventuality Time → Prop

/-- Predicate over time intervals (output of IMPF/PRFV). -/
abbrev IntervalPred (W Time : Type*) [LE Time] := W → Interval Time → Prop

/-- Predicate over time points (output of PERF, input to TENSE). -/
abbrev PointPred (W Time : Type*) := W → Time → Prop

-- ════════════════════════════════════════════════════
-- § Klein's Viewpoint Classification
-- ════════════════════════════════════════════════════

/-- Klein's (1994: 108) viewpoint aspect types. -/
inductive ViewpointType where
  | imperfective  -- TT INCL TSit
  | perfective    -- TT AT TSit
  | perfect       -- TT AFTER TSit
  | prospective   -- TT BEFORE TSit
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Bool-level viewpoint aspect, capturing the perfective/imperfective distinction
    without the full interval-based `EventPred`/`IntervalPred` machinery.

    Used by `Modal/Ability.lean` (actuality inferences) and
    `Phenomena/ActualityInferences/Data.lean` where the key insight is simply
    "perfective requires actualization, imperfective doesn't." -/
inductive ViewpointAspectB where
  | perfective
  | imperfective
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Project `ViewpointType` to the coarser perfective/imperfective distinction.
    Returns `none` for `perfect` and `prospective` (neither is simply perf/impf). -/
def ViewpointType.toBoolAspect : ViewpointType → Option ViewpointAspectB
  | .perfective => some .perfective
  | .imperfective => some .imperfective
  | .perfect | .prospective => none

/-- Embed `ViewpointAspectB` back into Klein's full classification. -/
def ViewpointAspectB.toKleinViewpoint : ViewpointAspectB → ViewpointType
  | .perfective => .perfective
  | .imperfective => .imperfective

/-- Roundtrip: embedding then projecting is the identity. -/
theorem toBoolAspect_toKleinViewpoint (a : ViewpointAspectB) :
    a.toKleinViewpoint.toBoolAspect = some a := by cases a <;> rfl

/-- The TT↔TSit interval relation for each viewpoint (Klein 1994: 108). -/
def ViewpointType.ttTSitRelation {Time : Type*} [LinearOrder Time]
    (v : ViewpointType) (tt tsit : Interval Time) : Prop :=
  match v with
  | .imperfective => tt.properSubinterval tsit
  | .perfective   => tsit.subinterval tt
  | .perfect      => tt.isAfter tsit
  | .prospective  => tt.isBefore tsit

-- ════════════════════════════════════════════════════
-- § Aspect Operators
-- ════════════════════════════════════════════════════

variable {Time : Type*} [LinearOrder Time] {W : Type*}

/-- **IMPERFECTIVE**: reference time properly contained in event runtime.
    Klein (1994): TT INCL TSit. Knick & Sharf (2026) eq. 25. -/
def IMPF (P : EventPred W Time) : IntervalPred W Time :=
  λ w t => ∃ e : Eventuality Time, t.properSubinterval e.τ ∧ P w e

/-- **PERFECTIVE**: event runtime contained in reference time.
    Klein (1994): TT AT TSit (simplified to TSit ⊆ TT, following Smith 1991).
    Knick & Sharf (2026) eq. 28. -/
def PRFV (P : EventPred W Time) : IntervalPred W Time :=
  λ w t => ∃ e : Eventuality Time, e.τ.subinterval t ∧ P w e

/-- **PROSPECTIVE**: reference time before situation time.
    Klein (1994): TT BEFORE TSit. -/
def PROSP (P : EventPred W Time) : IntervalPred W Time :=
  λ w t => ∃ e : Eventuality Time, t.isBefore e.τ ∧ P w e

/-- **NEUTRAL**: initial overlap between reference time and event runtime.
    Pancheva (2003) eq. 7b: ⟦NEUTRAL⟧ = λP.λi.∃e[i ∂τ(e) & P(e)]
    The beginning of the eventuality is in the reference interval,
    but the end may extend beyond. Derives Experiential perfect readings. -/
def NEUTRAL (P : EventPred W Time) : IntervalPred W Time :=
  λ w t => ∃ e : Eventuality Time, t.initialOverlap e.τ ∧ P w e

-- ════════════════════════════════════════════════════
-- § Perfect Time Span / Extended Now
-- ════════════════════════════════════════════════════

/-- Right Boundary: PTS finishes at reference time point t. -/
def RB (pts : Interval Time) (t : Time) : Prop := pts.finish = t

/-- Left Boundary: PTS starts at time tLB. -/
def LB (tLB : Time) (pts : Interval Time) : Prop := pts.start = tLB

/-- **PERFECT**: introduces Perfect Time Span.
    Knick & Sharf (2026) eq. 22b. -/
def PERF (p : IntervalPred W Time) : PointPred W Time :=
  λ w t => ∃ pts : Interval Time, RB pts t ∧ p w pts

/-- **PERFECT with Extended Now** (domain-restricted left boundary).
    Knick & Sharf (2026) eq. 23b.
    The domain restriction tᵣ constrains where the LB can be placed.
    Narrow focus on BEEN generates alternatives over tᵣ. -/
def PERF_XN (p : IntervalPred W Time) (tᵣ : Set Time) : PointPred W Time :=
  λ w t => ∃ pts : Interval Time, ∃ tLB ∈ tᵣ,
    LB tLB pts ∧ RB pts t ∧ p w pts

-- ════════════════════════════════════════════════════
-- § Klein Correspondence
-- ════════════════════════════════════════════════════

/-- IMPF matches Klein's IMPERFECTIVE: ∃e where TT ⊂ TSit. -/
theorem impf_is_klein_imperfective (P : EventPred W Time) (w : W) (t : Interval Time) :
    IMPF P w t ↔ ∃ e, ViewpointType.ttTSitRelation .imperfective t e.τ ∧ P w e := by
  simp only [IMPF, ViewpointType.ttTSitRelation, Eventuality.τ]

/-- PRFV matches Klein's PERFECTIVE: ∃e where TSit ⊆ TT. -/
theorem prfv_is_klein_perfective (P : EventPred W Time) (w : W) (t : Interval Time) :
    PRFV P w t ↔ ∃ e, ViewpointType.ttTSitRelation .perfective t e.τ ∧ P w e := by
  simp only [PRFV, ViewpointType.ttTSitRelation, Eventuality.τ]

-- ════════════════════════════════════════════════════
-- § Compositional Stacking
-- ════════════════════════════════════════════════════

/-- "has been V-ing" = PERF(IMPF(V)). -/
abbrev perfProg (P : EventPred W Time) : PointPred W Time :=
  PERF (IMPF P)

/-- "has V-ed" = PERF(PRFV(V)). -/
abbrev perfSimple (P : EventPred W Time) : PointPred W Time :=
  PERF (PRFV P)

/-- PERF(IMPF(P)) unfolds: ∃ PTS and event, with PTS right-bounded at t,
    the PTS properly inside the event, and P holds of the event. -/
theorem perf_impf_unfold (P : EventPred W Time) (w : W) (t : Time) :
    perfProg P w t ↔
    ∃ pts : Interval Time, ∃ e : Eventuality Time,
      RB pts t ∧ pts.properSubinterval e.τ ∧ P w e := by
  constructor
  · intro ⟨pts, hRB, e, hSub, hP⟩
    exact ⟨pts, e, hRB, hSub, hP⟩
  · intro ⟨pts, e, hRB, hSub, hP⟩
    exact ⟨pts, hRB, e, hSub, hP⟩

/-- PERF(PRFV(P)) unfolds: ∃ PTS and event, with PTS right-bounded at t,
    the event inside the PTS, and P holds of the event. -/
theorem perf_prfv_unfold (P : EventPred W Time) (w : W) (t : Time) :
    perfSimple P w t ↔
    ∃ pts : Interval Time, ∃ e : Eventuality Time,
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
    PERF_XN p tᵣ w t → PERF p w t := by
  intro ⟨pts, _tLB, _hmem, _hLB, hRB, hp⟩
  exact ⟨pts, hRB, hp⟩

/-- With maximal domain (Set.univ), PERF_XN collapses to PERF. -/
theorem perf_xn_univ_iff_perf (p : IntervalPred W Time) (w : W) (t : Time) :
    PERF_XN p Set.univ w t ↔ PERF p w t := by
  constructor
  · exact perf_xn_entails_perf p Set.univ w t
  · intro ⟨pts, hRB, hp⟩
    exact ⟨pts, pts.start, Set.mem_univ _, rfl, hRB, hp⟩

/-- Narrower domain restriction is stronger (monotone in tᵣ). -/
theorem perf_xn_monotone (p : IntervalPred W Time) (tᵣ₁ tᵣ₂ : Set Time)
    (hSub : tᵣ₁ ⊆ tᵣ₂) (w : W) (t : Time) :
    PERF_XN p tᵣ₁ w t → PERF_XN p tᵣ₂ w t := by
  intro ⟨pts, tLB, hmem, hLB, hRB, hp⟩
  exact ⟨pts, tLB, hSub hmem, hLB, hRB, hp⟩

-- ════════════════════════════════════════════════════
-- § Vendler Class Compatibility
-- ════════════════════════════════════════════════════

end Semantics.Lexical.Verb.ViewpointAspect

namespace Semantics.Lexical.Verb.Aspect

/-- States and activities naturally pair with IMPF (homogeneous). -/
def VendlerClass.naturallyImperfective : VendlerClass → Bool
  | .state | .activity => true
  | .achievement | .accomplishment => false

/-- Achievements and accomplishments naturally pair with PRFV (telic). -/
def VendlerClass.naturallyPerfective : VendlerClass → Bool
  | .state | .activity => false
  | .achievement | .accomplishment => true

end Semantics.Lexical.Verb.Aspect

namespace Semantics.Lexical.Verb.ViewpointAspect

open Core.Time
open Semantics.Lexical.Verb.Aspect

variable {Time : Type*} [LinearOrder Time] {W : Type*}

/-- Natural imperfectivity = homogeneity (subinterval property). -/
theorem naturally_imperfective_iff_homogeneous (c : VendlerClass) :
    c.naturallyImperfective = c.toProfile.isHomogeneous := by
  cases c <;> rfl

/-- Natural perfectivity = telicity. -/
theorem naturally_perfective_iff_telic (c : VendlerClass) :
    c.naturallyPerfective = (c.telicity == .telic) := by
  cases c <;> rfl

-- ════════════════════════════════════════════════════
-- § Entailment Properties
-- ════════════════════════════════════════════════════

/-- IMPF entails an event exists. -/
theorem impf_entails_event (P : EventPred W Time) (w : W) (t : Interval Time) :
    IMPF P w t → ∃ e, P w e :=
  λ ⟨e, _, hP⟩ => ⟨e, hP⟩

/-- PRFV entails an event exists. -/
theorem prfv_entails_event (P : EventPred W Time) (w : W) (t : Interval Time) :
    PRFV P w t → ∃ e, P w e :=
  λ ⟨e, _, hP⟩ => ⟨e, hP⟩

/-- PERF is monotone: p ⊆ q → PERF(p) ⊆ PERF(q). -/
theorem perf_monotone (p q : IntervalPred W Time)
    (h : ∀ w t, p w t → q w t) (w : W) (t : Time) :
    PERF p w t → PERF q w t :=
  λ ⟨pts, hRB, hp⟩ => ⟨pts, hRB, h w pts hp⟩

/-- IMPF and PRFV impose opposite containment directions.
    IMPF: reference ⊂ event runtime. PRFV: event runtime ⊆ reference. -/
theorem impf_prfv_opposite_containment (P : EventPred W Time) (w : W) (t : Interval Time) :
    (IMPF P w t → ∃ e, P w e ∧ t.properSubinterval e.τ) ∧
    (PRFV P w t → ∃ e, P w e ∧ e.τ.subinterval t) :=
  ⟨λ ⟨e, hSub, hP⟩ => ⟨e, hP, hSub⟩,
   λ ⟨e, hSub, hP⟩ => ⟨e, hP, hSub⟩⟩

-- ════════════════════════════════════════════════════
-- § Pancheva (2003): Higher Aspect and Perfect Types
-- ════════════════════════════════════════════════════

/-! Pancheva (2003) decomposes perfect participles into two aspect heads:
    [T [Asp₁=PERFECT [Asp₂=VIEWPOINT [vP]]]]. The inner Asp₂ (UNBOUNDED,
    NEUTRAL, or BOUNDED) determines the perfect type (universal, experiential,
    or resultative). The outer Asp₁ = PERFECT introduces the PTS via a
    **final subinterval** relation rather than a point-based right boundary. -/

/-- Pancheva's UNBOUNDED (Asp₂): non-strict ⊆ variant of IMPF.
    ⟦UNBOUNDED⟧ = λP.λi.∃e[i ⊆ τ(e) & P(e)] (Pancheva 2003: 282, eq. 7b).
    Differs from IMPF in using non-strict ⊆ rather than strict ⊂. -/
def UNBOUNDED (P : EventPred W Time) : IntervalPred W Time :=
  λ w t => ∃ e : Eventuality Time, t.subinterval e.τ ∧ P w e

/-- Pancheva's BOUNDED (Asp₂): strict ⊂ variant of PRFV.
    ⟦BOUNDED⟧ = λP.λi.∃e[τ(e) ⊂ i & P(e)] (Pancheva 2003: 282, eq. 7b).
    Differs from PRFV in using strict ⊂ rather than non-strict ⊆. -/
def BOUNDED (P : EventPred W Time) : IntervalPred W Time :=
  λ w t => ∃ e : Eventuality Time, e.τ.properSubinterval t ∧ P w e

/-- IMPF (strict ⊂) entails UNBOUNDED (non-strict ⊆). -/
theorem impf_entails_unbounded (P : EventPred W Time) (w : W) (t : Interval Time) :
    IMPF P w t → UNBOUNDED P w t :=
  λ ⟨e, hSub, hP⟩ => ⟨e, hSub.1, hP⟩

/-- BOUNDED (strict ⊂) entails PRFV (non-strict ⊆). -/
theorem bounded_entails_prfv (P : EventPred W Time) (w : W) (t : Interval Time) :
    BOUNDED P w t → PRFV P w t :=
  λ ⟨e, hSub, hP⟩ => ⟨e, hSub.1, hP⟩

/-- Pancheva-style interval-level PERFECT (Asp₁).
    ⟦PERFECT⟧ = λp.λi.∃i'[PTS(i', i) & p(i')] (Pancheva 2003: 284, eq. 9b).
    PTS(i', i) iff i is a final subinterval of i': i ⊆ i' ∧ i.finish = i'.finish. -/
def PERF_P (p : IntervalPred W Time) : IntervalPred W Time :=
  λ w i => ∃ pts : Interval Time, i.finalSubinterval pts ∧ p w pts

/-- Point-based PERF is the special case of interval-based PERF_P
    where the reference interval degenerates to a point [t, t]. -/
theorem perf_p_at_point_iff_perf (p : IntervalPred W Time) (w : W) (t : Time) :
    PERF_P p w (Interval.point t) ↔ PERF p w t := by
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

/-- Pancheva (2003) perfect type classification.
    The embedded Asp₂ determines the perfect reading:
    - universal = PERFECT(UNBOUNDED): event ongoing throughout PTS
    - experiential = PERFECT(NEUTRAL): event began within PTS
    - resultative = PERFECT(BOUNDED): event completed within PTS
    Note: Pancheva's resultative properly involves a result state relation;
    BOUNDED is a simplification sufficient for the temporal structure. -/
inductive PerfectType where
  | universal     -- PERFECT(UNBOUNDED): ongoing through PTS
  | experiential  -- PERFECT(NEUTRAL): began within PTS
  | resultative   -- PERFECT(BOUNDED): completed within PTS (simplified)
  deriving DecidableEq, Repr, BEq

/-- Universal perfect: PERF_P(UNBOUNDED(V)).
    "has been running" — event ongoing throughout PTS.
    Pancheva (2003: 285): explains why universal reading requires imperfective. -/
abbrev universalPerfect (P : EventPred W Time) : IntervalPred W Time :=
  PERF_P (UNBOUNDED P)

/-- Experiential perfect: PERF_P(NEUTRAL(V)).
    "has visited Paris" — event began within PTS.
    Pancheva (2003: 287): neutral aspect allows event to extend beyond PTS. -/
abbrev experientialPerfect (P : EventPred W Time) : IntervalPred W Time :=
  PERF_P (NEUTRAL P)

/-- Resultative perfect: PERF_P(BOUNDED(V)).
    "has broken the vase" — event completed within PTS.
    Simplified: properly involves result state (Pancheva 2003: 288). -/
abbrev resultativePerfect (P : EventPred W Time) : IntervalPred W Time :=
  PERF_P (BOUNDED P)

/-- perfProg at a point entails universalPerfect at that point.
    Since IMPF (strict ⊂) entails UNBOUNDED (non-strict ⊆),
    PERF(IMPF(V)) entails PERF(UNBOUNDED(V)) = universalPerfect. -/
theorem perf_prog_entails_universal_at_point (P : EventPred W Time) (w : W) (t : Time) :
    perfProg P w t → universalPerfect P w (Interval.point t) :=
  λ h => (perf_p_at_point_iff_perf (UNBOUNDED P) w t).mpr
    (perf_monotone (IMPF P) (UNBOUNDED P) (impf_entails_unbounded P) w t h)

-- ════════════════════════════════════════════════════
-- § Bridge to Situation Semantics
-- ════════════════════════════════════════════════════

/-- Evaluate an interval predicate at a point (trivial interval [t, t]).
    Bridge for non-perfect forms. -/
def IntervalPred.atPoint (p : IntervalPred W Time) : PointPred W Time :=
  λ w t => p w (Interval.point t)

/-- Lift a point predicate to Situation (for tense operator compatibility). -/
def PointPred.toSitProp (p : PointPred W Time) : Situation W Time → Prop :=
  λ s => p s.world s.time

end Semantics.Lexical.Verb.ViewpointAspect
