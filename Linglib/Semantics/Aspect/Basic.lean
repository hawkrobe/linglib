import Linglib.Semantics.Reference.Context.Index
import Linglib.Core.Order.Interval
import Linglib.Semantics.Events.Basic

/-!
# Aspect

This file is the root of the aspect API: situation type and viewpoint, the two components of
[smith-1997]. Situation type is the lexical classification of an eventuality by the three binary
features telicity, duration and dynamicity (`Telicity`, `Duration`, `Dynamicity`, bundled as an
`AspectualProfile`), projected onto the five classes of [vendler-1957] and [smith-1997]
(`VendlerClass`), with the aspectual shifts of compositional coercion (`AspectualProfile.telicize`
and its siblings) and the adverbial and progressive diagnostics of [dowty-1979] derived from the
features (`forXPrediction`, `inXPrediction`, `progressivePrediction`). Viewpoint aspect follows
[klein-1994]: a viewpoint relates Topic Time to Situation Time (`ViewpointType`), and the
compositional operators of [knick-sharf-2026] take an event predicate to an interval predicate
(`IMPF`, `PRFV`, `PROSP`), an interval predicate to a point predicate (`PERF`, `PERF_XN`), and
on to tense.

## Implementation notes

* Klein's four relations: TT INCL TSit is the imperfective, TT AT TSit the perfective, TT AFTER
  TSit the perfect and TT BEFORE TSit the prospective.
* The operator equations follow [knick-sharf-2026]: IMPF is λP λt ∃e, t ⊂ τ(e) ∧ P e; PRFV is
  λP λt ∃e, τ(e) ⊆ t ∧ P e; the standard extended-now PERF is λp λt ∃t_PTS, RB t_PTS t ∧ p t,
  and the paper's revision adds a left boundary drawn from a domain restriction tᵣ,
  λp λt ∃t_PTS ∃t_LB ⊆ tᵣ, LB t_LB t_PTS ∧ RB t_PTS t ∧ p t. The predicate applies to the outer
  reference time, under the paper's convention that beneath the perfect it corresponds to the
  perfect time span.
* `Event T` and event predicates come from `Semantics/Events/Basic.lean`; tense-aspect
  composition does not reference the event sort.

## References

* [smith-1997]
* [vendler-1957]
* [dowty-1979]
* [klein-1994]
* [knick-sharf-2026]
* [pancheva-2003]
-/

namespace Aspect

open Semantics.Context (Index)

/-! ### Situation type -/

/-- Whether an eventuality has a natural endpoint. -/
inductive Telicity
  | telic
  | atelic
  deriving DecidableEq, Repr, Inhabited

/-- Whether an eventuality takes time or is instantaneous. -/
inductive Duration
  | durative
  | punctual
  deriving DecidableEq, Repr, Inhabited

/-- Whether an eventuality involves change. -/
inductive Dynamicity
  | dynamic
  | stative
  deriving DecidableEq, Repr, Inhabited

/-- The five situation types: the four classes of [vendler-1957] and the semelfactives of
[smith-1997]. -/
inductive VendlerClass
  | state
  | activity
  | achievement
  | accomplishment
  | semelfactive
  deriving DecidableEq, Repr, Inhabited

namespace VendlerClass

/-- The telicity of a situation type. -/
def telicity : VendlerClass → Telicity
  | state | activity | semelfactive => .atelic
  | achievement | accomplishment => .telic

/-- The duration of a situation type. -/
def duration : VendlerClass → Duration
  | state | activity | accomplishment => .durative
  | achievement | semelfactive => .punctual

/-- The dynamicity of a situation type. -/
def dynamicity : VendlerClass → Dynamicity
  | state => .stative
  | activity | achievement | accomplishment | semelfactive => .dynamic

end VendlerClass

/-- The three features of a situation type, bundled. -/
structure AspectualProfile where
  telicity : Telicity
  duration : Duration
  dynamicity : Dynamicity
  deriving DecidableEq, Repr

namespace AspectualProfile

/-- The situation type of a profile. -/
@[simp] def toVendlerClass (p : AspectualProfile) : VendlerClass :=
  match p.dynamicity, p.duration, p.telicity with
  | .stative, _, _ => .state
  | .dynamic, .durative, .atelic => .activity
  | .dynamic, .punctual, .telic => .achievement
  | .dynamic, .durative, .telic => .accomplishment
  | .dynamic, .punctual, .atelic => .semelfactive

/-- Add a natural endpoint. -/
def telicize (p : AspectualProfile) : AspectualProfile := { p with telicity := .telic }

/-- Remove the natural endpoint, the effect of the progressive. -/
def atelicize (p : AspectualProfile) : AspectualProfile := { p with telicity := .atelic }

/-- Stretch a punctual eventuality over time, the iterative reading. -/
def duratize (p : AspectualProfile) : AspectualProfile := { p with duration := .durative }

/-- Read as a state. -/
def statify (p : AspectualProfile) : AspectualProfile := { p with dynamicity := .stative }

end AspectualProfile

/-- The canonical profile of a situation type. -/
@[simp] def VendlerClass.toProfile (c : VendlerClass) : AspectualProfile :=
  ⟨c.telicity, c.duration, c.dynamicity⟩

/-- The canonical profile of a state. -/
def stateProfile : AspectualProfile := ⟨.atelic, .durative, .stative⟩

/-- The canonical profile of an activity. -/
def activityProfile : AspectualProfile := ⟨.atelic, .durative, .dynamic⟩

/-- The canonical profile of an achievement. -/
def achievementProfile : AspectualProfile := ⟨.telic, .punctual, .dynamic⟩

/-- The canonical profile of an accomplishment. -/
def accomplishmentProfile : AspectualProfile := ⟨.telic, .durative, .dynamic⟩

/-- The canonical profile of a semelfactive. -/
def semelfactiveProfile : AspectualProfile := ⟨.atelic, .punctual, .dynamic⟩

@[simp] theorem VendlerClass.toProfile_toVendlerClass (c : VendlerClass) :
    c.toProfile.toVendlerClass = c := by
  cases c <;> rfl

/-- Telicizing an activity gives an accomplishment. -/
theorem telicize_activity : activityProfile.telicize.toVendlerClass = .accomplishment := rfl

/-- Duratizing a semelfactive gives an activity, the iterative reading. -/
theorem duratize_semelfactive : semelfactiveProfile.duratize.toVendlerClass = .activity := rfl

/-! ### Diagnostics

The adverbial and progressive tests of [dowty-1979], as functions of the three features: a
*for*-adverbial measures an atelic durative eventuality and coerces a telic or punctual one into
repetition or iteration; an *in*-adverbial needs a culmination; the progressive needs internal
stages, reads an achievement through its preliminary stages and a semelfactive as iterated. -/

/-- The outcome of a diagnostic: acceptable, unacceptable, degraded, or acceptable under a
meaning shift. -/
inductive DiagnosticResult
  | accept
  | reject
  | marginal
  | coerced
  deriving DecidableEq, Repr

/-- The *for*-adverbial test. -/
def forXPrediction (c : VendlerClass) : DiagnosticResult :=
  match c.telicity, c.duration with
  | .atelic, .durative => .accept
  | .telic, .punctual => .reject
  | _, _ => .coerced

/-- The *in*-adverbial test. -/
def inXPrediction (c : VendlerClass) : DiagnosticResult :=
  if c.telicity = .telic then .accept else .reject

/-- The progressive test. -/
def progressivePrediction (c : VendlerClass) : DiagnosticResult :=
  match c.dynamicity, c.duration, c.telicity with
  | .stative, _, _ => .reject
  | .dynamic, .durative, _ => .accept
  | .dynamic, .punctual, .telic => .marginal
  | .dynamic, .punctual, .atelic => .coerced

theorem inXPrediction_eq_accept_iff (c : VendlerClass) :
    inXPrediction c = .accept ↔ c.telicity = .telic := by
  cases c <;> decide

theorem forXPrediction_eq_accept_iff (c : VendlerClass) :
    forXPrediction c = .accept ↔ c.telicity = .atelic ∧ c.duration = .durative := by
  cases c <;> decide

theorem progressivePrediction_eq_accept_iff (c : VendlerClass) :
    progressivePrediction c = .accept ↔ c.duration = .durative ∧ c.dynamicity = .dynamic := by
  cases c <;> decide

-- ════════════════════════════════════════════════════
-- § Core Types
-- ════════════════════════════════════════════════════

/-! Event predicates and the `Event` type are imported from
    `Semantics/Events/Basic.lean` — the unified event ontology.
    Tense-aspect code uses `Event T` and `W → Event T → Prop` without
    referencing `.sort` (the field exists for Krifka-style consumers but
    is irrelevant for Klein-style tense composition). -/

/-- Predicate over time intervals (output of IMPF/PRFV). -/
abbrev IntervalPred (W T : Type*) [LinearOrder T] := W → NonemptyInterval T → Prop

/-- Predicate over time points (output of PERF, input to TENSE).
    Defined as `Index W T → Prop` to make the situation structure
    explicit in the tense-aspect pipeline, connecting directly to
    situation semantics (Elbourne, Percus, Kratzer). -/
abbrev PointPred (W T : Type*) := Index W T → Prop

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

/-- The perfective / imperfective opposition — viewpoint aspect at its
    coarsest, without the interval-based `Event T → Prop`/`IntervalPred`
    machinery of Klein's full classification (`ViewpointType`). The right
    granularity where the key fact is simply "perfective requires
    actualization, imperfective doesn't", or where the opposition is
    lexically encoded (`Verb.Stem`). -/
inductive Perfectivity where
  | perfective
  | imperfective
  deriving DecidableEq, Repr, Inhabited

/-- Project `ViewpointType` to the coarser perfective/imperfective distinction.
    Returns `none` for `perfect` and `prospective` (neither is simply perf/impf). -/
def ViewpointType.toPerfectivity : ViewpointType → Option Perfectivity
  | .perfective => some .perfective
  | .imperfective => some .imperfective
  | .perfect | .prospective | .neutral => none

/-- Embed `Perfectivity` back into Klein's full classification. -/
def Perfectivity.toKleinViewpoint : Perfectivity → ViewpointType
  | .perfective => .perfective
  | .imperfective => .imperfective

/-- Roundtrip: embedding then projecting is the identity. -/
theorem toPerfectivity_toKleinViewpoint (a : Perfectivity) :
    a.toKleinViewpoint.toPerfectivity = some a := by cases a <;> rfl

/-- The TT↔TSit interval relation for each viewpoint ([klein-1994]: 108). -/
def ViewpointType.ttTSitRelation {T : Type*} [LinearOrder T]
    (v : ViewpointType) (tt tsit : NonemptyInterval T) : Prop :=
  match v with
  | .imperfective => tt < tsit
  | .perfective   => tsit ≤ tt
  | .perfect      => tt.isAfter tsit
  | .prospective  => tt.isBefore tsit
  | .neutral      => tt.initialOverlap tsit

instance {T : Type*} [LinearOrder T] (v : ViewpointType) (tt tsit : NonemptyInterval T) :
    Decidable (v.ttTSitRelation tt tsit) := by
  cases v <;> unfold ViewpointType.ttTSitRelation <;> infer_instance

/-! ### Visibility properties of viewpoints

[smith-1997] §4.1 tabulates four visibility properties per viewpoint: whether
the initial point of the situation is asserted, whether the final point is
asserted, whether the viewpoint presents the situation as informationally
closed, and whether the viewpoint can focus an interval strictly inside the
situation (the structural source of the imperfective's "preliminary stages"
reading for punctuals, §4.2.2). Each property derives from `ttTSitRelation`:
visibility is interval geometry, and Smith's Table 1 re-emerges below as
iff theorems, not as a stipulated lookup. -/

/-- The viewpoint asserts the situation's initial point: every licensed
    (`tt`, `tsit`) pair has `tt` containing `tsit.fst`. -/
def ViewpointType.ShowsInitialPoint (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.fst ∈ tt

/-- The viewpoint asserts the situation's final point. -/
def ViewpointType.ShowsFinalPoint (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.snd ∈ tt

/-- The viewpoint presents the situation as informationally closed: the
    topic time reaches at least the situation time's right endpoint. -/
def ViewpointType.IsClosed (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.snd ≤ tt.snd

/-- The viewpoint focuses a topic time strictly inside the situation, the
    structural source of the imperfective's "preliminary stages" reading
    for punctual events ([smith-1997] §4.2.2). -/
def ViewpointType.FocusesPreliminaryStages (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tt < tsit

namespace ViewpointType

/-- Construct `ttTSitRelation v tt tsit` for a concrete `NonemptyInterval ℤ` pair using
    `refine ⟨...⟩ <;> show _ <;> omega`. Each viewpoint's witness comes from
    the underlying interval relation. -/
private theorem rel_imperfective :
    ttTSitRelation .imperfective (⟨⟨1, 2⟩, by omega⟩ : NonemptyInterval ℤ) ⟨⟨0, 3⟩, by omega⟩ := by decide

private theorem rel_perfect :
    ttTSitRelation .perfect (⟨⟨3, 4⟩, by omega⟩ : NonemptyInterval ℤ) ⟨⟨0, 2⟩, by omega⟩ := by decide

private theorem rel_prospective :
    ttTSitRelation .prospective (⟨⟨0, 1⟩, by omega⟩ : NonemptyInterval ℤ) ⟨⟨2, 3⟩, by omega⟩ := by decide

private theorem rel_neutral_short :
    ttTSitRelation .neutral (⟨⟨0, 1⟩, by omega⟩ : NonemptyInterval ℤ) ⟨⟨0, 5⟩, by omega⟩ := by decide

private theorem rel_neutral_wide :
    ttTSitRelation .neutral (⟨⟨0, 10⟩, by omega⟩ : NonemptyInterval ℤ) ⟨⟨0, 5⟩, by omega⟩ := by decide

private theorem rel_perfective_refl :
    ttTSitRelation .perfective (⟨⟨0, 1⟩, by omega⟩ : NonemptyInterval ℤ) ⟨⟨0, 1⟩, by omega⟩ := by decide

/-- [smith-1997] Table 1, IP column: only perfective and neutral assert the initial point. -/
theorem showsInitialPoint_iff (v : ViewpointType) :
    v.ShowsInitialPoint ↔ v = .perfective ∨ v = .neutral := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | perfective => exact Or.inl rfl
    | neutral => exact Or.inr rfl
    | imperfective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_imperfective
        have : (1 : ℤ) ≤ 0 := hC.1
        omega
    | perfect =>
        exfalso
        have hC := @h ℤ _ _ _ rel_perfect
        have : (3 : ℤ) ≤ 0 := hC.1
        omega
    | prospective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_prospective
        have : (2 : ℤ) ≤ 1 := hC.2
        omega
  · rintro (rfl | rfl)
    · intro _ _ tt tsit h
      exact ⟨h.1, le_trans tsit.fst_le_snd h.2⟩
    · intro _ _ _ _ h
      exact h.2

/-- [smith-1997] Table 1, FP column: only perfective asserts the final point. -/
theorem showsFinalPoint_iff (v : ViewpointType) :
    v.ShowsFinalPoint ↔ v = .perfective := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | perfective => rfl
    | imperfective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_imperfective
        have : (3 : ℤ) ≤ 2 := hC.2
        omega
    | perfect =>
        exfalso
        have hC := @h ℤ _ _ _ rel_perfect
        have : (3 : ℤ) ≤ 2 := hC.1
        omega
    | prospective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_prospective
        have : (3 : ℤ) ≤ 1 := hC.2
        omega
    | neutral =>
        exfalso
        have hC := @h ℤ _ _ _ rel_neutral_short
        have : (5 : ℤ) ≤ 1 := hC.2
        omega
  · rintro rfl
    intro _ _ tt tsit h
    exact ⟨le_trans h.1 tsit.fst_le_snd, h.2⟩

/-- [smith-1997] Table 1, Closed column: only perfective and perfect are closed. -/
theorem isClosed_iff (v : ViewpointType) :
    v.IsClosed ↔ v = .perfective ∨ v = .perfect := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | perfective => exact Or.inl rfl
    | perfect => exact Or.inr rfl
    | imperfective =>
        exfalso
        have : (3 : ℤ) ≤ 2 := @h ℤ _ _ _ rel_imperfective
        omega
    | prospective =>
        exfalso
        have : (3 : ℤ) ≤ 1 := @h ℤ _ _ _ rel_prospective
        omega
    | neutral =>
        exfalso
        have : (5 : ℤ) ≤ 1 := @h ℤ _ _ _ rel_neutral_short
        omega
  · rintro (rfl | rfl)
    · intro _ _ _ _ h
      exact h.2
    · intro _ _ tt _ h
      exact le_trans h tt.fst_le_snd

/-- [smith-1997] Table 1, Preliminaries column: only the imperfective places
    the topic time strictly inside the situation. -/
theorem focusesPreliminaryStages_iff (v : ViewpointType) :
    v.FocusesPreliminaryStages ↔ v = .imperfective := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | imperfective => rfl
    | perfective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_perfective_refl
        -- hC : tt < tt for tt = ⟨0,1,_⟩ — contradicts irreflexivity
        exact lt_irrefl _ hC
    | perfect =>
        exfalso
        have hC := @h ℤ _ _ _ rel_perfect
        have : (4 : ℤ) ≤ 2 := hC.1.2
        omega
    | prospective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_prospective
        have : (2 : ℤ) ≤ 0 := hC.1.1
        omega
    | neutral =>
        exfalso
        have hC := @h ℤ _ _ _ rel_neutral_wide
        have : (10 : ℤ) ≤ 5 := hC.1.2
        omega
  · rintro rfl
    intro _ _ _ _ h
    exact h

end ViewpointType

-- ════════════════════════════════════════════════════
-- § Aspect Operators
-- ════════════════════════════════════════════════════

variable {T : Type*} [LinearOrder T] {W : Type*}

/-- **IMPERFECTIVE**: reference time properly contained in event runtime.
    [klein-1994]: TT INCL TSit. [knick-sharf-2026] eq. 25. -/
def IMPF (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, t < e.τ ∧ P w e

/-- **PERFECTIVE**: event runtime contained in reference time.
    [klein-1994]: TT AT TSit (simplified to TSit ⊆ TT, following [smith-1997]).
    [knick-sharf-2026] eq. 28. -/
def PRFV (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, e.τ ≤ t ∧ P w e

/-- **PROSPECTIVE**: reference time before situation time.
    [klein-1994]: TT BEFORE TSit. -/
def PROSP (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, t.isBefore e.τ ∧ P w e

/-- **INIT_OVERLAP**: initial overlap between reference time and event runtime.
    [pancheva-2003] eq. 7b: ⟦NEUTRAL⟧ = λP.λi.∃e[i ∂τ(e) & P(e)]
    The beginning of the eventuality is in the reference interval,
    but the end may extend beyond. Derives experiential perfect readings.

    Renamed from `NEUTRAL` to avoid collision with [smith-1997]'s
    neutral viewpoint (`ViewpointType.neutral`), which is a different concept.
    Pancheva's operator is an inner Asp₂ head; Smith's neutral viewpoint is
    a default viewpoint type. -/
def INIT_OVERLAP (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, t.initialOverlap e.τ ∧ P w e

-- ════════════════════════════════════════════════════
-- § Perfect Time Span / Extended Now
-- ════════════════════════════════════════════════════

/-- Right Boundary: PTS finishes at reference time point t. -/
def RB (pts : NonemptyInterval T) (t : T) : Prop := pts.snd = t

/-- Left Boundary: PTS starts at time tLB. -/
def LB (tLB : T) (pts : NonemptyInterval T) : Prop := pts.fst = tLB

/-- **PERFECT**: introduces Perfect Time Span.
    [knick-sharf-2026] eq. 22b — the standard XN-theoretic entry
    that K&S start from. Verified against the proceedings PDF.

    K&S notation: `λp_it.λt.∃t_PTS.[RB(t_PTS, t) ∧ p(t)]`. The `p(t)` is
    written by K&S as application to the outer reference time, with the
    composition convention that `t` is bound to `t_PTS` when IMPF appears
    below PERF (paper §4.2.1, sentence after eq. 25). The implementation
    here applies p to `pts` directly (the post-composition meaning), which
    matches K&S's worked composition in their (26). -/
def PERF (p : IntervalPred W T) : PointPred W T :=
  λ s => ∃ pts : NonemptyInterval T, RB pts s.time ∧ p s.world pts

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
    The implementation here uses `tLB : T` (a single point) with
    `∃ tLB ∈ tᵣ` (membership), simplifying K&S's set-theoretic LB to a
    single time witness inside the domain-restriction set. The simpler
    typing is sufficient for the empirical predictions K&S draw and
    avoids carrying intervals at every level. -/
def PERF_XN (p : IntervalPred W T) (tᵣ : Set T) : PointPred W T :=
  λ s => ∃ pts : NonemptyInterval T, ∃ tLB ∈ tᵣ,
    LB tLB pts ∧ RB pts s.time ∧ p s.world pts

-- ════════════════════════════════════════════════════
-- § Klein Correspondence
-- ════════════════════════════════════════════════════

/-- IMPF matches Klein's IMPERFECTIVE: ∃e where TT ⊂ TSit. -/
theorem impf_is_klein_imperfective (P : W → Event T → Prop) (w : W) (t : NonemptyInterval T) :
    IMPF P w t ↔ ∃ e, ViewpointType.ttTSitRelation .imperfective t e.τ ∧ P w e := by
  simp only [IMPF, ViewpointType.ttTSitRelation, Event.τ]

/-- PRFV matches Klein's PERFECTIVE: ∃e where TSit ⊆ TT. -/
theorem prfv_is_klein_perfective (P : W → Event T → Prop) (w : W) (t : NonemptyInterval T) :
    PRFV P w t ↔ ∃ e, ViewpointType.ttTSitRelation .perfective t e.τ ∧ P w e := by
  simp only [PRFV, ViewpointType.ttTSitRelation, Event.τ]

-- ════════════════════════════════════════════════════
-- § Compositional Stacking
-- ════════════════════════════════════════════════════

/-- "has been V-ing" = PERF(IMPF(V)). -/
abbrev perfProg (P : W → Event T → Prop) : PointPred W T :=
  PERF (IMPF P)

/-- "has V-ed" = PERF(PRFV(V)). -/
abbrev perfSimple (P : W → Event T → Prop) : PointPred W T :=
  PERF (PRFV P)

/-- PERF(IMPF(P)) unfolds: ∃ PTS and event, with PTS right-bounded at t,
    the PTS properly inside the event, and P holds of the event. -/
theorem perf_impf_unfold (P : W → Event T → Prop) (w : W) (t : T) :
    perfProg P ⟨w, t⟩ ↔
    ∃ pts : NonemptyInterval T, ∃ e : Event T,
      RB pts t ∧ pts < e.τ ∧ P w e := by
  constructor
  · intro ⟨pts, hRB, e, hSub, hP⟩
    exact ⟨pts, e, hRB, hSub, hP⟩
  · intro ⟨pts, e, hRB, hSub, hP⟩
    exact ⟨pts, hRB, e, hSub, hP⟩

/-- PERF(PRFV(P)) unfolds: ∃ PTS and event, with PTS right-bounded at t,
    the event inside the PTS, and P holds of the event. -/
theorem perf_prfv_unfold (P : W → Event T → Prop) (w : W) (t : T) :
    perfSimple P ⟨w, t⟩ ↔
    ∃ pts : NonemptyInterval T, ∃ e : Event T,
      RB pts t ∧ e.τ ≤ pts ∧ P w e := by
  constructor
  · intro ⟨pts, hRB, e, hSub, hP⟩
    exact ⟨pts, e, hRB, hSub, hP⟩
  · intro ⟨pts, e, hRB, hSub, hP⟩
    exact ⟨pts, hRB, e, hSub, hP⟩

-- ════════════════════════════════════════════════════
-- § PERF_XN ↔ PERF
-- ════════════════════════════════════════════════════

/-- Extended Now entails basic perfect (PERF_XN is stronger). -/
theorem perf_xn_entails_perf (p : IntervalPred W T) (tᵣ : Set T)
    (w : W) (t : T) :
    PERF_XN p tᵣ ⟨w, t⟩ → PERF p ⟨w, t⟩ := by
  intro ⟨pts, _tLB, _hmem, _hLB, hRB, hp⟩
  exact ⟨pts, hRB, hp⟩

/-- With maximal domain (Set.univ), PERF_XN collapses to PERF. -/
theorem perf_xn_univ_iff_perf (p : IntervalPred W T) (w : W) (t : T) :
    PERF_XN p Set.univ ⟨w, t⟩ ↔ PERF p ⟨w, t⟩ := by
  constructor
  · exact perf_xn_entails_perf p Set.univ w t
  · intro ⟨pts, hRB, hp⟩
    exact ⟨pts, pts.fst, Set.mem_univ _, rfl, hRB, hp⟩

/-- Narrower domain restriction is stronger (monotone in tᵣ). -/
theorem perf_xn_monotone (p : IntervalPred W T) (tᵣ₁ tᵣ₂ : Set T)
    (hSub : tᵣ₁ ⊆ tᵣ₂) (w : W) (t : T) :
    PERF_XN p tᵣ₁ ⟨w, t⟩ → PERF_XN p tᵣ₂ ⟨w, t⟩ := by
  intro ⟨pts, tLB, hmem, hLB, hRB, hp⟩
  exact ⟨pts, tLB, hSub hmem, hLB, hRB, hp⟩

-- ════════════════════════════════════════════════════
-- § Entailment Properties
-- ════════════════════════════════════════════════════

/-- IMPF entails an event exists. -/
theorem impf_entails_event (P : W → Event T → Prop) (w : W) (t : NonemptyInterval T) :
    IMPF P w t → ∃ e, P w e :=
  λ ⟨e, _, hP⟩ => ⟨e, hP⟩

/-- PRFV entails an event exists. -/
theorem prfv_entails_event (P : W → Event T → Prop) (w : W) (t : NonemptyInterval T) :
    PRFV P w t → ∃ e, P w e :=
  λ ⟨e, _, hP⟩ => ⟨e, hP⟩

/-- PERF is monotone: p ⊆ q → PERF(p) ⊆ PERF(q). -/
theorem perf_monotone (p q : IntervalPred W T)
    (h : ∀ w t, p w t → q w t) (w : W) (t : T) :
    PERF p ⟨w, t⟩ → PERF q ⟨w, t⟩ :=
  λ ⟨pts, hRB, hp⟩ => ⟨pts, hRB, h w pts hp⟩

/-- IMPF and PRFV impose opposite containment directions.
    IMPF: reference ⊂ event runtime. PRFV: event runtime ⊆ reference. -/
theorem impf_prfv_opposite_containment (P : W → Event T → Prop) (w : W) (t : NonemptyInterval T) :
    (IMPF P w t → ∃ e, P w e ∧ t < e.τ) ∧
    (PRFV P w t → ∃ e, P w e ∧ e.τ ≤ t) :=
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
def UNBOUNDED (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, t ≤ e.τ ∧ P w e

/-- Pancheva's BOUNDED (Asp₂): strict ⊂ variant of PRFV.
    ⟦BOUNDED⟧ = λP.λi.∃e[τ(e) ⊂ i & P(e)] ([pancheva-2003]: 282, eq. 7b).
    Differs from PRFV in using strict ⊂ rather than non-strict ⊆. -/
def BOUNDED (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, e.τ < t ∧ P w e

/-- IMPF (strict ⊂) entails UNBOUNDED (non-strict ⊆). -/
theorem impf_entails_unbounded (P : W → Event T → Prop) (w : W) (t : NonemptyInterval T) :
    IMPF P w t → UNBOUNDED P w t :=
  λ ⟨e, hSub, hP⟩ => ⟨e, hSub.1, hP⟩

/-- BOUNDED (strict ⊂) entails PRFV (non-strict ⊆). -/
theorem bounded_entails_prfv (P : W → Event T → Prop) (w : W) (t : NonemptyInterval T) :
    BOUNDED P w t → PRFV P w t :=
  λ ⟨e, hSub, hP⟩ => ⟨e, hSub.1, hP⟩

/-- Pancheva-style interval-level PERFECT (Asp₁).
    ⟦PERFECT⟧ = λp.λi.∃i'[PTS(i', i) & p(i')] ([pancheva-2003]: 284, eq. 9b).
    PTS(i', i) iff i is a final subinterval of i': i ⊆ i' ∧ i.snd = i'.snd. -/
def PERF_P (p : IntervalPred W T) : IntervalPred W T :=
  λ w i => ∃ pts : NonemptyInterval T, i.finalSubinterval pts ∧ p w pts

/-- Point-based PERF is the special case of interval-based PERF_P
    where the reference interval degenerates to a point [t, t]. -/
theorem perf_p_at_point_iff_perf (p : IntervalPred W T) (w : W) (t : T) :
    PERF_P p w (NonemptyInterval.pure t) ↔ PERF p ⟨w, t⟩ := by
  constructor
  · intro ⟨pts, hFin, hp⟩
    exact ⟨pts, hFin.2.symm, hp⟩
  · intro ⟨pts, hRB, hp⟩
    exact ⟨pts, ⟨⟨le_trans pts.fst_le_snd (le_of_eq hRB), le_of_eq hRB.symm⟩, hRB.symm⟩, hp⟩

/-- PERF_P is monotone: if p entails q, then PERF_P(p) entails PERF_P(q). -/
theorem perf_p_monotone (p q : IntervalPred W T)
    (h : ∀ w t, p w t → q w t) (w : W) (i : NonemptyInterval T) :
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
abbrev universalPerfect (P : W → Event T → Prop) : IntervalPred W T :=
  PERF_P (UNBOUNDED P)

/-- Experiential perfect: PERF_P(INIT_OVERLAP(V)).
    "has visited Paris" — event began within PTS.
    [pancheva-2003]: initial-overlap aspect allows event to extend beyond PTS. -/
abbrev experientialPerfect (P : W → Event T → Prop) : IntervalPred W T :=
  PERF_P (INIT_OVERLAP P)

/-- Resultative perfect: PERF_P(BOUNDED(V)).
    "has broken the vase" — event completed within PTS.
    Simplified: properly involves result state ([pancheva-2003]: 288). -/
abbrev resultativePerfect (P : W → Event T → Prop) : IntervalPred W T :=
  PERF_P (BOUNDED P)

/-- perfProg at a point entails universalPerfect at that point.
    Since IMPF (strict ⊂) entails UNBOUNDED (non-strict ⊆),
    PERF(IMPF(V)) entails PERF(UNBOUNDED(V)) = universalPerfect. -/
theorem perf_prog_entails_universal_at_point (P : W → Event T → Prop) (w : W) (t : T) :
    perfProg P ⟨w, t⟩ → universalPerfect P w (NonemptyInterval.pure t) :=
  λ h => (perf_p_at_point_iff_perf (UNBOUNDED P) w t).mpr
    (perf_monotone (IMPF P) (UNBOUNDED P) (impf_entails_unbounded P) w t h)

-- ════════════════════════════════════════════════════
-- § Bridge to Situation Semantics
-- ════════════════════════════════════════════════════

/-- Evaluate an interval predicate at a point (trivial interval [t, t]).
    Bridge for non-perfect forms. -/
def IntervalPred.atPoint (p : IntervalPred W T) : PointPred W T :=
  λ s => p s.world (NonemptyInterval.pure s.time)

end Aspect
