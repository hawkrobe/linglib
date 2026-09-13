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
[klein-1994]: a viewpoint relates the topic time to the situation time (`ViewpointType`,
`ViewpointType.ttTSitRelation`), and the compositional operators of [knick-sharf-2026] take an
event predicate to an interval predicate (`IMPF`, `PRFV`, `PROSP`), an interval predicate to a
point predicate through the perfect time span (`PERF`, `PERF_XN`), and on to tense.

## Implementation notes

* Klein's four relations: TT INCL TSit is the imperfective, TT AT TSit the perfective, TT AFTER
  TSit the perfect and TT BEFORE TSit the prospective; the neutral viewpoint of [smith-1997]
  includes the initial point of the situation and at least one internal stage.
* The operator equations follow [knick-sharf-2026]: IMPF is λP λt ∃e, t ⊂ τ(e) ∧ P e, (25);
  PRFV is λP λt ∃e, τ(e) ⊆ t ∧ P e, (28); the extended-now PERF is
  λp λt ∃t_PTS, RB t_PTS t ∧ p t, (22b), and the paper's revision adds a left boundary drawn from
  a domain restriction tᵣ, λp λt ∃t_PTS ∃t_LB ⊆ tᵣ, LB t_LB t_PTS ∧ RB t_PTS t ∧ p t, (23b). The
  predicate applies to the outer reference time, under the paper's convention that beneath the
  perfect it corresponds to the perfect time span. A boundary is a time point here where the
  paper has a final or initial subinterval.
* The non-strict imperfective `UNBOUNDED` is [pancheva-2003]'s Asp₂ value, (7b), whose
  strict counterpart is `IMPF`.
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

/-! ### Viewpoint -/

/-- A predicate over time intervals, the output of a viewpoint operator. -/
abbrev IntervalPred (W T : Type*) [LinearOrder T] := W → NonemptyInterval T → Prop

/-- A predicate over world-time points, the output of the perfect and the input to tense. -/
abbrev PointPred (W T : Type*) := Reference.Index W T → Prop

/-- The viewpoints: the four relations of [klein-1994] between the topic time and the situation
time, and the neutral viewpoint of [smith-1997], the default in the absence of aspect
morphology. -/
inductive ViewpointType
  | imperfective
  | perfective
  | perfect
  | prospective
  | neutral
  deriving DecidableEq, Repr, Inhabited

/-- The perfective / imperfective opposition, viewpoint aspect at its coarsest: the right
granularity where the fact at issue is that the perfective requires actualization and the
imperfective does not, or where the opposition is lexically encoded, as on a `Verb.Stem`. -/
inductive Perfectivity
  | perfective
  | imperfective
  deriving DecidableEq, Repr, Inhabited

/-- The relation a viewpoint imposes between the topic time and the situation time: inclusion
in the situation, containment of the situation, posteriority, anteriority, and initial overlap
for the neutral viewpoint. -/
def ViewpointType.ttTSitRelation {T : Type*} [LinearOrder T]
    (v : ViewpointType) (tt tsit : NonemptyInterval T) : Prop :=
  match v with
  | .imperfective => tt < tsit
  | .perfective => tsit ≤ tt
  | .perfect => tt.isAfter tsit
  | .prospective => tt.isBefore tsit
  | .neutral => tt.initialOverlap tsit

instance {T : Type*} [LinearOrder T] (v : ViewpointType) (tt tsit : NonemptyInterval T) :
    Decidable (v.ttTSitRelation tt tsit) := by
  cases v <;> unfold ViewpointType.ttTSitRelation <;> infer_instance

/-! ### Operators -/

variable {T : Type*} [LinearOrder T] {W : Type*}

/-- The imperfective, (25): the reference time is properly contained in the run time of an
event of the predicate. -/
def IMPF (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, t < e.τ ∧ P w e

/-- The perfective, (28): the run time of an event of the predicate is contained in the
reference time. -/
def PRFV (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, e.τ ≤ t ∧ P w e

/-- The prospective: the reference time precedes an event of the predicate. -/
def PROSP (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, t.isBefore e.τ ∧ P w e

/-- The non-strict imperfective of [pancheva-2003], (7b): the reference time is contained,
not necessarily properly, in the run time of an event of the predicate. -/
def UNBOUNDED (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, t ≤ e.τ ∧ P w e

theorem impf_entails_unbounded (P : W → Event T → Prop) (w : W) (t : NonemptyInterval T) :
    IMPF P w t → UNBOUNDED P w t :=
  λ ⟨e, hSub, hP⟩ => ⟨e, hSub.1, hP⟩

/-- The right boundary of a perfect time span is the reference time, (22a). -/
def RB (pts : NonemptyInterval T) (t : T) : Prop := pts.snd = t

/-- The left boundary of a perfect time span, (23a). -/
def LB (tLB : T) (pts : NonemptyInterval T) : Prop := pts.fst = tLB

/-- The perfect, (22b): some perfect time span right-bounded by the reference time satisfies
the interval predicate. -/
def PERF (p : IntervalPred W T) : PointPred W T :=
  λ s => ∃ pts : NonemptyInterval T, RB pts s.time ∧ p s.world pts

/-- The perfect with a left boundary drawn from the domain restriction `tᵣ`, (23b): narrow focus
on the participle generates alternatives over `tᵣ`. -/
def PERF_XN (p : IntervalPred W T) (tᵣ : Set T) : PointPred W T :=
  λ s => ∃ pts : NonemptyInterval T, ∃ tLB ∈ tᵣ,
    LB tLB pts ∧ RB pts s.time ∧ p s.world pts

/-- With no domain restriction the left boundary is idle. -/
theorem perf_xn_univ_iff_perf (p : IntervalPred W T) (w : W) (t : T) :
    PERF_XN p Set.univ ⟨w, t⟩ ↔ PERF p ⟨w, t⟩ :=
  ⟨λ ⟨pts, _, _, _, hRB, hp⟩ => ⟨pts, hRB, hp⟩,
    λ ⟨pts, hRB, hp⟩ => ⟨pts, pts.fst, Set.mem_univ _, rfl, hRB, hp⟩⟩

/-- A narrower domain restriction is stronger. -/
theorem perf_xn_monotone (p : IntervalPred W T) {tᵣ₁ tᵣ₂ : Set T} (hSub : tᵣ₁ ⊆ tᵣ₂) (w : W)
    (t : T) : PERF_XN p tᵣ₁ ⟨w, t⟩ → PERF_XN p tᵣ₂ ⟨w, t⟩ :=
  λ ⟨pts, tLB, hmem, hLB, hRB, hp⟩ => ⟨pts, tLB, hSub hmem, hLB, hRB, hp⟩

theorem perf_monotone {p q : IntervalPred W T} (h : ∀ w t, p w t → q w t) (w : W) (t : T) :
    PERF p ⟨w, t⟩ → PERF q ⟨w, t⟩ :=
  λ ⟨pts, hRB, hp⟩ => ⟨pts, hRB, h w pts hp⟩

/-- An interval predicate evaluated at a point, the degenerate interval, for the non-perfect
forms. -/
def IntervalPred.atPoint (p : IntervalPred W T) : PointPred W T :=
  λ s => p s.world (NonemptyInterval.pure s.time)

end Aspect
