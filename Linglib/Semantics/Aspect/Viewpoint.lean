import Linglib.Semantics.Reference.Context.Index
import Linglib.Core.Order.Interval
import Linglib.Semantics.Events.Basic

/-!
# Viewpoint aspect

This file defines viewpoint, the second of the two components of aspect in Smith's theory.
Following Klein, a viewpoint relates the topic time to the situation time (`ViewpointType`,
`ViewpointType.ttTSitRelation`). A relation between the reference time and the run time of an
event gives an operator from event predicates to interval predicates (`IntervalPred.ofRel`),
monotone in the relation, and the operator of a viewpoint is that of its relation
(`ViewpointType.denote`). The compositional operators of Knick and Sharf are instances (`IMPF`,
`PRFV`, `PROSP`). The perfect takes an interval predicate to a point predicate through the
perfect time span (`PERF`, `PERF_XN`), and on to tense. The perfect time span of Iatridou,
Anagnostopoulou and Izvorski admits the spans a perfect-level adverbial allows (`PERF_ADV`), of
which the plain and extended-now perfects are the two instances.

## Implementation notes

* Klein's four relations: TT INCL TSit is the imperfective, TT AT TSit the perfective, TT AFTER
  TSit the perfect and TT BEFORE TSit the prospective; the neutral viewpoint of Smith includes
  the initial point of the situation and at least one internal stage.
* The operator equations follow Knick and Sharf: IMPF is λP λt ∃e, t ⊂ τ(e) ∧ P e, (25);
  PRFV is λP λt ∃e, τ(e) ⊆ t ∧ P e, (28); the extended-now PERF is
  λp λt ∃t_PTS, RB t_PTS t ∧ p t, (22b), and the paper's revision adds a left boundary drawn from
  a domain restriction tᵣ, λp λt ∃t_PTS ∃t_LB ⊆ tᵣ, LB t_LB t_PTS ∧ RB t_PTS t ∧ p t, (23b). The
  predicate applies to the outer reference time, under the paper's convention that beneath the
  perfect it corresponds to the perfect time span. A boundary is a time point here where the
  paper has a final or initial subinterval.
* A perfect-level adverbial is a predicate on spans, so *since t₀* is `LB t₀` and the covert
  adverbial of an unmodified perfect is `⊤`; at a fixed right boundary such a predicate is
  interchangeable with a domain restriction on the left boundary (`perf_adv_iff_perf_xn_image`).
* The non-strict imperfective `UNBOUNDED` is Pancheva's Asp₂ value, (7b), whose strict
  counterpart is `IMPF`.
* `Event T` and event predicates come from `Semantics/Events/Basic.lean`; tense-aspect
  composition does not reference the event sort.

## References

* [smith-1997]
* [klein-1994]
* [knick-sharf-2026]
* [pancheva-2003]
* [iatridou-anagnostopoulou-izvorski-2001]
-/

namespace Aspect

/-- A predicate over time intervals, the output of a viewpoint operator. -/
abbrev IntervalPred (W T : Type*) [LinearOrder T] := W → NonemptyInterval T → Prop

/-- A predicate over world-time points, the output of the perfect and the input to tense. -/
abbrev PointPred (W T : Type*) := Reference.Index W T → Prop

/-- The viewpoints are the four relations of [klein-1994] between the topic time and the situation
time, and the neutral viewpoint of [smith-1997], the default in the absence of aspect
morphology. -/
inductive ViewpointType
  | imperfective
  | perfective
  | perfect
  | prospective
  | neutral
  deriving DecidableEq, Repr, Inhabited

/-- The opposition of perfective and imperfective is viewpoint aspect at its coarsest, the right
granularity where the fact at issue is that the perfective requires actualization and the
imperfective does not, or where the opposition is lexically encoded, as on a `Verb.Stem`. -/
inductive Perfectivity
  | perfective
  | imperfective
  deriving DecidableEq, Repr, Inhabited

/-- `v.ttTSitRelation tt tsit` is the relation the viewpoint `v` imposes between the topic time and
the situation time, which is inclusion in the situation, containment of the situation,
posteriority, anteriority, and initial overlap for the neutral viewpoint. -/
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

/-- The aspect operator of a relation `R` between the reference time and the run time of an
event: the reference time stands in `R` to the run time of some event of the predicate. -/
def IntervalPred.ofRel (R : NonemptyInterval T → NonemptyInterval T → Prop)
    (P : W → Event T → Prop) : IntervalPred W T :=
  fun w t ↦ ∃ e : Event T, R t e.τ ∧ P w e

@[simp] theorem IntervalPred.ofRel_apply {R : NonemptyInterval T → NonemptyInterval T → Prop}
    {P : W → Event T → Prop} {w : W} {t : NonemptyInterval T} :
    IntervalPred.ofRel R P w t ↔ ∃ e : Event T, R t e.τ ∧ P w e := Iff.rfl

/-- The operator is monotone in the relation. -/
theorem IntervalPred.ofRel_mono {R S : NonemptyInterval T → NonemptyInterval T → Prop}
    (h : ∀ t s, R t s → S t s) {P : W → Event T → Prop} {w : W} {t : NonemptyInterval T} :
    IntervalPred.ofRel R P w t → IntervalPred.ofRel S P w t :=
  fun ⟨e, hR, hP⟩ ↦ ⟨e, h _ _ hR, hP⟩

/-- The operator of a viewpoint is the operator of its relation between the topic time and the
situation time. -/
def ViewpointType.denote (v : ViewpointType) (P : W → Event T → Prop) : IntervalPred W T :=
  IntervalPred.ofRel v.ttTSitRelation P

/-- The imperfective, (25), holds where the reference time is properly contained in the run time
of an event of the predicate. -/
def IMPF (P : W → Event T → Prop) : IntervalPred W T :=
  ViewpointType.imperfective.denote P

/-- The perfective, (28), holds where the run time of an event of the predicate is contained in
the reference time. -/
def PRFV (P : W → Event T → Prop) : IntervalPred W T :=
  ViewpointType.perfective.denote P

/-- The prospective holds where the reference time precedes an event of the predicate. -/
def PROSP (P : W → Event T → Prop) : IntervalPred W T :=
  ViewpointType.prospective.denote P

/-- The non-strict imperfective of [pancheva-2003], (7b): the reference time is contained,
not necessarily properly, in the run time of an event of the predicate. -/
def UNBOUNDED (P : W → Event T → Prop) : IntervalPred W T :=
  IntervalPred.ofRel (· ≤ ·) P

variable {P : W → Event T → Prop} {w : W} {t : NonemptyInterval T}

theorem impf_iff : IMPF P w t ↔ ∃ e : Event T, t < e.τ ∧ P w e := Iff.rfl

theorem prfv_iff : PRFV P w t ↔ ∃ e : Event T, e.τ ≤ t ∧ P w e := Iff.rfl

theorem prosp_iff : PROSP P w t ↔ ∃ e : Event T, t.isBefore e.τ ∧ P w e := Iff.rfl

theorem unbounded_iff : UNBOUNDED P w t ↔ ∃ e : Event T, t ≤ e.τ ∧ P w e := Iff.rfl

theorem impf_entails_unbounded (P : W → Event T → Prop) (w : W) (t : NonemptyInterval T) :
    IMPF P w t → UNBOUNDED P w t :=
  IntervalPred.ofRel_mono (R := (· < ·)) (S := (· ≤ ·)) fun _ _ ↦ le_of_lt

/-- The right boundary of a perfect time span is the reference time, (22a). -/
def RB (pts : NonemptyInterval T) (t : T) : Prop := pts.snd = t

/-- The left boundary of a perfect time span, (23a). -/
def LB (tLB : T) (pts : NonemptyInterval T) : Prop := pts.fst = tLB

/-- The perfect, (22b), holds where some perfect time span right-bounded by the reference time
satisfies the interval predicate. -/
def PERF (p : IntervalPred W T) : PointPred W T :=
  fun s ↦ ∃ pts : NonemptyInterval T, RB pts s.time ∧ p s.world pts

/-- The perfect with a left boundary drawn from the domain restriction `tᵣ`, (23b), over which
narrow focus on the participle generates alternatives. -/
def PERF_XN (p : IntervalPred W T) (tᵣ : Set T) : PointPred W T :=
  fun s ↦ ∃ pts : NonemptyInterval T, ∃ tLB ∈ tᵣ,
    LB tLB pts ∧ RB pts s.time ∧ p s.world pts

/-- With no domain restriction the left boundary is idle. -/
theorem perf_xn_univ_iff_perf (p : IntervalPred W T) (w : W) (t : T) :
    PERF_XN p Set.univ ⟨w, t⟩ ↔ PERF p ⟨w, t⟩ :=
  ⟨fun ⟨pts, _, _, _, hRB, hp⟩ ↦ ⟨pts, hRB, hp⟩,
    fun ⟨pts, hRB, hp⟩ ↦ ⟨pts, pts.fst, Set.mem_univ _, rfl, hRB, hp⟩⟩

/-- A narrower domain restriction is stronger. -/
theorem perf_xn_monotone (p : IntervalPred W T) {tᵣ₁ tᵣ₂ : Set T} (hSub : tᵣ₁ ⊆ tᵣ₂) (w : W)
    (t : T) : PERF_XN p tᵣ₁ ⟨w, t⟩ → PERF_XN p tᵣ₂ ⟨w, t⟩ :=
  fun ⟨pts, tLB, hmem, hLB, hRB, hp⟩ ↦ ⟨pts, tLB, hSub hmem, hLB, hRB, hp⟩

theorem perf_monotone {p q : IntervalPred W T} (h : ∀ w t, p w t → q w t) (w : W) (t : T) :
    PERF p ⟨w, t⟩ → PERF q ⟨w, t⟩ :=
  fun ⟨pts, hRB, hp⟩ ↦ ⟨pts, hRB, h w pts hp⟩

/-- An interval predicate evaluated at a point, the degenerate interval, for the non-perfect
forms. -/
def IntervalPred.atPoint (p : IntervalPred W T) : PointPred W T :=
  fun s ↦ p s.world (NonemptyInterval.pure s.time)

/-! ### The perfect-level adverbial -/

/-- The perfect over the spans a perfect-level adverbial admits, the perfect time span of
[iatridou-anagnostopoulou-izvorski-2001]: some admissible span right-bounded by the reference time
satisfies the interval predicate. -/
def PERF_ADV (p : IntervalPred W T) (adv : NonemptyInterval T → Prop) : PointPred W T :=
  fun s ↦ ∃ pts : NonemptyInterval T, adv pts ∧ RB pts s.time ∧ p s.world pts

variable (p : IntervalPred W T) (s : Reference.Index W T)

/-- The covert adverbial of an unmodified perfect admits every span. -/
theorem perf_adv_top_iff_perf : PERF_ADV p ⊤ s ↔ PERF p s :=
  ⟨fun ⟨pts, _, hRB, hp⟩ ↦ ⟨pts, hRB, hp⟩, fun ⟨pts, hRB, hp⟩ ↦ ⟨pts, trivial, hRB, hp⟩⟩

/-- A perfect-level adverbial is a conjunct of the interval predicate. -/
theorem perf_adv_iff_perf_inf (adv : NonemptyInterval T → Prop) :
    PERF_ADV p adv s ↔ PERF (fun w pts ↦ adv pts ∧ p w pts) s :=
  ⟨fun ⟨pts, hadv, hRB, hp⟩ ↦ ⟨pts, hRB, hadv, hp⟩, fun ⟨pts, hRB, hadv, hp⟩ ↦ ⟨pts, hadv, hRB, hp⟩⟩

/-- A weaker adverbial admits more spans. -/
theorem perf_adv_monotone {adv adv' : NonemptyInterval T → Prop} (h : ∀ pts, adv pts → adv' pts) :
    PERF_ADV p adv s → PERF_ADV p adv' s :=
  fun ⟨pts, hadv, hRB, hp⟩ ↦ ⟨pts, h pts hadv, hRB, hp⟩

/-- A domain restriction on the left boundary is the adverbial admitting the spans that start
in it. -/
theorem perf_xn_iff_perf_adv (tᵣ : Set T) : PERF_XN p tᵣ s ↔ PERF_ADV p (·.fst ∈ tᵣ) s :=
  ⟨fun ⟨pts, _, hmem, hLB, hRB, hp⟩ ↦ ⟨pts, Set.mem_of_eq_of_mem hLB hmem, hRB, hp⟩,
    fun ⟨pts, hmem, hRB, hp⟩ ↦ ⟨pts, pts.fst, hmem, rfl, hRB, hp⟩⟩

/-- For *since t₀*, the spans with left boundary `t₀` are the singleton domain restriction. -/
theorem perf_adv_lb_iff_perf_xn (t₀ : T) : PERF_ADV p (LB t₀) s ↔ PERF_XN p {t₀} s :=
  ⟨fun ⟨pts, hLB, hRB, hp⟩ ↦ ⟨pts, t₀, rfl, hLB, hRB, hp⟩,
    fun ⟨pts, _, htLB, hLB, hRB, hp⟩ ↦ ⟨pts, hLB.trans htLB, hRB, hp⟩⟩

/-- At a fixed right boundary an adverbial is a domain restriction on the left boundary, namely
the left boundaries of the admissible spans ending there. -/
theorem perf_adv_iff_perf_xn_image (adv : NonemptyInterval T → Prop) (w : W) (t : T) :
    PERF_ADV p adv ⟨w, t⟩ ↔ PERF_XN p ((·.fst) '' {pts | adv pts ∧ RB pts t}) ⟨w, t⟩ :=
  ⟨fun ⟨pts, hadv, hRB, hp⟩ ↦ ⟨pts, pts.fst, ⟨pts, ⟨hadv, hRB⟩, rfl⟩, rfl, hRB, hp⟩,
    fun ⟨pts, _, ⟨pts', ⟨hadv, hRB'⟩, hfst⟩, hLB, hRB, hp⟩ ↦
      have : pts' = pts :=
        NonemptyInterval.ext (Prod.ext (hfst.trans hLB.symm) (hRB'.trans hRB.symm))
      ⟨pts, this ▸ hadv, hRB, hp⟩⟩

end Aspect
