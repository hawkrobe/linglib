/-
# Tense–Aspect Composition

End-to-end composition chain bridging viewpoint aspect operators to tense
evaluation, following Knick & Sharf (2026).

## The Pipeline

```
EventPred ──[IMPF/PRFV]──▷ IntervalPred ──[PERF]──▷ PointPred ──[eval*]──▷ Prop
```

The aspect chain produces `PointPred W Time = Situation W Time → Prop`.
The eval* operators instantiate the situation (fixing world and time).

## Composed Forms

| Form                | Composition              | Example              |
|---------------------|--------------------------|----------------------|
| `simplePresent`     | PRES(IMPF(V).atPoint)    | "John runs"          |
| `simplePast`        | PAST(PRFV(V).atPoint)    | "John ran"           |
| `presPerfProg`      | PRES(PERF(IMPF(V)))      | "John has been running" |
| `presPerfSimple`    | PRES(PERF(PRFV(V)))      | "John has run"       |
| `presPerfProgXN`    | PRES(PERF_XN(IMPF(V),tᵣ))| "John has been running (since…)" |
| `pastPerfProg`      | PAST(PERF(IMPF(V)))      | "John had been running" |

## Key Results (Knick & Sharf 2026)

- U-perf(tᵣ) entails simple present for all tᵣ (Theorem 3)
- U-perf(Set.univ) ↔ simple present (broad focus, Theorem 4)
- Earlier LB strengthens IMPF (Theorem 5), later LB strengthens PRFV (Theorem 6)
- The converse of Theorem 5 is false: concrete counterexample (Theorem 7)

## References

- Knick, A. & Sharf, M. (2026). On focus and the perfect aspect.
- Klein, W. (1994). Time in Language. Chapter 6.
- Iatridou, S., Anagnostopoulou, E. & Izvorski, R. (2001).
  Observations about the form and meaning of the Perfect.
-/

import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect
import Linglib.Theories.Semantics.Tense.Compositional

namespace Semantics.TenseAspectComposition

open Core.Time
open Semantics.Lexical.Verb.ViewpointAspect

variable {W Time : Type*} [LinearOrder Time]

-- ════════════════════════════════════════════════════
-- § Tense Evaluation Operators
-- ════════════════════════════════════════════════════

/-- Evaluate a point predicate at speech time (PRESENT).
    PRES: p holds at tc in world w. -/
def evalPres (p : PointPred W Time) (tc : Time) (w : W) : Prop :=
  p ⟨w, tc⟩

/-- Evaluate a point predicate with existential past (PAST).
    PAST: ∃t < tc, p(w)(t). -/
def evalPast (p : PointPred W Time) (tc : Time) (w : W) : Prop :=
  ∃ t : Time, t < tc ∧ p ⟨w, t⟩

/-- Evaluate a point predicate with existential future (FUTURE).
    FUT: ∃t > tc, p(w)(t). -/
def evalFut (p : PointPred W Time) (tc : Time) (w : W) : Prop :=
  ∃ t : Time, t > tc ∧ p ⟨w, t⟩

-- ════════════════════════════════════════════════════
-- § Composed Tense–Aspect Forms
-- ════════════════════════════════════════════════════

/-- **Simple present**: PRES(IMPF(V).atPoint).
    "John runs" = at speech time, ∃e with tc ⊂ τ(e) and V(e).
    Since atPoint evaluates at [tc, tc], this gives:
    ∃e, [tc,tc] ⊂ τ(e) ∧ V(e). -/
def simplePresent (V : EventPred W Time) (tc : Time) (w : W) : Prop :=
  evalPres (IntervalPred.atPoint (IMPF V)) tc w

/-- **Simple past**: PAST(PRFV(V).atPoint).
    "John ran" = ∃t < tc, ∃e with τ(e) ⊆ [t,t] and V(e). -/
def simplePast (V : EventPred W Time) (tc : Time) (w : W) : Prop :=
  evalPast (IntervalPred.atPoint (PRFV V)) tc w

/-- **Present perfect progressive**: PRES(PERF(IMPF(V))).
    "John has been running" = at tc, ∃PTS with RB(PTS, tc) and IMPF(V)(PTS). -/
def presPerfProg (V : EventPred W Time) (tc : Time) (w : W) : Prop :=
  evalPres (PERF (IMPF V)) tc w

/-- **Present perfect simple**: PRES(PERF(PRFV(V))).
    "John has run" = at tc, ∃PTS with RB(PTS, tc) and PRFV(V)(PTS). -/
def presPerfSimple (V : EventPred W Time) (tc : Time) (w : W) : Prop :=
  evalPres (PERF (PRFV V)) tc w

/-- **Present perfect progressive with Extended Now**: PRES(PERF_XN(IMPF(V), tᵣ)).
    Knick & Sharf (2026) eq. 39b: the U-perf reading.
    "John has been running (since Monday)" with domain restriction tᵣ on LB. -/
def presPerfProgXN (V : EventPred W Time) (tᵣ : Set Time) (tc : Time) (w : W) : Prop :=
  evalPres (PERF_XN (IMPF V) tᵣ) tc w

/-- **Past perfect progressive**: PAST(PERF(IMPF(V))).
    "John had been running" = ∃t < tc, PERF(IMPF(V))(w)(t). -/
def pastPerfProg (V : EventPred W Time) (tc : Time) (w : W) : Prop :=
  evalPast (PERF (IMPF V)) tc w

-- ════════════════════════════════════════════════════
-- § Unfold Theorems
-- ════════════════════════════════════════════════════

/-- Simple present unfolds to: ∃e, [tc,tc] ⊂ τ(e) ∧ V(w)(e). -/
theorem simplePresent_unfold (V : EventPred W Time) (tc : Time) (w : W) :
    simplePresent V tc w ↔
    ∃ e : Eventuality Time, (Interval.point tc).properSubinterval e.τ ∧ V w e := by
  rfl

/-- Present perfect progressive with XN unfolds to K&S eq. 39b:
    ∃PTS, ∃tLB ∈ tᵣ, LB(tLB, PTS) ∧ RB(PTS, tc) ∧ IMPF(V)(w)(PTS). -/
theorem presPerfProgXN_unfold (V : EventPred W Time) (tᵣ : Set Time)
    (tc : Time) (w : W) :
    presPerfProgXN V tᵣ tc w ↔
    ∃ pts : Interval Time, ∃ tLB ∈ tᵣ,
      LB tLB pts ∧ RB pts tc ∧ IMPF V w pts := by
  rfl

-- ════════════════════════════════════════════════════
-- § Knick & Sharf (2026) Core Results
-- ════════════════════════════════════════════════════

/-- **Theorem 3** (K&S 2026): U-perf(tᵣ) entails simple present.

    For any domain restriction tᵣ, the present perfect progressive with
    Extended Now entails the simple present. Intuitively: if there is a PTS
    ending at tc containing the reference time inside an ongoing event, then
    tc itself is inside that event.

    Proof sketch: Given PERF_XN(IMPF(V), tᵣ)(w)(tc), we have PTS with
    RB(PTS, tc) and ∃e with PTS ⊂ τ(e). Since [tc,tc] ⊆ PTS (because
    tc = PTS.finish) and PTS ⊂ τ(e), we get [tc,tc] ⊂ τ(e). -/
theorem u_perf_entails_simple_present (V : EventPred W Time)
    (tᵣ : Set Time) (tc : Time) (w : W) :
    presPerfProgXN V tᵣ tc w → simplePresent V tc w := by
  intro ⟨pts, _, _, _, hRB, e, ⟨⟨hS1, hS2⟩, hOr⟩, hV⟩
  exact ⟨e, ⟨⟨le_trans hS1 (le_trans pts.valid (le_of_eq hRB)),
              le_trans (le_of_eq hRB.symm) hS2⟩,
             hOr.elim
               (fun h => Or.inl (lt_of_lt_of_le h (le_trans pts.valid (le_of_eq hRB))))
               (fun h => Or.inr (lt_of_eq_of_lt hRB.symm h))⟩, hV⟩

/-- **Theorem 4** (K&S 2026): U-perf with maximal domain ↔ simple present.

    Under broad focus (tᵣ = Set.univ), the U-perf reading is equivalent to
    the simple present. This is the "degenerate" case where no LB constraint
    is imposed.

    Proof sketch: (→) by Theorem 3. (←) Given simplePresent, we have
    ∃e with [tc,tc] ⊂ τ(e). Construct PTS = [e.τ.start, tc]. Then
    LB(e.τ.start, PTS) ∈ Set.univ, RB(PTS, tc), and PTS ⊆ τ(e) with
    PTS ⊂ τ(e) (since tc < e.τ.finish by properSubinterval). -/
theorem broad_focus_equiv (V : EventPred W Time) (tc : Time) (w : W) :
    presPerfProgXN V Set.univ tc w ↔ simplePresent V tc w := by
  constructor
  · exact u_perf_entails_simple_present V Set.univ tc w
  · intro h
    exact ⟨Interval.point tc, tc, Set.mem_univ _, rfl, rfl, h⟩

/-- **Theorem 5** (K&S 2026): Earlier LB is stronger under IMPF.

    If tLB₁ < tLB₂, then PERF_XN(IMPF(V), {tLB₁}) entails
    PERF_XN(IMPF(V), {tLB₂}).

    Under IMPF, the event must contain the entire PTS. A PTS starting
    earlier (at tLB₁) requires a longer event runtime, which also
    contains a PTS starting later (at tLB₂) — because IMPF gives
    the subinterval property.

    Proof sketch: Given PTS₁ = [tLB₁, tc] with e.τ ⊃ PTS₁ and V(e),
    construct PTS₂ = [tLB₂, tc]. Since tLB₁ < tLB₂ ≤ tc, PTS₂ is valid.
    PTS₂ ⊆ PTS₁ ⊆ τ(e), and PTS₂ ⊂ τ(e) follows from PTS₁ ⊂ τ(e). -/
theorem earlier_lb_stronger_impf (V : EventPred W Time)
    (tLB₁ tLB₂ : Time) (tc : Time) (w : W) (h : tLB₁ < tLB₂) (htc : tLB₂ ≤ tc) :
    PERF_XN (IMPF V) {tLB₁} ⟨w, tc⟩ → PERF_XN (IMPF V) {tLB₂} ⟨w, tc⟩ := by
  intro ⟨pts, tLB, htLB, hLB, hRB, e, ⟨⟨hS1, hS2⟩, _hOr⟩, hV⟩
  -- tLB = tLB₁ (from singleton), pts = [tLB₁, tc]
  -- e.τ ⊃ pts, so e.τ.start ≤ tLB₁ < tLB₂ and tc ≤ e.τ.finish
  -- Construct new PTS = [tLB₂, tc]
  refine ⟨⟨tLB₂, tc, htc⟩, tLB₂, rfl, rfl, rfl, e, ⟨⟨?_, ?_⟩, ?_⟩, hV⟩
  · -- e.τ.start ≤ tLB₂: from e.τ.start ≤ pts.start = tLB₁ < tLB₂
    have : tLB = tLB₁ := htLB
    exact le_of_lt (lt_of_le_of_lt (this ▸ hLB ▸ hS1) h)
  · -- tc ≤ e.τ.finish
    exact le_trans (le_of_eq hRB.symm) hS2
  · -- proper: e.τ.start < tLB₂ (left disjunct)
    have : tLB = tLB₁ := htLB
    exact Or.inl (lt_of_le_of_lt (this ▸ hLB ▸ hS1) h)

/-- **Theorem 6** (K&S 2026): Later LB is stronger under PRFV.

    If tLB₁ < tLB₂, then PERF_XN(PRFV(V), {tLB₂}) entails
    PERF_XN(PRFV(V), {tLB₁}).

    Under PRFV, the event must be contained within the PTS. A PTS
    starting later (at tLB₂) is shorter, imposing a tighter constraint
    on event placement. But a PTS starting earlier (at tLB₁) is longer,
    so any event fitting in [tLB₂, tc] also fits in [tLB₁, tc].

    Proof sketch: Given PTS₂ = [tLB₂, tc] with τ(e) ⊆ PTS₂,
    construct PTS₁ = [tLB₁, tc]. Since tLB₁ < tLB₂, PTS₂ ⊆ PTS₁,
    so τ(e) ⊆ PTS₁. -/
theorem later_lb_stronger_prfv (V : EventPred W Time)
    (tLB₁ tLB₂ : Time) (tc : Time) (w : W) (h : tLB₁ < tLB₂) :
    PERF_XN (PRFV V) {tLB₂} ⟨w, tc⟩ → PERF_XN (PRFV V) {tLB₁} ⟨w, tc⟩ := by
  intro ⟨pts, tLB, htLB, hLB, hRB, e, ⟨hS1, hS2⟩, hV⟩
  -- tLB = tLB₂ (singleton), pts = [tLB₂, tc]
  -- e.τ ⊆ pts: pts.start ≤ e.τ.start ∧ e.τ.finish ≤ pts.finish
  -- Construct PTS' = [tLB₁, tc], which is larger, so e.τ ⊆ PTS' too
  have htLBeq : tLB = tLB₂ := htLB
  have htc : tLB₂ ≤ tc := htLBeq ▸ hLB ▸ le_trans pts.valid (le_of_eq hRB)
  refine ⟨⟨tLB₁, tc, le_of_lt (lt_of_lt_of_le h htc)⟩, tLB₁, rfl, rfl, rfl, e, ⟨?_, ?_⟩, hV⟩
  · -- e.τ.start ≥ tLB₁: from tLB₁ < tLB₂ = pts.start ≤ e.τ.start
    exact le_of_lt (lt_of_lt_of_le h (htLBeq ▸ hLB ▸ hS1))
  · -- e.τ.finish ≤ tc: from e.τ.finish ≤ pts.finish = tc
    exact le_trans hS2 (le_of_eq hRB)

/-- **Theorem 7** (K&S 2026): Converse of Theorem 5 is FALSE.

    PERF_XN(IMPF(V), {tLB₂}) does NOT entail PERF_XN(IMPF(V), {tLB₁})
    when tLB₁ < tLB₂. An event that has been going on since tLB₂ need not
    have been going on since the earlier tLB₁.

    Counterexample: Let tLB₁ = 0, tLB₂ = 2, tc = 4. An event with
    runtime [1, 5] satisfies IMPF for PTS = [2, 4] (since [2,4] ⊂ [1,5]),
    but does NOT satisfy IMPF for PTS = [0, 4] (since [0,4] ⊄ [1,5]:
    the event hadn't started at time 0). -/
theorem earlier_lb_not_weaker_impf :
    ¬ ∀ (V : EventPred Unit ℤ) (tLB₁ tLB₂ : ℤ) (tc : ℤ) (w : Unit),
      tLB₁ < tLB₂ →
      PERF_XN (IMPF V) {tLB₂} ⟨w, tc⟩ → PERF_XN (IMPF V) {tLB₁} ⟨w, tc⟩ := by
  intro hall
  -- Counterexample: event runtime [1,5], tLB₁=0, tLB₂=2, tc=4
  let e₀ : Eventuality ℤ := ⟨⟨1, 5, by omega⟩⟩
  let V : EventPred Unit ℤ := fun _ e => e = e₀
  -- Premise: PERF_XN(IMPF(V), {2})(⟨(), 4⟩)
  -- PTS = [2,4], event [1,5]: [2,4] ⊂ [1,5] ✓
  have prem : PERF_XN (IMPF V) {(2 : ℤ)} ⟨(), 4⟩ := by
    refine ⟨⟨2, 4, by omega⟩, 2, rfl, rfl, rfl, e₀, ?_, rfl⟩
    dsimp only [e₀]
    simp only [Interval.properSubinterval, Interval.subinterval, Eventuality.τ]
    omega
  -- Conclusion: PERF_XN(IMPF(V), {0})((), 4) — should be false
  have concl := hall V 0 2 4 () (by omega) prem
  obtain ⟨pts, tLB, htLB, hLB, hRB, e, ⟨⟨hS1, _⟩, _⟩, hV⟩ := concl
  -- htLB : tLB = 0, hLB : pts.start = tLB, so pts.start = 0
  -- hV : e = e₀, so e.τ.start = 1
  -- hS1 : e.τ.start ≤ pts.start, i.e. 1 ≤ 0 — contradiction
  have htLBeq : tLB = (0 : ℤ) := htLB
  subst htLBeq
  dsimp only [V] at hV
  subst hV
  dsimp only [e₀] at hS1
  simp only [LB, Eventuality.τ] at hLB hS1
  omega

end Semantics.TenseAspectComposition
