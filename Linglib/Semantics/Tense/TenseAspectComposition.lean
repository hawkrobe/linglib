/-
# Tense–Aspect Composition

End-to-end composition chain bridging viewpoint aspect operators to tense
evaluation, following [knick-sharf-2026].

## The Pipeline

```
Event T → Prop ──[IMPF/PRFV]──▷ IntervalPred ──[PERF]──▷ PointPred ──[eval*]──▷ Prop
```

The aspect chain produces `PointPred W T = Index W T → Prop`.
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

## Key Results

- U-perf(tᵣ) entails simple present for all tᵣ (Theorem 3)
- U-perf(Set.univ) ↔ simple present (broad focus, Theorem 4)
- Earlier LB strengthens IMPF (Theorem 5), later LB strengthens PRFV (Theorem 6)
- The converse of Theorem 5 is false: concrete counterexample (Theorem 7)

-/

module

public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Quantification.Basic

@[expose] public section

namespace Tense.TenseAspectComposition

open Reference

open Aspect

variable {W T : Type*} [LinearOrder T]

/-! ### Tense Evaluation Operators -/

/-- Evaluate a point predicate at speech time (PRESENT).
    PRES: p holds at tc in world w. -/
def evalPres (p : PointPred W T) (tc : T) (w : W) : Prop :=
  p ⟨w, tc⟩

/-- Existential tense evaluation is `Quantifier.GQ.some` over the times `rel`-related to the
evaluation time `tc`, with scope `p` at `⟨w, ·⟩`; `evalPast` and `evalFut` are the `<` and `>`
instances. -/
def evalRel (rel : T → T → Prop) (p : PointPred W T) (tc : T) (w : W) : Prop :=
  Quantifier.GQ.some (fun t => rel t tc) (fun t => p ⟨w, t⟩)

omit [LinearOrder T] in
/-- Monotone in the body predicate — inherited from `scopeMonotone_some`, not reproved. -/
theorem evalRel_mono {rel : T → T → Prop} {p q : PointPred W T}
    (h : ∀ x, p x → q x) {tc : T} {w : W} :
    evalRel rel p tc w → evalRel rel q tc w :=
  Quantifier.GQ.scopeMonotone_some _ fun _ hp => h _ hp

/-- Existential past evaluates a point predicate as `∃ t < tc, p(w)(t)`. -/
def evalPast (p : PointPred W T) (tc : T) (w : W) : Prop :=
  evalRel (· < ·) p tc w

/-- Existential future evaluates a point predicate as `∃ t > tc, p(w)(t)`. -/
def evalFut (p : PointPred W T) (tc : T) (w : W) : Prop :=
  evalRel (· > ·) p tc w

/-! ### Composed Tense–Aspect Forms -/

/-- The simple present is `PRES(IMPF(V).atPoint)`, so *John runs* holds at speech time when
some event `e` with `[tc, tc] ⊂ τ(e)` satisfies `V`. -/
def simplePresent (V : W → Event T → Prop) (tc : T) (w : W) : Prop :=
  evalPres (IntervalPred.atPoint (IMPF V)) tc w

/-- The simple past is `PAST(PRFV(V).atPoint)`, so *John ran* holds when some `t < tc` and some
event `e` with `τ(e) ⊆ [t, t]` satisfy `V`. -/
def simplePast (V : W → Event T → Prop) (tc : T) (w : W) : Prop :=
  evalPast (IntervalPred.atPoint (PRFV V)) tc w

/-- The present perfect progressive is `PRES(PERF(IMPF(V)))`, so *John has been running* holds
at `tc` when some perfect time span right-bounded by `tc` satisfies `IMPF(V)`. -/
def presPerfProg (V : W → Event T → Prop) (tc : T) (w : W) : Prop :=
  evalPres (PERF (IMPF V)) tc w

/-- The present perfect simple is `PRES(PERF(PRFV(V)))`, so *John has run* holds at `tc` when
some perfect time span right-bounded by `tc` satisfies `PRFV(V)`. -/
def presPerfSimple (V : W → Event T → Prop) (tc : T) (w : W) : Prop :=
  evalPres (PERF (PRFV V)) tc w

/-- The present perfect progressive with Extended Now is `PRES(PERF_XN(IMPF(V), tᵣ))`, the
U-perfect reading of [knick-sharf-2026]; *John has been running since Monday* restricts the left
boundary to `tᵣ`. -/
def presPerfProgXN (V : W → Event T → Prop) (tᵣ : Set T) (tc : T) (w : W) : Prop :=
  evalPres (PERF_XN (IMPF V) tᵣ) tc w

/-- The past perfect progressive is `PAST(PERF(IMPF(V)))`, so *John had been running* holds when
some `t < tc` satisfies `PERF(IMPF(V))`. -/
def pastPerfProg (V : W → Event T → Prop) (tc : T) (w : W) : Prop :=
  evalPast (PERF (IMPF V)) tc w

/-! ### Unfold Theorems -/

/-- The simple present unfolds to `∃e, [tc, tc] ⊂ τ(e) ∧ V(w)(e)`. -/
theorem simplePresent_unfold (V : W → Event T → Prop) (tc : T) (w : W) :
    simplePresent V tc w ↔
    ∃ e : Event T, NonemptyInterval.pure tc < e.τ ∧ V w e := by
  rfl

/-- Present perfect progressive with XN unfolds to K&S eq. 39b:
    ∃PTS, ∃tLB ∈ tᵣ, LB(tLB, PTS) ∧ RB(PTS, tc) ∧ IMPF(V)(w)(PTS). -/
theorem presPerfProgXN_unfold (V : W → Event T → Prop) (tᵣ : Set T)
    (tc : T) (w : W) :
    presPerfProgXN V tᵣ tc w ↔
    ∃ pts : NonemptyInterval T, ∃ tLB ∈ tᵣ,
      LB tLB pts ∧ RB pts tc ∧ IMPF V w pts := by
  rfl

/-! ### [knick-sharf-2026] Core Results -/

/-- Theorem 3 of [knick-sharf-2026] says that the U-perfect entails the simple present for any
domain restriction `tᵣ`: a perfect time span ending at `tc` inside an ongoing event puts `tc`
itself inside that event. -/
theorem u_perf_entails_simple_present (V : W → Event T → Prop)
    (tᵣ : Set T) (tc : T) (w : W) :
    presPerfProgXN V tᵣ tc w → simplePresent V tc w := by
  intro ⟨pts, _, _, _, hRB, e, hlt, hV⟩
  obtain ⟨hsub, hOr⟩ := NonemptyInterval.lt_def.mp hlt
  obtain ⟨hS1, hS2⟩ := NonemptyInterval.le_def.mp hsub
  exact ⟨e, NonemptyInterval.lt_def.mpr
    ⟨NonemptyInterval.le_def.mpr
        ⟨le_trans hS1 (le_trans pts.fst_le_snd (le_of_eq hRB)),
         le_trans (le_of_eq hRB.symm) hS2⟩,
     hOr.elim
       (fun h => Or.inl (lt_of_lt_of_le h (le_trans pts.fst_le_snd (le_of_eq hRB))))
       (fun h => Or.inr (lt_of_eq_of_lt hRB.symm h))⟩, hV⟩

/-- Theorem 4 of [knick-sharf-2026] says that under broad focus, where `tᵣ` is the whole line,
the U-perfect is equivalent to the simple present, the degenerate case without a left-boundary
constraint; the converse direction takes the perfect time span from the event's start to
`tc`. -/
theorem broad_focus_equiv (V : W → Event T → Prop) (tc : T) (w : W) :
    presPerfProgXN V Set.univ tc w ↔ simplePresent V tc w := by
  constructor
  · exact u_perf_entails_simple_present V Set.univ tc w
  · intro h
    exact ⟨NonemptyInterval.pure tc, tc, Set.mem_univ _, rfl, rfl, h⟩

/-- Theorem 5 of [knick-sharf-2026] says that an earlier left boundary is stronger under the
imperfective, since an event containing a perfect time span from `tLB₁` also contains the
shorter one from a later `tLB₂` by the subinterval property. -/
theorem earlier_lb_stronger_impf (V : W → Event T → Prop)
    (tLB₁ tLB₂ : T) (tc : T) (w : W) (h : tLB₁ < tLB₂) (htc : tLB₂ ≤ tc) :
    PERF_XN (IMPF V) {tLB₁} ⟨w, tc⟩ → PERF_XN (IMPF V) {tLB₂} ⟨w, tc⟩ := by
  intro ⟨pts, tLB, htLB, hLB, hRB, e, hlt, hV⟩
  obtain ⟨hsub, _hOr⟩ := NonemptyInterval.lt_def.mp hlt
  obtain ⟨hS1, hS2⟩ := NonemptyInterval.le_def.mp hsub
  -- tLB = tLB₁ (from singleton), pts = [tLB₁, tc]
  -- e.τ ⊃ pts, so e.τ.fst ≤ tLB₁ < tLB₂ and tc ≤ e.τ.snd
  -- Construct new PTS = [tLB₂, tc]
  refine ⟨⟨⟨tLB₂, tc⟩, htc⟩, tLB₂, rfl, rfl, rfl, e,
    NonemptyInterval.lt_def.mpr ⟨NonemptyInterval.le_def.mpr ⟨?_, ?_⟩, ?_⟩, hV⟩
  · -- e.τ.fst ≤ tLB₂: from e.τ.fst ≤ pts.fst = tLB₁ < tLB₂
    have : tLB = tLB₁ := htLB
    exact le_of_lt (lt_of_le_of_lt (this ▸ hLB ▸ hS1) h)
  · -- tc ≤ e.τ.snd
    exact le_trans (le_of_eq hRB.symm) hS2
  · -- proper: e.τ.fst < tLB₂ (left disjunct)
    have : tLB = tLB₁ := htLB
    exact Or.inl (lt_of_le_of_lt (this ▸ hLB ▸ hS1) h)

/-- Theorem 6 of [knick-sharf-2026] says that a later left boundary is stronger under the
perfective, since an event fitting inside the shorter span from `tLB₂` also fits inside the
longer span from an earlier `tLB₁`. -/
theorem later_lb_stronger_prfv (V : W → Event T → Prop)
    (tLB₁ tLB₂ : T) (tc : T) (w : W) (h : tLB₁ < tLB₂) :
    PERF_XN (PRFV V) {tLB₂} ⟨w, tc⟩ → PERF_XN (PRFV V) {tLB₁} ⟨w, tc⟩ := by
  intro ⟨pts, tLB, htLB, hLB, hRB, e, hle, hV⟩
  obtain ⟨hS1, hS2⟩ := NonemptyInterval.le_def.mp hle
  -- tLB = tLB₂ (singleton), pts = [tLB₂, tc]
  -- e.τ ⊆ pts: pts.fst ≤ e.τ.fst ∧ e.τ.snd ≤ pts.snd
  -- Construct PTS' = [tLB₁, tc], which is larger, so e.τ ⊆ PTS' too
  have htLBeq : tLB = tLB₂ := htLB
  have htc : tLB₂ ≤ tc := htLBeq ▸ hLB ▸ le_trans pts.fst_le_snd (le_of_eq hRB)
  refine ⟨⟨⟨tLB₁, tc⟩, le_of_lt (lt_of_lt_of_le h htc)⟩, tLB₁, rfl, rfl, rfl, e,
    NonemptyInterval.le_def.mpr ⟨?_, ?_⟩, hV⟩
  · -- e.τ.fst ≥ tLB₁: from tLB₁ < tLB₂ = pts.fst ≤ e.τ.fst
    exact le_of_lt (lt_of_lt_of_le h (htLBeq ▸ hLB ▸ hS1))
  · -- e.τ.snd ≤ tc: from e.τ.snd ≤ pts.snd = tc
    exact le_trans hS2 (le_of_eq hRB)

/-- Theorem 7 of [knick-sharf-2026] says that the converse of Theorem 5 fails, since an event
going on since `tLB₂` need not have been going on since an earlier `tLB₁`; the counterexample
takes the boundaries `0` and `2`, speech time `4`, and an event running over `[1, 5]`. -/
theorem earlier_lb_not_weaker_impf :
    ¬ ∀ (V : Unit → Event ℤ → Prop) (tLB₁ tLB₂ : ℤ) (tc : ℤ) (w : Unit),
      tLB₁ < tLB₂ →
      PERF_XN (IMPF V) {tLB₂} ⟨w, tc⟩ → PERF_XN (IMPF V) {tLB₁} ⟨w, tc⟩ := by
  intro hall
  -- Counterexample: event runtime [1,5], tLB₁=0, tLB₂=2, tc=4
  -- sort defaults to .action; the proof doesn't reference .sort
  let e₀ : Event ℤ := ⟨⟨⟨1, 5⟩, by omega⟩, .action⟩
  let V : Unit → Event ℤ → Prop := fun _ e => e = e₀
  -- Premise: PERF_XN(IMPF(V), {2})(⟨(), 4⟩)
  -- PTS = [2,4], event [1,5]: [2,4] ⊂ [1,5] ✓
  have prem : PERF_XN (IMPF V) {(2 : ℤ)} ⟨(), 4⟩ := by
    refine ⟨⟨⟨2, 4⟩, by omega⟩, 2, rfl, rfl, rfl, e₀, ?_, rfl⟩
    dsimp only [e₀]
    decide
  -- Conclusion: PERF_XN(IMPF(V), {0})((), 4) — should be false
  have concl := hall V 0 2 4 () (by omega) prem
  obtain ⟨pts, tLB, htLB, hLB, hRB, e, hlt, hV⟩ := concl
  have hS1 := (NonemptyInterval.le_def.mp (NonemptyInterval.lt_def.mp hlt).1).1
  -- htLB : tLB = 0, hLB : pts.fst = tLB, so pts.fst = 0
  -- hV : e = e₀, so e.τ.fst = 1
  -- hS1 : e.τ.fst ≤ pts.fst, i.e. 1 ≤ 0 — contradiction
  have htLBeq : tLB = (0 : ℤ) := htLB
  subst htLBeq
  dsimp only [V] at hV
  subst hV
  dsimp only [e₀] at hS1
  simp only [LB, Event.τ] at hLB hS1
  omega

end Tense.TenseAspectComposition
