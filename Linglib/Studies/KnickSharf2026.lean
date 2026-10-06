module

public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Tense.Quantificational

/-!
# Knick and Sharf (2026): On focus and the perfect aspect

Knick and Sharf compose viewpoint aspect, the perfect and tense: an event predicate becomes an
interval predicate under the imperfective or perfective, a predicate of world-time points under
the perfect, and a proposition under a tense. The U-perfect, whose perfect time span has its
left boundary in a domain `tᵣ`, entails its simple present competitor whatever the domain and is
equivalent to it under broad focus, where the domain is unrestricted, which is why competition
rules it out there. Among the focus alternatives, a domain further in the past is stronger.

## Main definitions

* `simplePresent`: the simple present.
* `presPerfProgXN`: the U-perfect with domain restriction `tᵣ`.

## Main results

* `u_perf_entails_simple_present`: the U-perfect entails the simple present.
* `broad_focus_equiv`: under broad focus the two are equivalent.
* `earlier_lb_stronger_impf`: an earlier left boundary is stronger under the imperfective.
* `earlier_lb_not_weaker_impf`: and not conversely.

## Implementation notes

* A left boundary is a time point, where the paper's left boundary is a subinterval of `tᵣ`
  (`Aspect.PERF_XN`).
* `later_lb_stronger_prfv`, the reversed ordering under the perfective, is not drawn in the paper.

## References

* [knick-sharf-2026]
-/

@[expose] public section

namespace KnickSharf2026

open Reference Semantics ModalLogic

open Aspect
open Event (τ)

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-! ### Tense -/

/-- The present tense evaluates a point predicate at the speech time `tc` in the world `w`. -/
def evalPres (p : PointPred W T) (tc : T) (w : W) : Prop :=
  p ⟨w, tc⟩

/-- The past tense evaluates a point predicate at some time before the speech time `tc`, the
quantificational past of `Semantics/Tense/Quantificational.lean`. -/
def evalPast (p : PointPred W T) (tc : T) (w : W) : Prop :=
  ◇[Tense.accessibility ⟦Tense.past⟧] (fun t ↦ p (w, t)) tc

/-- The future tense evaluates a point predicate at some time after the speech time `tc`. -/
def evalFut (p : PointPred W T) (tc : T) (w : W) : Prop :=
  ◇[Tense.accessibility ⟦Tense.future⟧] (fun t ↦ p (w, t)) tc

/-! ### Composed forms -/

/-- The simple present is `PRES(IMPF(V).atPoint)`, so *John runs* holds at speech time when
some event `e` with `[tc, tc] ⊂ τ(e)` satisfies `V`. -/
def simplePresent (V : W → E → Prop) (tc : T) (w : W) : Prop :=
  evalPres (IntervalPred.atPoint (IMPF V)) tc w

/-- The simple past is `PAST(PRFV(V).atPoint)`, so *John ran* holds when some `t < tc` and some
event `e` with `τ(e) ⊆ [t, t]` satisfy `V`. -/
def simplePast (V : W → E → Prop) (tc : T) (w : W) : Prop :=
  evalPast (IntervalPred.atPoint (PRFV V)) tc w

/-- The present perfect progressive is `PRES(PERF(IMPF(V)))`, so *John has been running* holds
at `tc` when some perfect time span right-bounded by `tc` satisfies `IMPF(V)`. -/
def presPerfProg (V : W → E → Prop) (tc : T) (w : W) : Prop :=
  evalPres (PERF (IMPF V)) tc w

/-- The present perfect simple is `PRES(PERF(PRFV(V)))`, so *John has run* holds at `tc` when
some perfect time span right-bounded by `tc` satisfies `PRFV(V)`. -/
def presPerfSimple (V : W → E → Prop) (tc : T) (w : W) : Prop :=
  evalPres (PERF (PRFV V)) tc w

/-- The present perfect progressive with Extended Now is `PRES(PERF_XN(IMPF(V), tᵣ))`, the
U-perfect reading of [knick-sharf-2026]; *John has been running since Monday* restricts the left
boundary to `tᵣ`. -/
def presPerfProgXN (V : W → E → Prop) (tᵣ : Set T) (tc : T) (w : W) : Prop :=
  evalPres (PERF_XN (IMPF V) tᵣ) tc w

/-- The past perfect progressive is `PAST(PERF(IMPF(V)))`, so *John had been running* holds when
some `t < tc` satisfies `PERF(IMPF(V))`. -/
def pastPerfProg (V : W → E → Prop) (tc : T) (w : W) : Prop :=
  evalPast (PERF (IMPF V)) tc w

/-! ### Unfolding -/

/-- The simple present unfolds to `∃e, [tc, tc] ⊂ τ(e) ∧ V(w)(e)`. -/
theorem simplePresent_unfold (V : W → E → Prop) (tc : T) (w : W) :
    simplePresent V tc w ↔
    ∃ e : E, NonemptyInterval.pure tc < τ e ∧ V w e := by
  rfl

/-- The U-perfect under narrow focus, (39b), holds when some perfect time span with its left
boundary in `tᵣ` and its right boundary at `tc` falls under the imperfective. -/
theorem presPerfProgXN_unfold (V : W → E → Prop) (tᵣ : Set T)
    (tc : T) (w : W) :
    presPerfProgXN V tᵣ tc w ↔
    ∃ pts : NonemptyInterval T, ∃ tLB ∈ tᵣ,
      LB tLB pts ∧ RB pts tc ∧ IMPF V w pts := by
  rfl

/-! ### Results -/

/-- The U-perfect (39b) entails its simple present competitor (39a) whatever the domain `tᵣ`,
since a perfect time span ending at `tc` inside the run time of an event puts `tc` itself inside
it. -/
theorem u_perf_entails_simple_present (V : W → E → Prop)
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

/-- Under broad focus, where the domain `tᵣ` is the whole line, the U-perfect is equivalent to
the simple present, the equivalence by which competition rules it out; the converse direction
takes the point `tc` as the perfect time span. -/
theorem broad_focus_equiv (V : W → E → Prop) (tc : T) (w : W) :
    presPerfProgXN V Set.univ tc w ↔ simplePresent V tc w := by
  constructor
  · exact u_perf_entails_simple_present V Set.univ tc w
  · intro h
    exact ⟨NonemptyInterval.pure tc, tc, Set.mem_univ _, rfl, rfl, h⟩

/-- An earlier left boundary is stronger under the imperfective, the ordering of the focus
alternatives in (33) and (35), since an event whose run time contains the perfect time span from
`tLB₁` also contains the shorter one from a later `tLB₂`. -/
theorem earlier_lb_stronger_impf (V : W → E → Prop)
    (tLB₁ tLB₂ : T) (tc : T) (w : W) (h : tLB₁ < tLB₂) (htc : tLB₂ ≤ tc) :
    PERF_XN (IMPF V) {tLB₁} ⟨w, tc⟩ → PERF_XN (IMPF V) {tLB₂} ⟨w, tc⟩ := by
  intro ⟨pts, tLB, htLB, hLB, hRB, e, hlt, hV⟩
  obtain ⟨hsub, _hOr⟩ := NonemptyInterval.lt_def.mp hlt
  obtain ⟨hS1, hS2⟩ := NonemptyInterval.le_def.mp hsub
  -- tLB = tLB₁ (from singleton), pts = [tLB₁, tc]
  -- (τ e) ⊃ pts, so (τ e).fst ≤ tLB₁ < tLB₂ and tc ≤ (τ e).snd
  -- Construct new PTS = [tLB₂, tc]
  refine ⟨⟨⟨tLB₂, tc⟩, htc⟩, tLB₂, rfl, rfl, rfl, e,
    NonemptyInterval.lt_def.mpr ⟨NonemptyInterval.le_def.mpr ⟨?_, ?_⟩, ?_⟩, hV⟩
  · -- (τ e).fst ≤ tLB₂: from (τ e).fst ≤ pts.fst = tLB₁ < tLB₂
    have : tLB = tLB₁ := htLB
    exact le_of_lt (lt_of_le_of_lt (this ▸ hLB ▸ hS1) h)
  · -- tc ≤ (τ e).snd
    exact le_trans (le_of_eq hRB.symm) hS2
  · -- proper: (τ e).fst < tLB₂ (left disjunct)
    have : tLB = tLB₁ := htLB
    exact Or.inl (lt_of_le_of_lt (this ▸ hLB ▸ hS1) h)

/-- A later left boundary is stronger under the perfective (28), since an event fitting inside
the shorter span from `tLB₂` also fits inside the longer span from an earlier `tLB₁`. -/
theorem later_lb_stronger_prfv (V : W → E → Prop)
    (tLB₁ tLB₂ : T) (tc : T) (w : W) (h : tLB₁ < tLB₂) :
    PERF_XN (PRFV V) {tLB₂} ⟨w, tc⟩ → PERF_XN (PRFV V) {tLB₁} ⟨w, tc⟩ := by
  intro ⟨pts, tLB, htLB, hLB, hRB, e, hle, hV⟩
  obtain ⟨hS1, hS2⟩ := NonemptyInterval.le_def.mp hle
  -- tLB = tLB₂ (singleton), pts = [tLB₂, tc]
  -- (τ e) ⊆ pts: pts.fst ≤ (τ e).fst ∧ (τ e).snd ≤ pts.snd
  -- Construct PTS' = [tLB₁, tc], which is larger, so (τ e) ⊆ PTS' too
  have htLBeq : tLB = tLB₂ := htLB
  have htc : tLB₂ ≤ tc := htLBeq ▸ hLB ▸ le_trans pts.fst_le_snd (le_of_eq hRB)
  refine ⟨⟨⟨tLB₁, tc⟩, le_of_lt (lt_of_lt_of_le h htc)⟩, tLB₁, rfl, rfl, rfl, e,
    NonemptyInterval.le_def.mpr ⟨?_, ?_⟩, hV⟩
  · -- (τ e).fst ≥ tLB₁: from tLB₁ < tLB₂ = pts.fst ≤ (τ e).fst
    exact le_of_lt (lt_of_lt_of_le h (htLBeq ▸ hLB ▸ hS1))
  · -- (τ e).snd ≤ tc: from (τ e).snd ≤ pts.snd = tc
    exact le_trans hS2 (le_of_eq hRB)

/-- The ordering is strict, as the state `s''` of (33) shows, since an event going on since
`tLB₂` need not have been going on since an earlier `tLB₁`. The counterexample takes the boundaries
`0` and `2`, speech time `4`, and an event running over `[1, 5]`. -/
theorem earlier_lb_not_weaker_impf :
    ¬ ∀ (V : Unit → NonemptyInterval ℤ → Prop) (tLB₁ tLB₂ : ℤ) (tc : ℤ) (w : Unit),
      tLB₁ < tLB₂ →
      PERF_XN (IMPF V) {tLB₂} ⟨w, tc⟩ → PERF_XN (IMPF V) {tLB₁} ⟨w, tc⟩ := by
  intro hall
  -- Counterexample: event runtime [1,5], tLB₁=0, tLB₂=2, tc=4
  let e₀ : NonemptyInterval ℤ := ⟨⟨1, 5⟩, by omega⟩
  let V : Unit → NonemptyInterval ℤ → Prop := fun _ e => e = e₀
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
  -- hV : e = e₀, so (τ e).fst = 1
  -- hS1 : (τ e).fst ≤ pts.fst, i.e. 1 ≤ 0 — contradiction
  have htLBeq : tLB = (0 : ℤ) := htLB
  subst htLBeq
  dsimp only [V] at hV
  subst hV
  dsimp only [e₀] at hS1
  simp only [LB, Event.τ_nonemptyInterval] at hLB hS1
  omega

end KnickSharf2026
