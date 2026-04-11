import Linglib.Theories.Semantics.Tense.Aspect.Core

/-!
# The Subinterval Property

The subinterval property (Bennett & Partee 1972, Dowty 1979) is a fundamental
semantic property of event predicates that determines their aspectual class:

- **Statives and activities** have it: if John is sleeping for [1pm, 3pm],
  he is sleeping at every subinterval
- **Accomplishments and achievements** lack it: if John built a house in
  [Jan, Dec], he did not build a house in [Jan, Feb]

This property is central to the semantics of temporal adverbials
(@cite{rouillard-2026}), NPI licensing in boundary adverbials
(@cite{iatridou-zeijlstra-2021}), and the distribution of progressive
and imperfective aspect crosslinguistically.

Extracted from `MaximalInformativity.lean` because it is a general property
of event predicates, not specific to any particular analysis.
-/

namespace Semantics.Tense.Aspect.SubintervalProperty

open Core.Time
open Semantics.Tense.Aspect.Core

variable {W Time : Type*} [LinearOrder Time]

/-- **Subinterval property for event predicates** (mereological version).
    SUB(P) iff every subinterval of a P-event's runtime that is also
    the runtime of some event is the runtime of a P-event.
    States and activities have this property; accomplishments/achievements
    lack it. -/
def HasSubintervalProp (P : EventPred W Time) : Prop :=
  ∀ (e₁ : Eventuality Time) (w : W),
    P w e₁ →
    ∀ (t : Interval Time), t.subinterval e₁.τ →
    ∀ (e₂ : Eventuality Time), e₂.τ = t →
    P w e₂

/-- **Closed subinterval property** (CSUB).
    For any subinterval t of a P-event's runtime, there exists a P-event
    whose runtime is t. Stronger than SUB: guarantees witnesses exist,
    not just that predication is preserved. -/
def HasClosedSubintervalProp (P : EventPred W Time) : Prop :=
  ∀ (e₁ : Eventuality Time) (w : W),
    P w e₁ →
    ∀ (t : Interval Time), t.subinterval e₁.τ →
    ∃ (e₂ : Eventuality Time), e₂.τ = t ∧ P w e₂

-- ════════════════════════════════════════════════════
-- § Operator-Level Consequences
-- ════════════════════════════════════════════════════

/-! The subinterval property's consequences at the level of aspect operators.
    @cite{smith-1997} Ch. 2: states and activities have the subinterval
    property; accomplishments, achievements, and semelfactives lack it.

    The VendlerClass-level classification (`predictsSubintervalProp`,
    `sub_agrees_with_homogeneous`) is in `LexicalAspect.lean`. Here we
    prove the operator-level consequences:

    1. **Activity entailment** (p. 25): IMPF(activity) at I entails
       PRFV(activity) at some I' ⊆ I — activities have part-whole homogeneity.
    2. **Imperfective paradox** (p. 29): IMPF(accomplishment) does NOT
       entail PRFV(accomplishment) — the missing endpoint problem.
    3. **IMPF ⊢ PRFV ⟺ CSIP**: the imperfective entails the perfective
       if and only if the predicate has the closed subinterval property. -/

open Semantics.Tense.Aspect.LexicalAspect

/-- **Activity entailment** (@cite{smith-1997} p. 25):
    If an activity predicate P holds at interval I (IMPF reading: I is
    inside the event's runtime), then P holds at every subinterval of I
    (PRFV reading: subinterval is contained in the event).

    Formally: HasSubintervalProp(P) → IMPF(P)(w)(I) → ∀ I' ⊆ I, ∃e. τ(e) = I' ∧ P(w)(e).

    This is the semantic content of "activities entail their own
    imperfective": "John was running" at I entails "John ran" at
    every subinterval of I. -/
theorem activity_entailment
    (P : EventPred W Time) (hSub : HasClosedSubintervalProp P)
    (w : W) (e₁ : Eventuality Time) (hP : P w e₁)
    (t : Interval Time) (hSub' : t.subinterval e₁.τ) :
    ∃ (e₂ : Eventuality Time), e₂.τ = t ∧ P w e₂ :=
  hSub e₁ w hP t hSub'

/-- **Imperfective paradox** (@cite{smith-1997} p. 29):
    The subinterval property fails for accomplishments. This is why
    "John was building a house" does not entail "John built a house":
    proper subintervals of a house-building event are not themselves
    house-building events (the result state is missing).

    The hypothesis `t₁ < t₂` ensures Time is nontrivial — in a singleton
    Time there is only one interval and the SIP holds vacuously for all P.
    With two distinct time points, we can construct a "telic" predicate
    P that holds only for events spanning the full interval [t₁, t₂]
    and fails for proper subintervals like [t₁, t₁]. -/
theorem imperfective_paradox_possible
    (w : W) (t₁ t₂ : Time) (hlt : t₁ < t₂) :
    ¬ (∀ (P : EventPred W Time), HasSubintervalProp P) := by
  intro hall
  -- Define a "telic" predicate: P holds iff the event's runtime ends at t₂
  let P : EventPred W Time := λ _ e => e.τ.finish = t₂
  have hSub := hall P
  -- Construct an event e₁ with runtime [t₁, t₂]; P holds (finish = t₂)
  let e₁ : Eventuality Time := ⟨⟨t₁, t₂, le_of_lt hlt⟩⟩
  have hPe₁ : P w e₁ := rfl
  -- [t₁, t₁] is a subinterval of [t₁, t₂]
  let sub : Interval Time := ⟨t₁, t₁, le_refl t₁⟩
  have hSI : sub.subinterval e₁.τ := ⟨le_refl t₁, le_of_lt hlt⟩
  -- SIP says P must hold for any event with runtime [t₁, t₁]
  let e₂ : Eventuality Time := ⟨sub⟩
  have hPe₂ := hSub e₁ w hPe₁ sub hSI e₂ rfl
  -- But P w e₂ means t₁ = t₂, contradicting t₁ < t₂
  exact absurd hPe₂ (ne_of_lt hlt)

-- ════════════════════════════════════════════════════
-- § IMPF ⊢ PRFV for Homogeneous Predicates
-- ════════════════════════════════════════════════════

/-! The central result connecting aspect operators to the subinterval
    property. For predicates with the closed SIP (states, activities),
    the imperfective entails the perfective at the same interval:

      CSIP(P) → IMPF(P)(w)(t) → PRFV(P)(w)(t)

    This is the formal reason the imperfective paradox does NOT arise
    for homogeneous predicates. "Mary was running" (IMPF) entails
    "Mary ran" (PRFV) because any subinterval of a running event is
    itself a running event — so the reference time t, which is inside
    the event's runtime, is itself the runtime of a running event.

    Combined with `imperfective_paradox_possible` (which shows that
    predicates without the SIP can fail this entailment), this gives
    a complete characterization:

      IMPF entails PRFV ⟺ the predicate has the subinterval property

    The proof:
    1. IMPF gives us event e with t ⊂ τ(e) and P(w, e)
    2. properSubinterval implies subinterval: t ⊆ τ(e)
    3. CSIP with e, w, t yields witness e₂ with τ(e₂) = t and P(w, e₂)
    4. Since τ(e₂) = t ⊆ t (reflexive), PRFV holds with witness e₂ -/

/-- **IMPF entails PRFV for CSIP predicates** (@cite{smith-1997} Ch. 2).
    If P has the closed subinterval property, then IMPF(P)(w)(t) entails
    PRFV(P)(w)(t) — the imperfective entails the perfective at the same
    reference interval.

    This is why "Mary was running" entails "Mary ran": the reference
    time t is properly inside the running event's runtime, and since
    running has the CSIP, there exists a running event whose runtime
    IS exactly t, which satisfies the PRFV containment requirement. -/
theorem impf_entails_prfv_of_csip
    (P : EventPred W Time) (hCSIP : HasClosedSubintervalProp P)
    (w : W) (t : Interval Time) :
    IMPF P w t → PRFV P w t := by
  intro ⟨e, hPSub, hP⟩
  -- hPSub : t.properSubinterval e.τ — reference time properly inside event
  -- hPSub.1 : t.subinterval e.τ — non-strict containment (first component)
  -- hP : P w e — the predicate holds for e
  obtain ⟨e₂, he₂, hPe₂⟩ := hCSIP e w hP t hPSub.1
  -- e₂ : event with τ(e₂) = t and P(w, e₂)
  -- For PRFV we need τ(e₂) ⊆ t, i.e. t ⊆ t (since τ(e₂) = t)
  exact ⟨e₂, he₂ ▸ Interval.subinterval_refl t, hPe₂⟩

/-- **CSIP is necessary for IMPF→PRFV** (converse of `impf_entails_prfv_of_csip`):
    if IMPF entails PRFV for ALL predicates, then every predicate has CSIP.

    Combined with the forward direction, this gives a complete characterization:
      (∀ P, IMPF(P) ⊆ PRFV(P)) ⟺ (∀ P, CSIP(P))

    The proof uses the **refined predicate trick**: given P, e, w, t with
    P(w,e) and t ⊆ τ(e), we apply the hypothesis not to P directly but
    to Q(w', e') := P(w', e') ∧ t ⊆ τ(e'). Then:
    - PRFV gives τ(e₂) ⊆ t (event contained in reference time)
    - Q gives t ⊆ τ(e₂) (from the predicate's second conjunct)
    - Mutual containment gives τ(e₂) = t (closing the ⊆ → = gap) -/
theorem csip_necessary_for_impf_prfv :
    (∀ (P : EventPred W Time) (w : W) (t : Interval Time),
      IMPF P w t → PRFV P w t) →
    ∀ (P : EventPred W Time), HasClosedSubintervalProp P := by
  intro hall P e w hP t hSub
  -- Case split: τ(e) = t or τ(e) ≠ t
  by_cases heq : e.τ = t
  · -- τ(e) = t: e itself witnesses CSIP
    exact ⟨e, heq, hP⟩
  · -- τ(e) ≠ t: t is a proper subinterval of τ(e)
    -- Step 1: derive properness from subinterval + inequality
    have hProper : t.properSubinterval e.τ := by
      refine ⟨hSub, ?_⟩
      by_contra hne
      push Not at hne
      -- hne : t.start ≤ e.τ.start ∧ e.τ.finish ≤ t.finish
      apply heq
      have ⟨h1, h2⟩ := hSub
      -- h1 : e.τ.start ≤ t.start, h2 : t.finish ≤ e.τ.finish
      have hs := le_antisymm h1 hne.1
      have hf := le_antisymm hne.2 h2
      rcases e with ⟨⟨_, _, _⟩⟩; rcases t with ⟨_, _, _⟩; simp_all
    -- Step 2: refined predicate Q carries reverse containment
    let Q : EventPred W Time := fun w' e' => P w' e' ∧ t.subinterval e'.τ
    -- IMPF(Q)(w)(t): witnessed by e (proper subinterval + P holds + t ⊆ τ(e))
    obtain ⟨e₂, hSub₂, hPe₂, hSubRev⟩ := hall Q w t ⟨e, hProper, hP, hSub⟩
    -- hSub₂ : τ(e₂) ⊆ t (from PRFV), hSubRev : t ⊆ τ(e₂) (from Q)
    -- Mutual containment → equality
    refine ⟨e₂, ?_, hPe₂⟩
    have ⟨a1, a2⟩ := hSub₂
    have ⟨b1, b2⟩ := hSubRev
    rcases e₂ with ⟨⟨_, _, _⟩⟩; rcases t with ⟨_, _, _⟩
    simp only [Eventuality.τ, Interval.mk.injEq]
    exact ⟨le_antisymm b1 a1, le_antisymm a2 b2⟩

end Semantics.Tense.Aspect.SubintervalProperty
