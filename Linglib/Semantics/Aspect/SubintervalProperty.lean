/-
Copyright (c) 2026 Linglib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.UpperLower.Basic
import Linglib.Semantics.Aspect.Basic

/-!
# The Subinterval Property

The subinterval property ([bennett-partee-1972], [dowty-1979]) is a fundamental
semantic property of event predicates that diagnoses the atelic/telic
(homogeneous/non-homogeneous) division of aspectual classes:

- **Statives and activities** have it: if John is sleeping for [1pm, 3pm],
  he is sleeping at every subinterval
- **Accomplishments and achievements** lack it: if John built a house in
  [Jan, Dec], he did not build a house in [Jan, Feb]

It does *not* by itself fix the full four-way Vendler class (state vs. activity
and accomplishment vs. achievement need stativity/punctuality diagnostics);
it draws only the homogeneous/non-homogeneous line.

This property underlies the semantics of temporal adverbials
([rouillard-2026]) and interacts with the aspectual sensitivity of boundary
adverbials ([iatridou-zeijlstra-2021]) and the distribution of progressive
and imperfective aspect crosslinguistically.

This is general event-predicate substrate, not specific to any particular
analysis — consumed by `Studies/Rouillard2026.lean`,
`Studies/IatridouZeijlstra2021.lean`,
`Studies/OgiharaSteinertThrelkeld2024.lean`, and the run-time projection in
`Semantics/Tense/TemporalConnectives/Projection.lean`.
-/

namespace Semantics.Aspect.SubintervalProperty

open Semantics.Aspect

variable {W Time : Type*} [LinearOrder Time]

/-- **Subinterval property for event predicates** (mereological version).
    SUB(P) iff every subinterval of a P-event's runtime that is also
    the runtime of some event is the runtime of a P-event.
    States and activities have this property; accomplishments/achievements
    lack it.

    This is the *universal-over-witnesses* form: it constrains only those
    subintervals that already happen to be some event's runtime. It is
    therefore **vacuously satisfiable** when the event ontology is sparse
    (no event has runtime exactly `t` ⇒ the inner `∀ e₂` is empty). The
    contentful, witness-*producing* form is `HasClosedSubintervalProp`
    (CSUB) below, which every operator-level theorem in this file consumes;
    plain SUB is the weaker conditional and does not on its own express
    Bennett-Partee/Dowty homogeneity.

    The `Stratified.SubintervalReference` decomposition form at
    [champollion-2017]'s analogous parameter-space point (dim = τ,
    point-interval granularity) is genuinely different math — ∃-decomposition
    over P-parts vs ∀-projection over hypothetical witness events; the
    distinctness is backed by the counterexamples in
    `Semantics/Aspect/Stratified.lean`. The quantifier-level cousin
    ([zhao-2025] ATOM-DIST_t) lives in `Semantics/Aspect/AtomDist.lean`. The
    three formulations are NOT directly interderivable; bridging requires
    explicit witness-existence assumptions. -/
def HasSubintervalProp (P : W → Event Time → Prop) : Prop :=
  ∀ (e₁ : Event Time) (w : W),
    P w e₁ →
    ∀ (t : NonemptyInterval Time), t ≤ e₁.τ →
    ∀ (e₂ : Event Time), e₂.τ = t →
    P w e₂

/-- **Closed subinterval property** (CSUB): `P`'s run-times form a *lower set*.

    This is the contentful homogeneity property — `eventDenotation (P w ·)`
    (the run-time image, `Semantics/Events/Basic.lean`) is downward-closed in
    `NonemptyInterval Time` at every world. Equivalently, for any subinterval
    `t` of a P-event's runtime there *exists* a P-event whose runtime is `t`
    (the witness form — see `hasClosedSubintervalProp_iff_witnesses`).

    CSUB is exactly **Krifka divisivity** of the run-time image: `DIV`
    ([champollion-2017]; `Semantics/Mereology.lean`) is by definition
    `IsLowerSet`, so `HasClosedSubintervalProp P ↔ ∀ w, DIV (eventDenotation (P w ·))`
    holds definitionally. Stating CSUB directly on mathlib's `IsLowerSet`
    collapses three former encodings of the same concept — the bespoke
    ∀∀∃ witness predicate, `Mereology.DIV`, and the lower-set fact proved
    ad hoc in `Tense/TemporalConnectives/Projection.lean` — onto one carrier.

    Stronger than `HasSubintervalProp` (SUB): SUB only constrains witnesses
    that already exist and is vacuous under a sparse event ontology; CSUB
    *produces* a witness at every subinterval, which is what every
    operator-level theorem below consumes. -/
def HasClosedSubintervalProp (P : W → Event Time → Prop) : Prop :=
  ∀ w, IsLowerSet (eventDenotation (fun e => P w e))

/-- **CSUB ⟺ the witness form.** Unfolds the lower-set definition to the
    classic Bennett-Partee/Dowty statement: every subinterval of a P-event's
    runtime is itself the runtime of some P-event. Operator-level theorems
    consume CSUB through this characterization. -/
theorem hasClosedSubintervalProp_iff_witnesses {P : W → Event Time → Prop} :
    HasClosedSubintervalProp P ↔
      ∀ (e₁ : Event Time) (w : W), P w e₁ →
        ∀ (t : NonemptyInterval Time), t ≤ e₁.τ →
        ∃ (e₂ : Event Time), e₂.τ = t ∧ P w e₂ := by
  constructor
  · intro h e₁ w hP t ht
    obtain ⟨e₂, hPe₂, he₂⟩ := h w ht (mem_eventDenotation_of hP)
    exact ⟨e₂, he₂, hPe₂⟩
  · intro h w a b hba ha
    obtain ⟨e₁, hPe₁, rfl⟩ := ha
    obtain ⟨e₂, he₂, hPe₂⟩ := h e₁ w hPe₁ b hba
    exact ⟨e₂, hPe₂, he₂⟩

-- ════════════════════════════════════════════════════
-- § Operator-Level Consequences
-- ════════════════════════════════════════════════════

/-! The subinterval property's consequences at the level of aspect operators.
    The atelic/telic homogeneity generalization is canonically
    [dowty-1979] / [bennett-partee-1972]; [smith-1997] supplies the
    viewpoint-classification framing (states and activities have the
    subinterval property; accomplishments, achievements, and semelfactives
    lack it).

    **Caveat — these are *extensional* results.** `IMPF`/`PRFV` here
    existentially quantify over a *completed* event in the evaluation world
    (`Basic.lean`). The genuine imperfective paradox — "John was building a
    house" can be true with no house ever completed — is *intensional* and
    requires a modal PROG over inertia/continuation worlds ([dowty-1979];
    Landman 1992; Portner 1998), which this file does NOT model. What is
    proved below is the homogeneity half: for subinterval-closed predicates
    the extensional imperfective entails the perfective, and for telic ones
    it need not.

    `Features/Aktionsart.lean` carries the VendlerClass enum used to
    state the consumer-side facts (`c = .state ∨ c = .activity` for
    SUB-having classes). Here we prove the operator-level consequences:

    1. **Activity entailment**: for CSUB predicates, holding at `e₁` yields a
       P-event at every subinterval of `e₁`'s runtime — part-whole homogeneity.
    2. **Telic non-homogeneity**: not every predicate is subinterval-closed
       (the missing-endpoint predicate is a witness).
    3. **IMPF ⊢ PRFV ⟺ CSUB**: the extensional imperfective entails the
       perfective iff the predicate has the closed subinterval property. -/

open Features

/-- **Activity entailment** ([dowty-1979]; [bennett-partee-1972]):
    if an activity predicate `P` has the closed subinterval property and
    holds of event `e₁`, then every subinterval `t` of `e₁`'s runtime is
    itself the runtime of a P-event.

    Formally: `HasClosedSubintervalProp P → P w e₁ → t ≤ e₁.τ →
    ∃ e₂, e₂.τ = t ∧ P w e₂`.

    This is the part-whole homogeneity behind "activities entail their own
    imperfective" — "John was running" entails "John ran" at every
    subinterval. It is the witness form of CSUB
    (`hasClosedSubintervalProp_iff_witnesses`). -/
theorem activity_entailment
    (P : W → Event Time → Prop) (hSub : HasClosedSubintervalProp P)
    (w : W) (e₁ : Event Time) (hP : P w e₁)
    (t : NonemptyInterval Time) (hSub' : t ≤ e₁.τ) :
    ∃ (e₂ : Event Time), e₂.τ = t ∧ P w e₂ :=
  hasClosedSubintervalProp_iff_witnesses.mp hSub e₁ w hP t hSub'

/-- **Telic non-homogeneity** (the extensional core of the imperfective
    paradox, [dowty-1979]): the subinterval property is not universal — some
    predicates fail it. This is why "John was building a house" does not
    entail "John built a house": proper subintervals of a house-building
    event are not themselves house-building events (the result state is
    missing). (The *full* paradox — truth without any completed event — is
    intensional and modeled elsewhere; see the section caveat above. This
    theorem only exhibits a non-subinterval-closed predicate.)

    The hypothesis `t₁ < t₂` ensures Time is nontrivial — in a singleton
    Time there is only one interval and SUB holds vacuously for all P.
    With two distinct time points, we construct a "telic" predicate
    P that holds only for events finishing at t₂ and fails for proper
    subintervals like [t₁, t₁]. -/
theorem imperfective_paradox_possible
    (w : W) (t₁ t₂ : Time) (hlt : t₁ < t₂) :
    ¬ (∀ (P : W → Event Time → Prop), HasSubintervalProp P) := by
  intro hall
  -- Define a "telic" predicate: P holds iff the event's runtime ends at t₂
  let P : W → Event Time → Prop := λ _ e => e.τ.snd = t₂
  have hSub := hall P
  -- Construct an event e₁ with runtime [t₁, t₂]; P holds (finish = t₂)
  -- sort is irrelevant here (defaults to .dynamic); the proof never reads .sort
  let e₁ : Event Time := ⟨⟨⟨t₁, t₂⟩, le_of_lt hlt⟩, .dynamic⟩
  have hPe₁ : P w e₁ := rfl
  -- [t₁, t₁] is a subinterval of [t₁, t₂]
  let sub : NonemptyInterval Time := ⟨⟨t₁, t₁⟩, le_refl t₁⟩
  have hSI : sub ≤ e₁.τ := NonemptyInterval.le_def.mpr ⟨le_refl t₁, le_of_lt hlt⟩
  -- SIP says P must hold for any event with runtime [t₁, t₁]
  -- sort is irrelevant here (defaults to .dynamic); the proof never reads .sort
  let e₂ : Event Time := ⟨sub, .dynamic⟩
  have hPe₂ := hSub e₁ w hPe₁ sub hSI e₂ rfl
  -- But P w e₂ means t₁ = t₂, contradicting t₁ < t₂
  exact absurd hPe₂ (ne_of_lt hlt)

-- ════════════════════════════════════════════════════
-- § IMPF ⊢ PRFV for Homogeneous Predicates
-- ════════════════════════════════════════════════════

/-! The central result connecting aspect operators to the subinterval
    property. For predicates with the closed subinterval property (CSUB —
    states, activities), the extensional imperfective entails the perfective
    at the same interval:

      CSUB(P) → IMPF(P)(w)(t) → PRFV(P)(w)(t)

    This is the formal reason the (extensional) imperfective paradox does NOT
    arise for homogeneous predicates. "Mary was running" (IMPF) entails
    "Mary ran" (PRFV) because any subinterval of a running event is
    itself a running event — so the reference time t, which is inside
    the event's runtime, is itself the runtime of a running event.

    Combined with `csub_necessary_for_impf_prfv` (the converse), this gives
    a complete characterization:

      (∀ P, IMPF(P) ⊆ PRFV(P)) ⟺ (∀ P, CSUB(P))

    The proof:
    1. IMPF gives us event e with t ⊂ τ(e) and P(w, e)
    2. proper containment implies containment: t ≤ τ(e)
    3. CSUB with e, w, t yields witness e₂ with τ(e₂) = t and P(w, e₂)
    4. Since τ(e₂) = t ≤ t (reflexive), PRFV holds with witness e₂ -/

/-- **IMPF entails PRFV for CSUB predicates** ([dowty-1979]; [smith-1997]).
    If P has the closed subinterval property, then IMPF(P)(w)(t) entails
    PRFV(P)(w)(t) — the (extensional) imperfective entails the perfective at
    the same reference interval.

    This is why "Mary was running" entails "Mary ran": the reference
    time t is properly inside the running event's runtime, and since
    running has CSUB, there exists a running event whose runtime
    IS exactly t, which satisfies the PRFV containment requirement. -/
theorem impf_entails_prfv_of_csub
    (P : W → Event Time → Prop) (hCSUB : HasClosedSubintervalProp P)
    (w : W) (t : NonemptyInterval Time) :
    IMPF P w t → PRFV P w t := by
  intro ⟨e, hPSub, hP⟩
  -- hPSub : t < e.τ — reference time properly inside event
  -- hPSub.1 : t ≤ e.τ — non-strict containment (first component)
  -- hP : P w e — the predicate holds for e
  obtain ⟨e₂, he₂, hPe₂⟩ := hasClosedSubintervalProp_iff_witnesses.mp hCSUB e w hP t hPSub.1
  -- e₂ : event with τ(e₂) = t and P(w, e₂)
  -- For PRFV we need τ(e₂) ⊆ t, i.e. t ⊆ t (since τ(e₂) = t)
  exact ⟨e₂, he₂ ▸ le_refl t, hPe₂⟩

/-- **CSUB is necessary for IMPF→PRFV** (converse of `impf_entails_prfv_of_csub`):
    if IMPF entails PRFV for ALL predicates, then every predicate has CSUB.

    Combined with the forward direction, this gives a complete characterization:
      (∀ P, IMPF(P) ⊆ PRFV(P)) ⟺ (∀ P, CSUB(P))

    The proof uses the **refined predicate trick**: given P, e, w, t with
    P(w,e) and t ⊆ τ(e), we apply the hypothesis not to P directly but
    to Q(w', e') := P(w', e') ∧ t ⊆ τ(e'). The case split on `e.τ = t` is
    load-bearing: IMPF requires *strict* containment `t < e.τ`, so the
    equality case must be discharged by `e` itself. Then:
    - PRFV gives τ(e₂) ⊆ t (event contained in reference time)
    - Q gives t ⊆ τ(e₂) (from the predicate's second conjunct)
    - Mutual containment gives τ(e₂) = t (closing the ⊆ → = gap) -/
theorem csub_necessary_for_impf_prfv :
    (∀ (P : W → Event Time → Prop) (w : W) (t : NonemptyInterval Time),
      IMPF P w t → PRFV P w t) →
    ∀ (P : W → Event Time → Prop), HasClosedSubintervalProp P := by
  intro hall P
  rw [hasClosedSubintervalProp_iff_witnesses]
  intro e w hP t hSub
  -- Case split: τ(e) = t or τ(e) ≠ t
  by_cases heq : e.τ = t
  · -- τ(e) = t: e itself witnesses CSUB
    exact ⟨e, heq, hP⟩
  · -- τ(e) ≠ t: t is strictly contained in τ(e)
    have hProper : t < e.τ := lt_of_le_of_ne hSub (fun h => heq (h ▸ rfl))
    -- Step 2: refined predicate Q carries reverse containment
    let Q : W → Event Time → Prop := fun w' e' => P w' e' ∧ t ≤ e'.τ
    -- IMPF(Q)(w)(t): witnessed by e (proper subinterval + P holds + t ⊆ τ(e))
    obtain ⟨e₂, hSub₂, hPe₂, hSubRev⟩ := hall Q w t ⟨e, hProper, hP, hSub⟩
    -- hSub₂ : τ(e₂) ⊆ t (from PRFV), hSubRev : t ⊆ τ(e₂) (from Q)
    -- Mutual containment → equality (antisymmetry of the containment order)
    exact ⟨e₂, le_antisymm hSub₂ hSubRev, hPe₂⟩

end Semantics.Aspect.SubintervalProperty
