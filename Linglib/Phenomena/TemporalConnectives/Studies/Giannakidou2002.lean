import Linglib.Phenomena.TemporalConnectives.Studies.Karttunen1974
import Linglib.Theories.Semantics.Tense.Aspect.Core
import Linglib.Phenomena.TemporalConnectives.NegationData
import Linglib.Fragments.Greek.TemporalConnectives

/-!
# Giannakidou (2002): UNTIL, Aspect, and Negation
@cite{giannakidou-2002} @cite{karttunen-1974} @cite{klein-1994}
@cite{de-swart-1996} @cite{de-swart-molendijk-1999}

A Novel Argument for Two *Until*s. Semantics and Linguistic Theory 12, 84–103.

## Central Argument

Viewpoint aspect determines negation scope with *until*:

- **Imperfective main clause**: homogeneous (subinterval property), satisfying
  durative *until*'s selectional restriction. Both wide-scope and narrow-scope
  negation are available.

- **Perfective main clause**: not homogeneous. Only narrow-scope negation
  (= Karttunen's ¬*before*) is available.

This provides a novel argument for @cite{karttunen-1974}'s two-*until*
hypothesis: the scope readings are logically independent, so the restriction
to narrow scope under PRFV is a genuine empirical constraint, not a logical
consequence.

A secondary contribution (§6) refines @cite{karttunen-1974}'s identity
NPI-*until* = ¬*before*: while truth-conditionally valid, *para monon*
(NPI-*until*) and *prin* (*before*) differ on **actualization** — NPI-*until*
entails the main-clause event occurred, *before* does not — and on scope
interaction with imperfective aspect.

## Architecture

Uses `Aspect.Core.UNBOUNDED` (= non-strict IMPF, @cite{pancheva-2003}) projected
to `SentDenotation` for the imperfective denotation:

```
EventPred Unit Time ──[UNBOUNDED]──▷ IntervalPred ──[fix w=()]──▷ SentDenotation
```

The key property — subinterval-closure — holds for both `UNBOUNDED` (⊆) and
`IMPF` (⊂); we use `UNBOUNDED` because the argument doesn't depend on the
strict/non-strict distinction and the non-strict version connects cleanly to
`stativeDenotation` in `Basic.lean`.

## Key Results

1. `impfDen_subinterval_closed`: IMPF gives homogeneity
2. `prfvDen_not_subinterval_closed`: PRFV does not
3. `scope_readings_distinct`/`scope_readings_independent`: logically independent
4. `impfDen_homogeneous`/`prfvDen_not_always_homogeneous`: wide scope derived
5. `wideScopeNotUntil_compatible_with_empty_main`: wide scope lacks actualization
6. `eventiveUntil_entails_actualization`: NPI-until entails actualization
7. `negBefore_lacks_actualization`: ¬*before* compatible with no main-clause event
8. `before_not_equiv_eventiveUntil`: ¬*before* ≠ NPI-*until* on actualization (§6)
9. `stativizer_all_wrong`: all five diagnostics refute @cite{de-swart-1996} (§5)

-/

namespace Phenomena.TemporalConnectives.Studies.Giannakidou2002

open Core.Time
open Core.Time.Interval
open Semantics.Tense.Aspect.Core
open Semantics.Tense.TemporalConnectives

variable {Time : Type*} [LinearOrder Time]

-- ============================================================================
-- § 1: Aspect.Core → SentDenotation Projection
-- ============================================================================

/-- IMPF denotation: project `Aspect.Core.UNBOUNDED` to `SentDenotation`.
    Each interval in the denotation is a subinterval of some event runtime
    (@cite{klein-1994}: TT ⊆ TSit). Uses `UNBOUNDED` (@cite{pancheva-2003})
    rather than `IMPF` (which requires strict ⊂) because the homogeneity
    argument is identical and the non-strict version connects cleanly to
    `stativeDenotation`. -/
abbrev impfDen (P : EventPred Unit Time) : SentDenotation Time :=
  { i | UNBOUNDED P () i }

/-- PRFV denotation: the set of exact event runtimes.
    Unlike the `Aspect.Core.PRFV` operator (which gives intervals CONTAINING
    the runtime: TSit ⊆ TT), this gives the τ-image {τ(e) | P(e)} — the
    interval set that directly characterizes the event's temporal extent.
    This matches the `eventDenotation` pattern from `EventBridge.lean`. -/
def prfvDen (P : EventPred Unit Time) : SentDenotation Time :=
  { i | ∃ e : Eventuality Time, P () e ∧ e.τ = i }

-- ============================================================================
-- § 2: Homogeneity
-- ============================================================================

/-- A sentence denotation is homogeneous (subinterval-closed) when membership
    is preserved under subintervals. This is Karttunen's selectional restriction
    for durative *until*: the main clause must be homogeneous. -/
def IsHomogeneous (D : SentDenotation Time) : Prop :=
  ∀ t ∈ D, ∀ t', t'.subinterval t → t' ∈ D

/-- IMPF denotation satisfies the subinterval property.

    This is exactly the homogeneity property that @cite{karttunen-1974} requires
    of the main clause of durative *until*. The imperfective viewpoint
    provides this automatically: since the event extends beyond any reference
    interval, every sub-window into the event is equally valid. -/
theorem impfDen_subinterval_closed (P : EventPred Unit Time)
    (t : Interval Time) (ht : t ∈ impfDen P)
    (t' : Interval Time) (ht' : t'.subinterval t) :
    t' ∈ impfDen P := by
  obtain ⟨e, hSub, hP⟩ := ht
  exact ⟨e, ⟨le_trans hSub.1 ht'.1, le_trans ht'.2 hSub.2⟩, hP⟩

/-- IMPF denotation contains the event runtime itself (the maximal interval). -/
theorem impfDen_contains_runtime (P : EventPred Unit Time)
    (e : Eventuality Time) (hP : P () e) :
    e.τ ∈ impfDen P :=
  ⟨e, subinterval_refl _, hP⟩

/-- PRFV denotation does NOT have the subinterval property.

    Counterexample: An event with runtime [0, 5]. The interval [0, 5] is
    in the denotation, but [1, 3] (a strict subinterval) is not — PRFV
    only includes the exact runtime.

    This is why perfective clauses cannot be main clauses of durative
    *until*: they lack the homogeneity that *until* requires. -/
theorem prfvDen_not_subinterval_closed :
    ¬ ∀ (P : EventPred Unit ℤ) (t : Interval ℤ),
      t ∈ prfvDen P → ∀ t', t'.subinterval t → t' ∈ prfvDen P := by
  intro h
  let e₀ : Eventuality ℤ := ⟨⟨0, 5, by omega⟩⟩
  let P : EventPred Unit ℤ := fun _ e => e = e₀
  let sub : Interval ℤ := ⟨1, 3, by omega⟩
  have hrt : e₀.τ ∈ prfvDen P := ⟨e₀, rfl, rfl⟩
  have hsub : sub.subinterval e₀.τ := by
    dsimp only [sub, e₀]
    simp only [subinterval, Eventuality.τ]; omega
  have hmem := h P e₀.τ hrt sub hsub
  obtain ⟨e', he', hτ⟩ := hmem
  dsimp only [P] at he'
  subst he'
  simp only [Eventuality.τ] at hτ
  have : (0 : ℤ) = 1 := congrArg Interval.start hτ
  omega

-- ============================================================================
-- § 3: Scope Pattern (Derived from Homogeneity)
-- ============================================================================

/-- IMPF denotation is homogeneous — wide scope is available. -/
theorem impfDen_homogeneous (P : EventPred Unit Time) :
    IsHomogeneous (impfDen P) :=
  impfDen_subinterval_closed P

/-- PRFV denotation is not always homogeneous — wide scope is not always
    available. This is derived from the subinterval-closure failure, not
    stipulated as a Bool field. -/
theorem prfvDen_not_always_homogeneous :
    ¬ ∀ (P : EventPred Unit ℤ), IsHomogeneous (prfvDen P) := by
  intro h
  exact prfvDen_not_subinterval_closed fun P t ht t' ht' => h P t ht t' ht'

/-- @cite{giannakidou-2002}'s scope generalization, derived from homogeneity:
    wide-scope negation requires a homogeneous main clause, which IMPF provides
    and PRFV does not. The restriction to narrow scope under PRFV follows from
    PRFV's failure of subinterval-closure, not from a stipulated constraint. -/
theorem scope_pattern_derived :
    -- IMPF always permits wide scope (homogeneous)
    (∀ (P : EventPred Unit Time), IsHomogeneous (impfDen P)) ∧
    -- PRFV does not always permit wide scope (not always homogeneous)
    ¬ (∀ (P : EventPred Unit ℤ), IsHomogeneous (prfvDen P)) :=
  ⟨impfDen_homogeneous, prfvDen_not_always_homogeneous⟩

-- ============================================================================
-- § 4: Connection to stativeDenotation
-- ============================================================================

/-- For a single event with runtime `i`, the IMPF denotation is exactly
    the stative denotation of `i` (all subintervals). This connects the
    aspect bridge to the existing temporal connective infrastructure
    in `Basic.lean`. -/
theorem impfDen_singleton_eq_stativeDenotation
    (i : Interval Time) :
    impfDen (fun () (e : Eventuality Time) => e.τ = i) =
    stativeDenotation i := by
  ext j
  simp only [UNBOUNDED, stativeDenotation, Set.mem_setOf_eq, Eventuality.τ]
  constructor
  · rintro ⟨e, hSub, rfl⟩; exact hSub
  · intro h; exact ⟨⟨i⟩, h, rfl⟩

/-- For a single event, the PRFV denotation is exactly the accomplishment
    denotation (singleton containing just the runtime). -/
theorem prfvDen_singleton_eq_accomplishmentDenotation
    (i : Interval Time) :
    prfvDen (fun () (e : Eventuality Time) => e.τ = i) =
    accomplishmentDenotation i := by
  ext j
  simp only [prfvDen, accomplishmentDenotation,
    Set.mem_setOf_eq, Eventuality.τ]
  constructor
  · rintro ⟨e, rfl, rfl⟩; rfl
  · intro h; exact ⟨⟨i⟩, rfl, h.symm⟩

-- ============================================================================
-- § 5: Time Traces Coincide
-- ============================================================================

/-- The time traces of IMPF and PRFV denotations are identical: both equal
    the set of times contained in some event runtime.

    This is why Karttunen's Level 1 (point-set) definitions cannot distinguish
    imperfective from perfective clauses — the difference is only visible
    at Level 2 (interval sets). -/
theorem timeTrace_impf_eq_prfv (P : EventPred Unit Time) :
    timeTrace (impfDen P) = timeTrace (prfvDen P) := by
  ext t
  simp only [timeTrace, prfvDen, UNBOUNDED, Set.mem_setOf_eq, Eventuality.τ]
  constructor
  · rintro ⟨i, ⟨e, hSub, hP⟩, ht⟩
    exact ⟨e.τ, ⟨e, hP, rfl⟩,
      ⟨le_trans hSub.1 ht.1, le_trans ht.2 hSub.2⟩⟩
  · rintro ⟨i, ⟨e, hP, rfl⟩, ht⟩
    exact ⟨Interval.point t,
      ⟨e, ⟨ht.1, ht.2⟩, hP⟩, ⟨le_refl _, le_refl _⟩⟩

-- ============================================================================
-- § 6: Scope Readings
-- ============================================================================

/-- **Wide-scope negation** over imperfective *until*:

    ¬∃t [t ∈ timeTrace(IMPF(A)) ∧ t ∈ timeTrace(B)]

    "It's not the case that A was ongoing up to the time of B."

    Available when A is imperfective: the main clause denotes a homogeneous
    interval set via IMPF, so *until* can take it as an argument.
    Negation scopes over the entire *until*-clause. -/
def wideScopeNotUntil (A : EventPred Unit Time) (B : SentDenotation Time) : Prop :=
  ¬ Karttunen.when_ (impfDen A) B

/-- **Narrow-scope negation** under *until* (= Karttunen's ¬*before*):

    ¬(A BEFORE B)

    "A didn't happen before B" — the event occurred, but not prior to B.

    This is the only reading available with perfective main clauses:
    since PRFV gives a bounded event, *until* reduces to temporal ordering
    and negation gives Karttunen's notUntil = ¬before. -/
def narrowScopeNotUntil (A : EventPred Unit Time) (B : SentDenotation Time) : Prop :=
  Karttunen.notUntil (prfvDen A) B

/-- Narrow-scope ¬*until* is exactly ¬*before* (by definition).
    This is @cite{karttunen-1974}'s identity, now made explicit in the
    aspectual decomposition. -/
theorem narrowScope_eq_not_before (A : EventPred Unit Time) (B : SentDenotation Time) :
    narrowScopeNotUntil A B ↔ ¬ Anscombe.before (prfvDen A) B :=
  Iff.rfl

/-- The two scope readings are **semantically distinct**: there exist A, B
    where wide-scope holds but narrow-scope fails.

    Counterexample: event A with runtime [0, 5], B at time 7.
    - Wide scope: ¬(any A-time overlaps with time 7). TRUE — 7 ∉ [0, 5].
    - Narrow scope: ¬(A happened before B). FALSE — time 0 < 7, so A
      precedes B and `Anscombe.before` holds. -/
theorem scope_readings_distinct :
    ∃ (A : EventPred Unit ℤ) (B : SentDenotation ℤ),
      wideScopeNotUntil A B ∧ ¬ narrowScopeNotUntil A B := by
  let e₀ : Eventuality ℤ := ⟨⟨0, 5, by omega⟩⟩
  let A : EventPred Unit ℤ := fun _ e => e = e₀
  let iB : Interval ℤ := ⟨7, 7, by omega⟩
  let B : SentDenotation ℤ := {iB}
  refine ⟨A, B, ?_, ?_⟩
  · intro ⟨t, ht_A, ht_B⟩
    obtain ⟨i, ⟨e, hSub, he⟩, hi⟩ := ht_A
    dsimp only [A] at he; subst he
    obtain ⟨j, (hj : j = iB), hjt⟩ := ht_B
    subst hj
    simp only [subinterval, contains, Eventuality.τ, e₀, iB] at hSub hi hjt
    omega
  · intro hNot
    apply hNot
    refine ⟨0, ⟨e₀.τ, ⟨e₀, rfl, rfl⟩, ?_⟩, ?_⟩
    · simp only [contains, Eventuality.τ, e₀]; omega
    · intro t' ⟨j, (hj : j = iB), hjt⟩
      subst hj
      simp only [contains, iB] at hjt; omega

/-- The reverse also holds: there exist A, B where narrow-scope holds
    but wide-scope fails. This confirms the two readings are genuinely
    independent. -/
theorem scope_readings_independent :
    ∃ (A : EventPred Unit ℤ) (B : SentDenotation ℤ),
      ¬ wideScopeNotUntil A B ∧ narrowScopeNotUntil A B := by
  let e₀ : Eventuality ℤ := ⟨⟨5, 10, by omega⟩⟩
  let A : EventPred Unit ℤ := fun _ e => e = e₀
  let iB : Interval ℤ := ⟨3, 7, by omega⟩
  let B : SentDenotation ℤ := {iB}
  refine ⟨A, B, ?_, ?_⟩
  · intro hWide
    apply hWide
    refine ⟨5,
      ⟨Interval.point 5, ⟨e₀, by
        simp only [subinterval, Interval.point, Eventuality.τ, e₀]; omega,
        rfl⟩,
        by simp only [contains, Interval.point]; omega⟩,
      ⟨iB, rfl, by simp only [contains, iB]; omega⟩⟩
  · intro ⟨t, ht_A, hall⟩
    obtain ⟨i, ⟨e, he, hτ⟩, hi⟩ := ht_A
    dsimp only [A] at he; subst he
    rw [← hτ] at hi
    simp only [contains, Eventuality.τ, e₀] at hi
    have h3 : (3 : ℤ) ∈ timeTrace B :=
      ⟨iB, rfl, by simp only [contains, iB]; omega⟩
    have := hall 3 h3
    omega

-- ============================================================================
-- § 7: Eventive UNTIL (para monon) Semantics (@cite{giannakidou-2002}, §3.2)
-- ============================================================================

/-- **Eventive UNTIL**: the semantics of Greek *para monon* and Karttunen's
    punctual *until*. Combines temporal coincidence (A overlaps B) with
    lateness (A does not precede B):

    ⟦dhen P para monon Q⟧ = (∃t. t∈A ∧ t∈B) ∧ ¬(A before B)

    This builds actualization into the **assertion**, unlike
    `Karttunen.notUntil` (= ¬before alone) which holds vacuously when A is
    empty.

    This is a simplified version of the full ex. (39), which additionally
    includes a contextual restriction C over the scale of relevant times:
    `¬∃t'∃e' [t'∈C ∧ t'<t ∧ P(e',t')]`. The scalar/contextual component
    is abstracted away here; the core truth-conditional difference (overlap +
    lateness vs. lateness alone) is preserved. -/
def eventiveUntil (A B : SentDenotation Time) : Prop :=
  (∃ t, t ∈ timeTrace A ∧ t ∈ timeTrace B) ∧ ¬ Anscombe.before A B

-- ============================================================================
-- § 8: Actualization Asymmetry
-- ============================================================================

/-- Eventive UNTIL entails main-clause actualization: A must have occurred.
    This is the **actualization entailment** that @cite{giannakidou-2002}
    identifies as the hallmark of NPI-*until* (para monon), absent from
    durative *until* (mexri) and before (prin). -/
theorem eventiveUntil_entails_actualization (A B : SentDenotation Time) :
    eventiveUntil A B → ∃ t, t ∈ timeTrace A := by
  rintro ⟨⟨t, ht, _⟩, _⟩; exact ⟨t, ht⟩

/-- Eventive UNTIL entails complement actualization: B must have occurred. -/
theorem eventiveUntil_entails_complement (A B : SentDenotation Time) :
    eventiveUntil A B → ∃ t, t ∈ timeTrace B := by
  rintro ⟨⟨t, _, ht⟩, _⟩; exact ⟨t, ht⟩

/-- Eventive UNTIL entails ¬*before*: A didn't happen prior to B. -/
theorem eventiveUntil_entails_notBefore (A B : SentDenotation Time) :
    eventiveUntil A B → Karttunen.notUntil A B :=
  And.right

/-- Eventive UNTIL entails temporal coincidence (*when*): A and B overlap. -/
theorem eventiveUntil_entails_when (A B : SentDenotation Time) :
    eventiveUntil A B → Karttunen.when_ A B := by
  rintro ⟨⟨t, htA, htB⟩, _⟩; exact ⟨t, htA, htB⟩

/-- Karttunen's `notUntil` does NOT entail eventive UNTIL:
    ¬(A before B) holds vacuously when A is empty (no actualization). -/
theorem notUntil_not_implies_eventiveUntil :
    ∃ (A B : SentDenotation ℤ),
      Karttunen.notUntil A B ∧ ¬ eventiveUntil A B := by
  refine ⟨∅, { Interval.point 0 }, ?_, ?_⟩
  · intro ⟨t, ⟨i, hi, _⟩, _⟩
    exact absurd hi (Set.mem_empty_iff_false i).mp
  · intro ⟨⟨t, ⟨i, hi, _⟩, _⟩, _⟩
    exact absurd hi (Set.mem_empty_iff_false i).mp

/-- **Wide-scope negation does NOT entail actualization.**

    This is the key asymmetry with eventive UNTIL (§8 above):
    NPI-*until* (para monon) entails actualization, but the Mittwoch
    reading (wide-scope negation over durative *until*) does not.

    Proved by construction: an event A with runtime [0, 5] and complement B
    at time 3. Wide-scope negation holds (the state of not-A extends beyond
    B), but A DID occur — the non-actualization is shown by the fact that
    wide-scope is COMPATIBLE with either actualization or non-actualization,
    unlike eventive UNTIL which requires it.

    This formalizes the contrast between @cite{giannakidou-2002}'s ex. (51)
    (imperfective *mexri* + continuation asserting no event) and ex. (57)
    (perfective *para monon* + contradictory continuation). -/
theorem wideScopeNotUntil_compatible_with_empty_main :
    ∃ (A : EventPred Unit ℤ) (B : SentDenotation ℤ),
      wideScopeNotUntil A B ∧ ¬ ∃ t, t ∈ timeTrace (impfDen A) := by
  let A : EventPred Unit ℤ := fun _ _ => False
  let B : SentDenotation ℤ := { Interval.point 0 }
  refine ⟨A, B, ?_, ?_⟩
  · intro ⟨t, ⟨i, ⟨e, _, habs⟩, _⟩, _⟩; exact habs
  · intro ⟨t, i, ⟨e, _, habs⟩, _⟩; exact habs

/-- Durative *until* is compatible with A preceding B:
    the main clause state can extend well before the complement time.

    This is the formal correlate of @cite{giannakidou-2002}'s ex. (7):
    "Sure, the princess slept until midnight. In fact she only woke up
    at 2am." — the state extends past the boundary, and the change-of-state
    is not entailed. -/
theorem durative_compatible_with_before :
    ∃ (A B : SentDenotation ℤ),
      Karttunen.until A B ∧ Anscombe.before A B := by
  let iA : Interval ℤ := ⟨0, 10, by omega⟩
  let iB : Interval ℤ := ⟨5, 5, by omega⟩
  refine ⟨stativeDenotation iA, {iB}, ?_, ?_⟩
  · exact ⟨5,
      ⟨iA, stativeDenotation_self iA, by simp only [contains, iA]; omega⟩,
      ⟨iB, rfl, by simp only [contains, iB]; omega⟩⟩
  · refine ⟨0,
      ⟨iA, stativeDenotation_self iA, by simp only [contains, iA]; omega⟩, ?_⟩
    intro t' ⟨j, hj, hjt⟩
    simp only [Set.mem_singleton_iff] at hj; subst hj
    simp only [contains, iB] at hjt; omega

/-- **Eventive UNTIL is strictly stronger than Karttunen's notUntil.**
    - eventiveUntil → notUntil (actualization + lateness → lateness)
    - notUntil ↛ eventiveUntil (lateness alone lacks actualization)

    This is the formal content of @cite{giannakidou-2002}'s central claim:
    the two readings are not truth-conditionally equivalent under negation. -/
theorem eventiveUntil_strictly_stronger :
    (∀ (A B : SentDenotation ℤ), eventiveUntil A B → Karttunen.notUntil A B) ∧
    (∃ (A B : SentDenotation ℤ), Karttunen.notUntil A B ∧ ¬ eventiveUntil A B) :=
  ⟨fun _ _ h => h.2, notUntil_not_implies_eventiveUntil⟩

-- ============================================================================
-- § 9: Bridge to NegationData
-- ============================================================================

open Phenomena.TemporalConnectives.NegationData

/-- The NegationData actualization three-way split aligns with the formal
    semantics: eventive-type (entailment) corresponds to `eventiveUntil`
    (overlap + lateness), endpoint-type (implicature) to `Karttunen.until`
    (overlap alone), and before-type (none) to `Karttunen.notUntil`
    (lateness alone). -/
theorem actualization_matches_semantics :
    -- Eventive type: actualization is entailed (eventiveUntil)
    greek_para_monon.actualizationStatus = .entailment ∧
    english_npi_until.actualizationStatus = .entailment ∧
    -- Endpoint type: actualization is an implicature (durative until)
    greek_mexri.actualizationStatus = .implicature ∧
    english_dur_until.actualizationStatus = .implicature ∧
    -- Before type: no actualization (¬before = notUntil)
    greek_prin.actualizationStatus = .none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The aspect diagnostic from NegationData: durative *until* (*mexri*)
    requires imperfective main clause; NPI-*until* (*para monon*) does not.
    This matches the formal result: wide-scope requires homogeneity
    (= imperfective), narrow-scope does not. -/
theorem aspect_matches_scope :
    -- mexri requires durative → wide scope requires homogeneity
    greek_mexri.requiresDurativeMain = true ∧
    -- para monon has no durative restriction → narrow scope doesn't need it
    greek_para_monon.requiresDurativeMain = false ∧
    -- prin has no durative restriction
    greek_prin.requiresDurativeMain = false :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 10: Bridge to Greek Fragment
-- ============================================================================

open Fragments.Greek.TemporalConnectives

/-- Greek lexicalizes the three semantic types as distinct lexemes:
    *mexri* (durative), *para monon* (eventive NPI), *prin* (before).
    Each maps to a different temporal connective operator:
    - *mexri* → `Karttunen.until` (= `when_`, overlap)
    - *para monon* → `eventiveUntil` (overlap + lateness)
    - *prin* → `Anscombe.before` (ordering) -/
theorem greek_three_way_maps_to_operators :
    -- mexri is durative until (endpoint type)
    mexri.order = .until_ ∧ mexri.complementVeridical = true ∧
    -- para monon is eventive NPI-until
    paraMonon.order = .until_ ∧ paraMonon.complementVeridical = false ∧
    paraMonon.forcesPunctual = true ∧
    -- prin is before
    prin.order = .before ∧ prin.complementVeridical = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The veridicality split between *mexri* (veridical) and *para monon*
    (non-veridical) corresponds to the formal difference: durative until
    presupposes the complement, while eventive until asserts both overlap
    and non-precedence. -/
theorem veridicality_split :
    mexri.complementVeridical = true ∧
    paraMonon.complementVeridical = false ∧
    prin.complementVeridical = false :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 11: Negation is NOT a Stativizer (@cite{giannakidou-2002}, §5)
-- ============================================================================

/-! @cite{giannakidou-2002} refutes the analysis of negation as an aspectual
    operator that converts eventive predicates into stative ones
    (@cite{de-swart-1996}, @cite{de-swart-molendijk-1999}). On that account,
    negation takes an eventuality description P and yields a maximal state s
    such that no event of type P is contained in s. If this were correct,
    negated perfectives should behave like statives — but they don't:
    Greek negated perfectives still reject durative *until* (*mexri*),
    reject *how long*, reject *while*, and accept imperatives. -/

/-- @cite{de-swart-1996}'s stativizer hypothesis: negation converts events
    into maximal states, so ALL negated predicates (including perfectives)
    should be homogeneous (subinterval-closed), just like true statives.

    The formal refutation: if this were correct, then PRFV denotations
    would always be homogeneous. But we proved in §2 that PRFV is NOT
    always homogeneous (`prfvDen_not_subinterval_closed`). -/
theorem stativizer_false_for_perfective :
    ¬ (∀ (P : EventPred Unit ℤ), IsHomogeneous (prfvDen P)) :=
  prfvDen_not_always_homogeneous

/-- The five stativizer diagnostics and their results for negated
    perfective forms (@cite{giannakidou-2002}, §5, ex. 67–71):

    | Diagnostic | True stative | Neg+PRFV | Stativizer predicts |
    |------------|-------------|----------|---------------------|
    | *how long* | ✓           | ✗        | ✓ (WRONG)           |
    | *while*    | ✓           | ✗        | ✓ (WRONG)           |
    | *for* adv  | ✓           | ✗        | ✓ (WRONG)           |
    | imperative | ✗           | ✓        | ✗ (WRONG)           |
    | *mexri*    | ✓           | ✗        | ✓ (WRONG)           |

    All five diagnostics give results inconsistent with stativehood for
    negated perfectives. -/
inductive StativizerDiagnostic where
  | howLong     -- *for how long* adverbial
  | while_      -- *while*-clause embedding
  | forAdverb   -- *for/in* adverbial compatibility
  | imperative  -- imperative mood
  | mexri       -- durative *until* compatibility
  deriving DecidableEq, Repr

/-- Result of applying a stativizer diagnostic. -/
structure DiagnosticResult where
  diagnostic : StativizerDiagnostic
  /-- Is this compatible with true statives? -/
  trueStativeResult : Bool
  /-- Is this compatible with negated perfectives? -/
  negPerfResult : Bool
  /-- What does the stativizer predict for negated perfectives? -/
  stativizerPredicts : Bool
  deriving Repr

def diagnosticResults : List DiagnosticResult :=
  [ ⟨.howLong,    true,  false, true⟩
  , ⟨.while_,     true,  false, true⟩
  , ⟨.forAdverb,  true,  false, true⟩
  , ⟨.imperative, false, true,  false⟩
  , ⟨.mexri,      true,  false, true⟩ ]

/-- The stativizer gets every diagnostic wrong: its prediction never
    matches the actual negated-perfective result. -/
theorem stativizer_all_wrong :
    ∀ d ∈ diagnosticResults, d.negPerfResult ≠ d.stativizerPredicts := by
  intro d hd
  simp only [diagnosticResults, List.mem_cons, List.mem_nil_iff,
             or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide

-- ============================================================================
-- § 12: English Simple Past = Covert Perfective (@cite{giannakidou-2002}, §4.3)
-- ============================================================================

/-- @cite{giannakidou-2002}'s argument that the English simple past has a
    perfective default value: English past-tense statives with *until*
    pattern with Greek PERFECTIVE, not imperfective.

    Evidence: "The princess didn't sleep until midnight" lacks the
    Mittwoch reading (no wide-scope *until*), entails actualization
    (she fell asleep at midnight), and disallows preposing
    ("*Until midnight, the princess didn't sleep"). These are exactly
    the properties of Greek negated perfective + *mexri*, not
    Greek negated imperfective + *mexri*.

    Formalized as: the scope pattern for English simple past follows
    from PRFV (not IMPF), which is why wide-scope is unavailable. -/
theorem english_past_perfective_default :
    -- PRFV lacks homogeneity → wide scope unavailable
    ¬ (∀ (P : EventPred Unit ℤ), IsHomogeneous (prfvDen P)) ∧
    -- IMPF has homogeneity → wide scope would be available if past were imperfective
    (∀ (P : EventPred Unit ℤ), IsHomogeneous (impfDen P)) :=
  ⟨prfvDen_not_always_homogeneous, impfDen_homogeneous⟩

-- ============================================================================
-- § 13: *Before* ≠ NPI-*Until* on Actualization (@cite{giannakidou-2002}, §6)
-- ============================================================================

/-! @cite{giannakidou-2002}'s §6 refines @cite{karttunen-1974}'s identity
    NPI-*until* = ¬*before*: while truth-conditionally valid at the level of
    temporal ordering, the two connectives differ on **actualization**.

    - *Prin/before*: no actualization. "I prigipisa dhen eftase prin apo ta
      mesanixta" (ex. 72) is compatible with "she arrived later or didn't
      arrive at all."
    - *Para monon*/NPI-*until*: actualization is an entailment. "I prigipisa
      dhen eftase para monon ta mesanixta" (ex. 38) is contradicted by
      "she didn't arrive that night."

    Additionally, the Mittwoch reading (wide scope) is NOT available with
    *prin* + imperfective stative (ex. 76): "I prigipisa dhen kimotane prin
    apo ta mesanixta" gives only a habitual reading ("there was a period
    during which she had the habit of not going to bed before midnight"),
    not a stative reading. This contrasts with *mexri* + IMPF (ex. 74)
    which does give the stative/Mittwoch reading. -/

/-- ¬*before* (= @cite{karttunen-1974}'s notUntil) is compatible with the
    main-clause event never occurring: when A = ∅, `¬(A before B)` holds
    vacuously since `Anscombe.before ∅ B` is always false.

    @cite{giannakidou-2002}, §6, ex. (72): "I prigipisa dhen eftase prin apo
    ta mesanixta" — the princess may or may not have arrived. *Prin/before*
    with negation does not entail actualization of the arriving event.

    Contrast with `eventiveUntil`, which requires main-clause actualization
    (the overlap conjunct forces a witness in A). -/
theorem negBefore_lacks_actualization :
    ∃ (A B : SentDenotation ℤ),
      Karttunen.notUntil A B ∧ ¬ ∃ t, t ∈ timeTrace A := by
  refine ⟨∅, { Interval.point 0 }, ?_, ?_⟩
  · intro ⟨t, ⟨i, hi, _⟩, _⟩
    exact absurd hi (Set.mem_empty_iff_false i).mp
  · intro ⟨t, i, hi, _⟩
    exact absurd hi (Set.mem_empty_iff_false i).mp

/-- **NPI-*until* ≠ ¬*before* on actualization** (@cite{giannakidou-2002}, §6).

    - `eventiveUntil A B` entails main-clause actualization (∃t ∈ A)
    - `¬(A before B)` is compatible with main-clause non-actualization (A = ∅)

    This is the formal content of @cite{giannakidou-2002}'s central §6 claim:
    @cite{karttunen-1974}'s truth-conditional identity (NPI-*until* = ¬*before*)
    holds at the level of temporal ordering, but the two connective types are
    not interchangeable — NPI-*until* additionally requires actualization.
    The impression of equivalence is a by-product of scalarity, a feature
    common to both *prin/before* and *until/para monon*. -/
theorem before_not_equiv_eventiveUntil :
    -- eventiveUntil entails main-clause actualization
    (∀ (A B : SentDenotation Time), eventiveUntil A B → ∃ t, t ∈ timeTrace A) ∧
    -- ¬before is compatible with main-clause non-actualization
    (∃ (A B : SentDenotation ℤ), Karttunen.notUntil A B ∧ ¬ ∃ t, t ∈ timeTrace A) :=
  ⟨eventiveUntil_entails_actualization, negBefore_lacks_actualization⟩

end Phenomena.TemporalConnectives.Studies.Giannakidou2002
