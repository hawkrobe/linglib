import Linglib.Studies.Karttunen1974
import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Tense.TemporalConnectives.Projection
import Linglib.Data.Examples.Giannakidou2002
import Linglib.Fragments.Greek.StandardModern.TemporalConnectives
import Linglib.Fragments.Icelandic.TemporalConnectives
import Linglib.Fragments.Dutch.TemporalConnectives
import Linglib.Fragments.Finnish.TemporalConnectives

/-!
# Giannakidou (2002): UNTIL, Aspect, and Negation
[giannakidou-2002] [karttunen-1974] [klein-1994]
[de-swart-1996] [de-swart-molendijk-1999]

A Novel Argument for Two *Until*s. Semantics and Linguistic Theory 12, 84–103.

## Central Argument

Viewpoint aspect determines negation scope with *until*:

- **Imperfective main clause**: homogeneous (subinterval property), satisfying
  durative *until*'s selectional restriction. Both wide-scope and narrow-scope
  negation are available.

- **Perfective main clause**: not homogeneous. Only narrow-scope negation
  (= Karttunen's ¬*before*) is available.

This provides a novel argument for [karttunen-1974]'s two-*until*
hypothesis: the scope readings are logically independent, so the restriction
to narrow scope under PRFV is a genuine empirical constraint, not a logical
consequence.

A secondary contribution (§6) refines [karttunen-1974]'s identity
NPI-*until* = ¬*before*: while truth-conditionally valid, *para monon*
(NPI-*until*) and *prin* (*before*) differ on **actualization** — NPI-*until*
entails the main-clause event occurred, *before* does not — and on scope
interaction with imperfective aspect.

## Architecture

Uses `Aspect.Core.UNBOUNDED` (= non-strict IMPF, [pancheva-2003]) projected
to `SentDenotation` for the imperfective denotation:

```
Unit → Event Time → Prop ──[UNBOUNDED]──▷ IntervalPred ──[fix w=()]──▷ SentDenotation
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
9. `stativizer_all_wrong`: all five diagnostics refute [de-swart-1996] (§5)

-/

namespace Giannakidou2002

open Core.Order
open NonemptyInterval
open Semantics.Aspect
open Tense.TemporalConnectives

variable {Time : Type*} [LinearOrder Time]

-- ============================================================================
-- § 1: Aspect.Core → SentDenotation Projection
-- ============================================================================

/-- IMPF denotation: project `Aspect.Core.UNBOUNDED` to `SentDenotation`.
    Each interval in the denotation is a subinterval of some event runtime
    ([klein-1994]: TT ⊆ TSit). Uses `UNBOUNDED` ([pancheva-2003])
    rather than `IMPF` (which requires strict ⊂) because the homogeneity
    argument is identical and the non-strict version connects cleanly to
    `stativeDenotation`. -/
abbrev impfDen (P : Unit → Event Time → Prop) : SentDenotation Time :=
  { i | UNBOUNDED P () i }

/-- PRFV denotation: the set of exact event runtimes — the `eventDenotation`
    τ-image (`Projection.lean`) of `P ()`. Unlike the `Aspect.Core.PRFV` operator
    (whose intervals CONTAIN the runtime: TSit ⊆ TT), this gives the runtime itself,
    directly characterizing the event's temporal extent. -/
def prfvDen (P : Unit → Event Time → Prop) : SentDenotation Time :=
  eventDenotation (P ())

-- ============================================================================
-- § 2: Homogeneity
-- ============================================================================

/-! A sentence denotation is *homogeneous* (subinterval-closed) when membership is
    preserved under subintervals — Karttunen's selectional restriction for durative
    *until*. This is exactly mathlib's `IsLowerSet` over the interval `≤` (subinterval
    containment), so we state homogeneity directly as `IsLowerSet` below. -/

/-- IMPF denotation satisfies the subinterval property.

    This is exactly the homogeneity property that [karttunen-1974] requires
    of the main clause of durative *until*. The imperfective viewpoint
    provides this automatically: since the event extends beyond any reference
    interval, every sub-window into the event is equally valid. -/
theorem impfDen_subinterval_closed (P : Unit → Event Time → Prop)
    (t : NonemptyInterval Time) (ht : t ∈ impfDen P)
    (t' : NonemptyInterval Time) (ht' : t' ≤ t) :
    t' ∈ impfDen P := by
  obtain ⟨e, hSub, hP⟩ := ht
  exact ⟨e, ⟨le_trans hSub.1 ht'.1, le_trans ht'.2 hSub.2⟩, hP⟩

/-- IMPF denotation contains the event runtime itself (the maximal interval). -/
theorem impfDen_contains_runtime (P : Unit → Event Time → Prop)
    (e : Event Time) (hP : P () e) :
    e.τ ∈ impfDen P :=
  ⟨e, le_refl _, hP⟩

/-- PRFV denotation does NOT have the subinterval property.

    Counterexample: An event with runtime [0, 5]. The interval [0, 5] is
    in the denotation, but [1, 3] (a strict subinterval) is not — PRFV
    only includes the exact runtime.

    This is why perfective clauses cannot be main clauses of durative
    *until*: they lack the homogeneity that *until* requires. -/
theorem prfvDen_not_subinterval_closed :
    ¬ ∀ (P : Unit → Event ℤ → Prop) (t : NonemptyInterval ℤ),
      t ∈ prfvDen P → ∀ t', t' ≤ t → t' ∈ prfvDen P := by
  intro h
  -- sort defaults to .action; the proof doesn't reference .sort
  let e₀ : Event ℤ := ⟨⟨⟨0, 5⟩, by omega⟩, .dynamic⟩
  let P : Unit → Event ℤ → Prop := fun _ e => e = e₀
  let sub : NonemptyInterval ℤ := ⟨⟨1, 3⟩, by omega⟩
  have hrt : e₀.τ ∈ prfvDen P := ⟨e₀, rfl, rfl⟩
  have hsub : sub ≤ e₀.τ := by
    dsimp only [sub, e₀]
    simp only [NonemptyInterval.le_def, Event.τ]; omega
  have hmem := h P e₀.τ hrt sub hsub
  obtain ⟨e', he', hτ⟩ := hmem
  dsimp only [P] at he'
  subst he'
  simp only [Event.τ] at hτ
  have : (0 : ℤ) = 1 := congrArg (fun i => i.fst) hτ
  omega

-- ============================================================================
-- § 3: Scope Pattern (Derived from Homogeneity)
-- ============================================================================

/-- IMPF denotation is homogeneous (a lower set / subinterval-closed) — wide scope
    is available. -/
theorem impfDen_homogeneous (P : Unit → Event Time → Prop) :
    IsLowerSet (impfDen P) := by
  intro a b hba ha
  exact impfDen_subinterval_closed P a ha b hba

/-- PRFV denotation is not always homogeneous — wide scope is not always
    available. This is derived from the subinterval-closure failure, not
    stipulated as a Bool field. -/
theorem prfvDen_not_always_homogeneous :
    ¬ ∀ (P : Unit → Event ℤ → Prop), IsLowerSet (prfvDen P) := by
  intro h
  exact prfvDen_not_subinterval_closed fun P t ht t' ht' => h P ht' ht

/-- [giannakidou-2002]'s scope generalization, derived from homogeneity:
    wide-scope negation requires a homogeneous main clause, which IMPF provides
    and PRFV does not. The restriction to narrow scope under PRFV follows from
    PRFV's failure of subinterval-closure, not from a stipulated constraint. -/
theorem scope_pattern_derived :
    -- IMPF always permits wide scope (homogeneous)
    (∀ (P : Unit → Event Time → Prop), IsLowerSet (impfDen P)) ∧
    -- PRFV does not always permit wide scope (not always homogeneous)
    ¬ (∀ (P : Unit → Event ℤ → Prop), IsLowerSet (prfvDen P)) :=
  ⟨impfDen_homogeneous, prfvDen_not_always_homogeneous⟩

-- ============================================================================
-- § 4: Connection to stativeDenotation
-- ============================================================================

/-- For a single event with runtime `i`, the IMPF denotation is exactly
    the stative denotation of `i` (all subintervals). This connects the
    aspect bridge to the existing temporal connective infrastructure
    in `Basic.lean`. -/
theorem impfDen_singleton_eq_stativeDenotation
    (i : NonemptyInterval Time) :
    impfDen (fun () (e : Event Time) => e.τ = i) =
    stativeDenotation i := by
  ext j
  simp only [UNBOUNDED, stativeDenotation, Set.mem_Iic, Set.mem_setOf_eq, Event.τ]
  constructor
  · rintro ⟨e, hSub, rfl⟩; exact hSub
    -- sort defaults to .action; the proof doesn't reference .sort
  · intro h; exact ⟨⟨i, .dynamic⟩, h, rfl⟩

/-- For a single event, the PRFV denotation is exactly the accomplishment
    denotation (singleton containing just the runtime). -/
theorem prfvDen_singleton_eq_accomplishmentDenotation
    (i : NonemptyInterval Time) :
    prfvDen (fun () (e : Event Time) => e.τ = i) =
    accomplishmentDenotation i := by
  ext j
  simp only [prfvDen, mem_eventDenotation, accomplishmentDenotation, Event.τ]
  constructor
  · rintro ⟨e, rfl, rfl⟩; rfl
    -- sort is irrelevant here (defaults to .dynamic); the proof never reads .sort
  · intro h; exact ⟨⟨i, .dynamic⟩, rfl, h.symm⟩

-- ============================================================================
-- § 5: Time Traces Coincide
-- ============================================================================

/-- The time traces of IMPF and PRFV denotations are identical: both equal
    the set of times contained in some event runtime.

    This is why Karttunen's Level 1 (point-set) definitions cannot distinguish
    imperfective from perfective clauses — the difference is only visible
    at Level 2 (interval sets). -/
theorem timeTrace_impf_eq_prfv (P : Unit → Event Time → Prop) :
    timeTrace (impfDen P) = timeTrace (prfvDen P) := by
  ext t
  simp only [timeTrace, prfvDen, UNBOUNDED, Set.mem_setOf_eq, Event.τ]
  constructor
  · rintro ⟨i, ⟨e, hSub, hP⟩, ht⟩
    exact ⟨e.τ, ⟨e, hP, rfl⟩,
      ⟨le_trans hSub.1 ht.1, le_trans ht.2 hSub.2⟩⟩
  · rintro ⟨i, ⟨e, hP, rfl⟩, ht⟩
    exact ⟨NonemptyInterval.pure t,
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
def wideScopeNotUntil (A : Unit → Event Time → Prop) (B : SentDenotation Time) : Prop :=
  ¬ Karttunen.when_ (impfDen A) B

/-- **Narrow-scope negation** under *until* (= Karttunen's ¬*before*):

    ¬(A BEFORE B)

    "A didn't happen before B" — the event occurred, but not prior to B.

    This is the only reading available with perfective main clauses:
    since PRFV gives a bounded event, *until* reduces to temporal ordering
    and negation gives Karttunen's notUntil = ¬before. -/
def narrowScopeNotUntil (A : Unit → Event Time → Prop) (B : SentDenotation Time) : Prop :=
  Karttunen.notUntil (prfvDen A) B

/-- Narrow-scope ¬*until* is exactly ¬*before* (by definition).
    This is [karttunen-1974]'s identity, now made explicit in the
    aspectual decomposition. -/
theorem narrowScope_eq_not_before (A : Unit → Event Time → Prop) (B : SentDenotation Time) :
    narrowScopeNotUntil A B ↔ ¬ Anscombe.before (prfvDen A) B :=
  Iff.rfl

/-- The two scope readings are **semantically distinct**: there exist A, B
    where wide-scope holds but narrow-scope fails.

    Counterexample: event A with runtime [0, 5], B at time 7.
    - Wide scope: ¬(any A-time overlaps with time 7). TRUE — 7 ∉ [0, 5].
    - Narrow scope: ¬(A happened before B). FALSE — time 0 < 7, so A
      precedes B and `Anscombe.before` holds. -/
theorem scope_readings_distinct :
    ∃ (A : Unit → Event ℤ → Prop) (B : SentDenotation ℤ),
      wideScopeNotUntil A B ∧ ¬ narrowScopeNotUntil A B := by
  -- sort defaults to .action; the proof doesn't reference .sort
  let e₀ : Event ℤ := ⟨⟨⟨0, 5⟩, by omega⟩, .dynamic⟩
  let A : Unit → Event ℤ → Prop := fun _ e => e = e₀
  let iB : NonemptyInterval ℤ := ⟨⟨7, 7⟩, by omega⟩
  let B : SentDenotation ℤ := {iB}
  refine ⟨A, B, ?_, ?_⟩
  · intro ⟨t, ht_A, ht_B⟩
    obtain ⟨i, ⟨e, hSub, he⟩, hi⟩ := ht_A
    dsimp only [A] at he; subst he
    obtain ⟨j, (hj : j = iB), hjt⟩ := ht_B
    subst hj
    simp only [NonemptyInterval.le_def, NonemptyInterval.mem_def, Event.τ, e₀, iB] at hSub hi hjt
    omega
  · intro hNot
    apply hNot
    refine ⟨0, ⟨e₀.τ, ⟨e₀, rfl, rfl⟩, ?_⟩, ?_⟩
    · simp only [NonemptyInterval.mem_def, Event.τ, e₀]; omega
    · intro t' ⟨j, (hj : j = iB), hjt⟩
      subst hj
      simp only [NonemptyInterval.mem_def, iB] at hjt; omega

/-- The reverse also holds: there exist A, B where narrow-scope holds
    but wide-scope fails. This confirms the two readings are genuinely
    independent. -/
theorem scope_readings_independent :
    ∃ (A : Unit → Event ℤ → Prop) (B : SentDenotation ℤ),
      ¬ wideScopeNotUntil A B ∧ narrowScopeNotUntil A B := by
  -- sort defaults to .action; the proof doesn't reference .sort
  let e₀ : Event ℤ := ⟨⟨⟨5, 10⟩, by omega⟩, .dynamic⟩
  let A : Unit → Event ℤ → Prop := fun _ e => e = e₀
  let iB : NonemptyInterval ℤ := ⟨⟨3, 7⟩, by omega⟩
  let B : SentDenotation ℤ := {iB}
  refine ⟨A, B, ?_, ?_⟩
  · intro hWide
    apply hWide
    refine ⟨5,
      ⟨NonemptyInterval.pure 5, ⟨e₀, by
        simp only [NonemptyInterval.le_def, NonemptyInterval.pure, Event.τ, e₀]; omega,
        rfl⟩,
        by simp only [NonemptyInterval.mem_def, NonemptyInterval.pure]; omega⟩,
      ⟨iB, rfl, by simp only [NonemptyInterval.mem_def, iB]; omega⟩⟩
  · intro ⟨t, ht_A, hall⟩
    obtain ⟨i, ⟨e, he, hτ⟩, hi⟩ := ht_A
    dsimp only [A] at he; subst he
    rw [← hτ] at hi
    simp only [NonemptyInterval.mem_def, Event.τ, e₀] at hi
    have h3 : (3 : ℤ) ∈ timeTrace B :=
      ⟨iB, rfl, by simp only [NonemptyInterval.mem_def, iB]; omega⟩
    have := hall 3 h3
    omega

-- ============================================================================
-- § 7: Eventive UNTIL (para monon) Semantics ([giannakidou-2002], §3.2)
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
    This is the **actualization entailment** that [giannakidou-2002]
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
  refine ⟨∅, { NonemptyInterval.pure 0 }, ?_, ?_⟩
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

    This formalizes the contrast between [giannakidou-2002]'s ex. (51)
    (imperfective *mexri* + continuation asserting no event) and ex. (57)
    (perfective *para monon* + contradictory continuation). -/
theorem wideScopeNotUntil_compatible_with_empty_main :
    ∃ (A : Unit → Event ℤ → Prop) (B : SentDenotation ℤ),
      wideScopeNotUntil A B ∧ ¬ ∃ t, t ∈ timeTrace (impfDen A) := by
  let A : Unit → Event ℤ → Prop := fun _ _ => False
  let B : SentDenotation ℤ := { NonemptyInterval.pure 0 }
  refine ⟨A, B, ?_, ?_⟩
  · intro ⟨t, ⟨i, ⟨e, _, habs⟩, _⟩, _⟩; exact habs
  · intro ⟨t, i, ⟨e, _, habs⟩, _⟩; exact habs

/-- Durative *until* is compatible with A preceding B:
    the main clause state can extend well before the complement time.

    This is the formal correlate of [giannakidou-2002]'s ex. (7):
    "Sure, the princess slept until midnight. In fact she only woke up
    at 2am." — the state extends past the boundary, and the change-of-state
    is not entailed. -/
theorem durative_compatible_with_before :
    ∃ (A B : SentDenotation ℤ),
      Karttunen.until A B ∧ Anscombe.before A B := by
  let iA : NonemptyInterval ℤ := ⟨⟨0, 10⟩, by omega⟩
  let iB : NonemptyInterval ℤ := ⟨⟨5, 5⟩, by omega⟩
  refine ⟨stativeDenotation iA, {iB}, ?_, ?_⟩
  · exact ⟨5,
      ⟨iA, stativeDenotation_self iA, by simp only [NonemptyInterval.mem_def, iA]; omega⟩,
      ⟨iB, rfl, by simp only [NonemptyInterval.mem_def, iB]; omega⟩⟩
  · refine ⟨0,
      ⟨iA, stativeDenotation_self iA, by simp only [NonemptyInterval.mem_def, iA]; omega⟩, ?_⟩
    intro t' ⟨j, hj, hjt⟩
    simp only [Set.mem_singleton_iff] at hj; subst hj
    simp only [NonemptyInterval.mem_def, iB] at hjt; omega

/-- **Eventive UNTIL is strictly stronger than Karttunen's notUntil.**
    - eventiveUntil → notUntil (actualization + lateness → lateness)
    - notUntil ↛ eventiveUntil (lateness alone lacks actualization)

    This is the formal content of [giannakidou-2002]'s central claim:
    the two readings are not truth-conditionally equivalent under negation. -/
theorem eventiveUntil_strictly_stronger :
    (∀ (A B : SentDenotation ℤ), eventiveUntil A B → Karttunen.notUntil A B) ∧
    (∃ (A B : SentDenotation ℤ), Karttunen.notUntil A B ∧ ¬ eventiveUntil A B) :=
  ⟨fun _ _ h => h.2, notUntil_not_implies_eventiveUntil⟩

-- ============================================================================
-- § 9: Bridge to the Example Rows
-- ============================================================================

open Data.Examples

/-- Giannakidou's three-way semantic typology of *until*-type connectives:
    before-type (*prin*), endpoint-type (durative *until*, *mexri*), and
    eventive-type (NPI-*until*, *para monon*). -/
inductive UntilType where
  | before
  | endpoint
  | eventive
  deriving DecidableEq, Repr

/-- Whether a connective entails that the main-clause event actually
    occurred at the boundary time: an entailment (cancellation yields
    contradiction, ex. 38), a cancellable Q-implicature (ex. 7), or
    absent entirely (exx. 72–73). -/
inductive ActualizationStatus where
  | entailment
  | implicature
  | absent
  deriving DecidableEq, Repr

/-- Value of a `paperFeatures` key, if present. -/
def featureOf (row : LinguisticExample) (key : String) : Option String :=
  (row.paperFeatures.find? (·.1 == key)).map (·.2)

/-- The row's `semantic_type` feature as an `UntilType`. -/
def untilTypeOf (row : LinguisticExample) : Option UntilType :=
  match featureOf row "semantic_type" with
  | some "before"   => some .before
  | some "endpoint" => some .endpoint
  | some "eventive" => some .eventive
  | _ => none

/-- The row's `actualization` feature as an `ActualizationStatus`. -/
def actualizationOf (row : LinguisticExample) : Option ActualizationStatus :=
  match featureOf row "actualization" with
  | some "entailment"  => some .entailment
  | some "implicature" => some .implicature
  | some "none"        => some .absent
  | _ => none

/-- The actualization status each semantic type carries, matching the
    formal operators: eventive = `eventiveUntil` (the overlap conjunct
    entails actualization), endpoint = `Karttunen.until` (boundary
    change-of-state only implicated), before = `Karttunen.notUntil` under
    negation (lateness alone, cf. `negBefore_lacks_actualization`). -/
def UntilType.actualization : UntilType → ActualizationStatus
  | .before   => .absent
  | .endpoint => .implicature
  | .eventive => .entailment

/-- Every row's actualization annotation is determined by its semantic
    type — the three-way split that is the paper's central claim. -/
theorem actualization_determined_by_type :
    ∀ row ∈ Examples.all,
      actualizationOf row = (untilTypeOf row).map UntilType.actualization := by
  decide

/-- Endpoint-type rows are exactly the veridical ones: durative *until*
    presupposes its complement, while before-type and eventive-type
    connectives are nonveridical. -/
theorem veridical_iff_endpoint :
    ∀ row ∈ Examples.all,
      (featureOf row "complement_veridical" = some "true" ↔
        untilTypeOf row = some .endpoint) := by
  decide

/-- Endpoint-type rows are exactly the ones with the durative main-clause
    restriction. The formal correlate: wide scope requires homogeneity
    (`impfDen_homogeneous`), which only durative/imperfective main clauses
    provide; narrow scope (`narrowScopeNotUntil`) does not. -/
theorem durative_main_iff_endpoint :
    ∀ row ∈ Examples.all,
      (featureOf row "requires_durative_main" = some "true" ↔
        untilTypeOf row = some .endpoint) := by
  decide

/-- Eventive-type rows are exactly the ones requiring an anti-veridical
    (DE) trigger — the licensing condition on *para monon* and English
    NPI-*until*. -/
theorem requires_de_iff_eventive :
    ∀ row ∈ Examples.all,
      (featureOf row "requires_de" = some "true" ↔
        untilTypeOf row = some .eventive) := by
  decide

/-- Before-type rows license NPIs; endpoint-type rows do not. (Eventive
    rows split: English NPI-*until* hosts NPIs, *para monon* does not.) -/
theorem npi_licensing_by_type :
    ∀ row ∈ Examples.all,
      (untilTypeOf row = some .before →
        featureOf row "licenses_npis" = some "true") ∧
      (untilTypeOf row = some .endpoint →
        featureOf row "licenses_npis" = some "false") := by
  decide

/-- Greek lexicalizes all three semantic types as distinct connectives:
    *prin* (before), *mexri* (endpoint), *para monon* (eventive). -/
theorem greek_lexicalizes_three_types :
    ∀ ty : UntilType, ∃ row ∈ Examples.all,
      row.language = "mode1248" ∧ untilTypeOf row = some ty := by
  intro ty; cases ty <;> decide

/-- The mood restriction each semantic type imposes in Greek. -/
def UntilType.greekMood : UntilType → Option String
  | .before   => some "subjunctive"
  | .endpoint => some "indicative"
  | .eventive => none

/-- Greek mood tracks the semantic type: subjunctive for before-type,
    indicative for endpoint-type, no mood restriction for eventive-type.
    The mood split is the morphological reflex of (non)veridicality. -/
theorem greek_mood_tracks_type :
    ∀ row ∈ Examples.all, row.language = "mode1248" →
      featureOf row "mood" = (untilTypeOf row).bind UntilType.greekMood := by
  decide

-- ============================================================================
-- § 10: Bridge to Greek Fragment
-- ============================================================================

open Greek.StandardModern.TemporalConnectives

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
-- § 11: Negation is NOT a Stativizer ([giannakidou-2002], §5)
-- ============================================================================

/-! [giannakidou-2002] refutes the analysis of negation as an aspectual
    operator that converts eventive predicates into stative ones
    ([de-swart-1996], [de-swart-molendijk-1999]). On that account,
    negation takes an eventuality description P and yields a maximal state s
    such that no event of type P is contained in s. If this were correct,
    negated perfectives should behave like statives — but they don't:
    Greek negated perfectives still reject durative *until* (*mexri*),
    reject *how long*, reject *while*, and accept imperatives. -/

/-- [de-swart-1996]'s stativizer hypothesis: negation converts events
    into maximal states, so ALL negated predicates (including perfectives)
    should be homogeneous (subinterval-closed), just like true statives.

    The formal refutation: if this were correct, then PRFV denotations
    would always be homogeneous. But we proved in §2 that PRFV is NOT
    always homogeneous (`prfvDen_not_subinterval_closed`). -/
theorem stativizer_false_for_perfective :
    ¬ (∀ (P : Unit → Event ℤ → Prop), IsLowerSet (prfvDen P)) :=
  prfvDen_not_always_homogeneous

/-- The five stativizer diagnostics and their results for negated
    perfective forms ([giannakidou-2002], §5, ex. 67–71):

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
-- § 12: English Simple Past = Covert Perfective ([giannakidou-2002], §4.3)
-- ============================================================================

/-- [giannakidou-2002]'s argument that the English simple past has a
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
    ¬ (∀ (P : Unit → Event ℤ → Prop), IsLowerSet (prfvDen P)) ∧
    -- IMPF has homogeneity → wide scope would be available if past were imperfective
    (∀ (P : Unit → Event ℤ → Prop), IsLowerSet (impfDen P)) :=
  ⟨prfvDen_not_always_homogeneous, impfDen_homogeneous⟩

-- ============================================================================
-- § 13: *Before* ≠ NPI-*Until* on Actualization ([giannakidou-2002], §6)
-- ============================================================================

/-! [giannakidou-2002]'s §6 refines [karttunen-1974]'s identity
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

/-- ¬*before* (= [karttunen-1974]'s notUntil) is compatible with the
    main-clause event never occurring: when A = ∅, `¬(A before B)` holds
    vacuously since `Anscombe.before ∅ B` is always false.

    [giannakidou-2002], §6, ex. (72): "I prigipisa dhen eftase prin apo
    ta mesanixta" — the princess may or may not have arrived. *Prin/before*
    with negation does not entail actualization of the arriving event.

    Contrast with `eventiveUntil`, which requires main-clause actualization
    (the overlap conjunct forces a witness in A). -/
theorem negBefore_lacks_actualization :
    ∃ (A B : SentDenotation ℤ),
      Karttunen.notUntil A B ∧ ¬ ∃ t, t ∈ timeTrace A := by
  refine ⟨∅, { NonemptyInterval.pure 0 }, ?_, ?_⟩
  · intro ⟨t, ⟨i, hi, _⟩, _⟩
    exact absurd hi (Set.mem_empty_iff_false i).mp
  · intro ⟨t, i, hi, _⟩
    exact absurd hi (Set.mem_empty_iff_false i).mp

/-- **NPI-*until* ≠ ¬*before* on actualization** ([giannakidou-2002], §6).

    - `eventiveUntil A B` entails main-clause actualization (∃t ∈ A)
    - `¬(A before B)` is compatible with main-clause non-actualization (A = ∅)

    This is the formal content of [giannakidou-2002]'s central §6 claim:
    [karttunen-1974]'s truth-conditional identity (NPI-*until* = ¬*before*)
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

-- ============================================================================
-- §7: Cross-Linguistic Until-Strategy Typology
-- ============================================================================

/-! Per-language strategy entries for the durative/eventive *until*
distinction. The `UntilStrategy` enum + `UntilTypologyEntry` schema (consolidated from the former
`Typology/TemporalConnectives.lean`) plus the per-language data + Fragment
grounding theorems are all paper-anchored here. -/

/-- How a language handles the durative/eventive *until* distinction
    ([giannakidou-2002]). -/
inductive UntilStrategy where
  /-- Three distinct lexemes: *before*, durative *until*, eventive NPI-*until*.
      Greek: *prin*, *mexri*, *para monon*. -/
  | threeWay
  /-- Two distinct lexemes: durative *until* and eventive NPI-*until*.
      Icelandic: *flanga til*, *fyrr en*. Finnish: *kunnes*, *ennenkuin*. -/
  | twoWay
  /-- Single ambiguous lexeme, disambiguated by negation context.
      English: *until*. -/
  | ambiguous
  /-- Durative *until* blocked under negation; PPI replaces NPI-*until*.
      Dutch: *tot*, *pas*. German: *bis*, *erst*. -/
  | ppiReplacement
  deriving DecidableEq, Repr

/-- A language's strategy for the two-*until* distinction. -/
structure UntilTypologyEntry where
  language : String
  strategy : UntilStrategy
  /-- Surface form for durative *until*. -/
  durativeForm : String
  /-- Surface form for eventive *until* (NPI or PPI). -/
  eventiveForm : String
  /-- Is the eventive form morphologically built on *before*?
      ([karttunen-1974]'s identity NPI-*until* = ¬*before*.) -/
  eventiveMorphBeforeBased : Bool
  /-- Does the language have overt perfective/imperfective marking?
      Orthogonal to the lexicalization choice. -/
  hasOvertAspect : Bool
  deriving Repr


def greek : UntilTypologyEntry where
  language := "Greek"
  strategy := .threeWay
  durativeForm := "mexri (μέχρι)"
  eventiveForm := "para monon (παρά μονον)"
  eventiveMorphBeforeBased := false
  hasOvertAspect := true

def icelandic : UntilTypologyEntry where
  language := "Icelandic"
  strategy := .twoWay
  durativeForm := "flanga til / til"
  eventiveForm := "fyrr en"
  eventiveMorphBeforeBased := true   -- fyrr = 'earlier/before' + en = 'than'
  hasOvertAspect := false

def finnish : UntilTypologyEntry where
  language := "Finnish"
  strategy := .twoWay
  durativeForm := "kunnes / siihen saakka"
  eventiveForm := "ennenkuin"
  eventiveMorphBeforeBased := true   -- ennen = 'before' + kuin = 'than'
  hasOvertAspect := false

def english : UntilTypologyEntry where
  language := "English"
  strategy := .ambiguous
  durativeForm := "until"
  eventiveForm := "until (NPI, with negation)"
  eventiveMorphBeforeBased := false
  hasOvertAspect := false  -- no overt perf/impf; simple past = covert perfective

def dutch : UntilTypologyEntry where
  language := "Dutch"
  strategy := .ppiReplacement
  durativeForm := "tot"
  eventiveForm := "pas"
  eventiveMorphBeforeBased := false
  hasOvertAspect := false

def german : UntilTypologyEntry where
  language := "German"
  strategy := .ppiReplacement
  durativeForm := "bis"
  eventiveForm := "erst"
  eventiveMorphBeforeBased := false
  hasOvertAspect := false

/-- The full typological sample (6 languages, 4 strategies). -/
def typology : List UntilTypologyEntry :=
  [greek, icelandic, finnish, english, dutch, german]

/-- Every language in the sample uses distinct surface forms for durative
    and eventive *until* (even the ambiguous strategy uses the same form
    in different syntactic contexts, disambiguated by negation). -/
theorem all_distinguish_durative_eventive :
    ∀ e ∈ typology, e.durativeForm ≠ e.eventiveForm := by
  intro e he
  simp only [typology, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The two-way and three-way strategies both have morphologically
    *before*-based eventive forms in at least one language, confirming
    [karttunen-1974]'s identity NPI-*until* = ¬*before*. -/
theorem before_morphology_attested :
    icelandic.eventiveMorphBeforeBased = true ∧
    finnish.eventiveMorphBeforeBased = true :=
  ⟨rfl, rfl⟩

/-- Overt aspect marking is NOT required for lexicalization of the
    two-*until* distinction. Icelandic and Finnish lack overt verbal
    aspect but still lexicalize two *until*s. -/
theorem aspect_not_required :
    icelandic.hasOvertAspect = false ∧ icelandic.strategy = .twoWay ∧
    finnish.hasOvertAspect = false ∧ finnish.strategy = .twoWay :=
  ⟨rfl, rfl, rfl, rfl⟩

-- Bridge to Fragment data --

open Greek.StandardModern.TemporalConnectives in
/-- Greek strategy confirmed by fragment: three distinct forms. -/
theorem greek_confirmed :
    mexri.form ≠ paraMonon.form ∧
    mexri.form ≠ prin.form ∧
    paraMonon.form ≠ prin.form := by
  exact ⟨by decide, by decide, by decide⟩

open Icelandic.TemporalConnectives in
/-- Icelandic strategy confirmed by fragment: two distinct forms with
    veridicality split. -/
theorem icelandic_confirmed :
    flangaTil.form ≠ fyrrEn.form ∧
    flangaTil.complementVeridical = true ∧
    fyrrEn.complementVeridical = false :=
  ⟨by decide, rfl, rfl⟩

open Dutch.TemporalConnectives in
/-- Dutch strategy confirmed by fragment: two distinct forms with
    veridicality split. -/
theorem dutch_confirmed :
    tot.form ≠ pas.form ∧
    tot.complementVeridical = true ∧
    pas.complementVeridical = false :=
  ⟨by decide, rfl, rfl⟩

-- Bridge to the example rows --

/-- The eventive type is attested in both English (NPI-*until*) and Greek
    (*para monon*): the lexicalization strategies differ, but the semantic
    type — and with it the actualization entailment
    (`actualization_determined_by_type`) — is preserved. -/
theorem eventive_attested_crosslinguistically :
    (∃ row ∈ Examples.all,
      row.language = "stan1293" ∧ untilTypeOf row = some .eventive) ∧
    (∃ row ∈ Examples.all,
      row.language = "mode1248" ∧ untilTypeOf row = some .eventive) := by
  constructor <;> decide

end Giannakidou2002
