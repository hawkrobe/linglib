import Linglib.Theories.Semantics.Tense.TemporalConnectives.Karttunen
import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect

/-!
# Viewpoint Aspect × Temporal Connective Interaction
@cite{giannakidou-2002} @cite{karttunen-1974} @cite{klein-1994} @cite{mittwoch-1977}@cite{giannakidou-2002} shows that viewpoint aspect determines negation scope
with *until*:

- **Imperfective main clause** (states/progressives): the main clause is
  homogeneous (subinterval property), satisfying durative *until*'s
  selectional restriction. Negation can scope wide or
  narrow.

- **Perfective main clause** (achievements/accomplishments): the event is
  bounded (no subinterval property). Only narrow-scope negation is available:
  ¬(*before*) (= Karttunen's `notUntil`).

## Architecture

This file bridges `ViewpointAspect` operators (IMPF, PRFV) into the temporal
connective layer by projecting `EventPred` through viewpoint aspect to
`SentDenotation`:

```
EventPred Unit Time ──[impfDenotation]──▷ SentDenotation Time (homogeneous)
EventPred Unit Time ──[prfvDenotation]──▷ SentDenotation Time (quantized)
```

The world parameter is fixed to `Unit`: temporal connectives are
world-independent (purely temporal structure).

## Key Results

1. `impfDenotation_subinterval_closed`: IMPF gives homogeneity
2. `prfvDenotation_not_subinterval_closed`: PRFV does not
3. `scope_readings_distinct`: wide-scope and narrow-scope ¬*until* differ

-/

namespace Semantics.Tense.TemporalConnectives

open Core.Time
open Core.Time.Interval
open Semantics.Lexical.Verb.ViewpointAspect

variable {Time : Type*} [LinearOrder Time]

-- ============================================================================
-- § 1: EventPred → SentDenotation via Viewpoint Aspect
-- ============================================================================

/-- Project an event predicate to a sentence denotation via **imperfective**
    aspect. The result is homogeneous: for each event satisfying P, the
    denotation includes all subintervals of the event runtime.

    This captures @cite{klein-1994}'s IMPF: the reference time (TT) is properly
    inside the situation time (TSit), so the event extends beyond any
    particular reference point. Every subinterval of the event runtime is
    a valid reference window into the ongoing event.

    World parameter fixed to `Unit`: temporal connectives are
    world-independent. -/
def impfDenotation (P : EventPred Unit Time) : SentDenotation Time :=
  { i | ∃ e : Eventuality Time, P () e ∧ i.subinterval e.τ }

/-- Project an event predicate to a sentence denotation via **perfective**
    aspect. The result is quantized: only the exact event runtime is included.

    This captures @cite{klein-1994}'s PRFV: the situation time (TSit) is contained
    in the reference time (TT), so the event is viewed as complete. The
    denotation contains only the event's actual runtime — the bounded interval
    during which the event occurred. -/
def prfvDenotation (P : EventPred Unit Time) : SentDenotation Time :=
  { i | ∃ e : Eventuality Time, P () e ∧ e.τ = i }

-- ============================================================================
-- § 2: Homogeneity of IMPF Denotations
-- ============================================================================

/-- IMPF denotation satisfies the subinterval property: if interval `t` is in
    the denotation (i.e., `t ⊆ τ(e)` for some event `e`), then every
    subinterval of `t` is also in the denotation.

    This is exactly the homogeneity property that @cite{karttunen-1974} requires
    of the main clause of durative *until*. The imperfective viewpoint
    provides this automatically: since the event extends beyond any reference
    interval, every sub-window into the event is equally valid. -/
theorem impfDenotation_subinterval_closed (P : EventPred Unit Time)
    (t : Interval Time) (ht : t ∈ impfDenotation P)
    (t' : Interval Time) (ht' : t'.subinterval t) :
    t' ∈ impfDenotation P := by
  obtain ⟨e, hP, hSub⟩ := ht
  exact ⟨e, hP, ⟨le_trans hSub.1 ht'.1, le_trans ht'.2 hSub.2⟩⟩

/-- IMPF denotation contains the event runtime itself (the maximal interval).
    Every event satisfying P contributes its runtime to the denotation. -/
theorem impfDenotation_contains_runtime (P : EventPred Unit Time)
    (e : Eventuality Time) (hP : P () e) :
    e.τ ∈ impfDenotation P :=
  ⟨e, hP, subinterval_refl _⟩

/-- PRFV denotation does NOT have the subinterval property.

    Counterexample: An event with runtime [0, 5]. The interval [0, 5] is
    in the denotation, but [1, 3] (a strict subinterval) is not — PRFV
    only includes the exact runtime.

    This is why perfective clauses cannot be main clauses of durative
    *until*: they lack the homogeneity that *until* requires. -/
theorem prfvDenotation_not_subinterval_closed :
    ¬ ∀ (P : EventPred Unit ℤ) (t : Interval ℤ),
      t ∈ prfvDenotation P → ∀ t', t'.subinterval t → t' ∈ prfvDenotation P := by
  intro h
  let e₀ : Eventuality ℤ := ⟨⟨0, 5, by omega⟩⟩
  let P : EventPred Unit ℤ := fun _ e => e = e₀
  let sub : Interval ℤ := ⟨1, 3, by omega⟩
  have hrt : e₀.τ ∈ prfvDenotation P := ⟨e₀, rfl, rfl⟩
  have hsub : sub.subinterval e₀.τ := by
    dsimp only [sub, e₀]
    simp only [subinterval, Eventuality.τ]; omega
  have hmem := h P e₀.τ hrt sub hsub
  obtain ⟨e', he', hτ⟩ := hmem
  -- e' = e₀ (by P), so e'.τ = [0,5]. But hτ says e'.τ = [1,3]. Contradiction.
  dsimp only [P] at he'
  subst he'
  simp only [Eventuality.τ] at hτ
  have : (0 : ℤ) = 1 := congrArg Interval.start hτ
  omega

-- ============================================================================
-- § 3: Connection to stativeDenotation
-- ============================================================================

/-- For a single event with runtime `i`, the IMPF denotation is exactly
    the stative denotation of `i` (all subintervals). This connects the
    ViewpointAspect bridge to the existing temporal connective infrastructure
    in `Basic.lean`. -/
theorem impfDenotation_singleton_eq_stativeDenotation
    (i : Interval Time) :
    impfDenotation (fun () (e : Eventuality Time) => e.τ = i) =
    stativeDenotation i := by
  ext j
  simp only [impfDenotation, stativeDenotation,
    Set.mem_setOf_eq, Eventuality.τ]
  constructor
  · rintro ⟨e, rfl, h⟩; exact h
  · intro h; exact ⟨⟨i⟩, rfl, h⟩

/-- For a single event, the PRFV denotation is exactly the accomplishment
    denotation (singleton containing just the runtime). -/
theorem prfvDenotation_singleton_eq_accomplishmentDenotation
    (i : Interval Time) :
    prfvDenotation (fun () (e : Eventuality Time) => e.τ = i) =
    accomplishmentDenotation i := by
  ext j
  simp only [prfvDenotation, accomplishmentDenotation,
    Set.mem_setOf_eq, Eventuality.τ]
  constructor
  · rintro ⟨e, rfl, rfl⟩; rfl
  · intro h; exact ⟨⟨i⟩, rfl, h.symm⟩

-- ============================================================================
-- § 4: Time Traces Coincide
-- ============================================================================

/-- The time traces of IMPF and PRFV denotations are identical: both equal
    the set of times contained in some event runtime.

    This is why Karttunen's Level 1 (point-set) definitions cannot distinguish
    imperfective from perfective clauses — the difference is only visible
    at Level 2 (interval sets). Giannakidou's scope analysis requires
    the Level 2 distinction. -/
theorem timeTrace_impf_eq_prfv (P : EventPred Unit Time) :
    timeTrace (impfDenotation P) = timeTrace (prfvDenotation P) := by
  ext t
  simp only [timeTrace, impfDenotation, prfvDenotation,
    Set.mem_setOf_eq, Eventuality.τ]
  constructor
  · rintro ⟨i, ⟨e, hP, hSub⟩, ht⟩
    exact ⟨e.τ, ⟨e, hP, rfl⟩,
      ⟨le_trans hSub.1 ht.1, le_trans ht.2 hSub.2⟩⟩
  · rintro ⟨i, ⟨e, hP, rfl⟩, ht⟩
    exact ⟨Interval.point t,
      ⟨e, hP, ⟨ht.1, ht.2⟩⟩, ⟨le_refl _, le_refl _⟩⟩

-- ============================================================================
-- § 5: Giannakidou's Scope Readings
-- ============================================================================

/-- **Wide-scope negation** over imperfective *until*:

    ¬∃t [t ∈ timeTrace(IMPF(A)) ∧ t ∈ timeTrace(B)]

    "It's not the case that A was ongoing up to the time of B."

    Available when A is imperfective: the main clause denotes a homogeneous
    interval set via IMPF, so *until* can take it as an argument.
    Negation scopes over the entire *until*-clause. -/
def wideScopeNotUntil (A : EventPred Unit Time) (B : SentDenotation Time) : Prop :=
  ¬ Karttunen.when_ (impfDenotation A) B

/-- **Narrow-scope negation** under *until* (= Karttunen's ¬*before*):

    ¬(A BEFORE B)

    "A didn't happen before B" — the event occurred, but not prior to B.

    This is the only reading available with perfective main clauses:
    since PRFV gives a bounded event, *until* reduces to temporal ordering
    and negation gives Karttunen's notUntil = ¬before. -/
def narrowScopeNotUntil (A : EventPred Unit Time) (B : SentDenotation Time) : Prop :=
  Karttunen.notUntil (prfvDenotation A) B

-- ============================================================================
-- § 6: Scope Properties
-- ============================================================================

/-- Narrow-scope ¬*until* is exactly ¬*before* (by definition).
    This is @cite{karttunen-1974}'s identity, now made explicit in the
    aspectual decomposition. -/
theorem narrowScope_eq_not_before (A : EventPred Unit Time) (B : SentDenotation Time) :
    narrowScopeNotUntil A B ↔ ¬ Anscombe.before (prfvDenotation A) B :=
  Iff.rfl

/-- The two scope readings are **semantically distinct**: there exist A, B
    where wide-scope holds but narrow-scope fails.

    Counterexample: event A with runtime [0, 5], B at time 7.
    - Wide scope: ¬(any A-time overlaps with time 7). TRUE — 7 ∉ [0, 5].
    - Narrow scope: ¬(A happened before B). FALSE — time 0 < 7, so A
      precedes B and `Anscombe.before` holds.

    Intuitively: the sleeping event [0, 5] ended before time 7. The wide-scope
    reading says "sleeping didn't extend to 7" (true). The narrow-scope reading
    says "sleeping didn't happen before 7" (false — it did). -/
theorem scope_readings_distinct :
    ∃ (A : EventPred Unit ℤ) (B : SentDenotation ℤ),
      wideScopeNotUntil A B ∧ ¬ narrowScopeNotUntil A B := by
  let e₀ : Eventuality ℤ := ⟨⟨0, 5, by omega⟩⟩
  let A : EventPred Unit ℤ := fun _ e => e = e₀
  let iB : Interval ℤ := ⟨7, 7, by omega⟩
  let B : SentDenotation ℤ := {iB}
  refine ⟨A, B, ?_, ?_⟩
  · -- Wide scope: ¬(∃ t, t ∈ timeTrace(impfDenotation A) ∧ t ∈ timeTrace B)
    intro ⟨t, ht_A, ht_B⟩
    -- t ∈ timeTrace(impfDenotation A): t is in some subinterval of [0, 5]
    obtain ⟨i, ⟨e, he, hSub⟩, hi⟩ := ht_A
    dsimp only [A] at he; subst he
    -- t ∈ timeTrace B: t is in iB = [7, 7]
    obtain ⟨j, (hj : j = iB), hjt⟩ := ht_B
    subst hj
    -- t ≤ 5 (from subinterval of [0,5]) and t ≥ 7 (from containment in [7,7])
    simp only [subinterval, contains, Eventuality.τ, e₀, iB] at hSub hi hjt
    omega
  · -- Narrow scope: show Anscombe.before (prfvDenotation A) B holds
    intro hNot
    apply hNot
    -- Construct: time 0 ∈ timeTrace(prfvDenotation A), and 0 < all B-times
    refine ⟨0, ⟨e₀.τ, ⟨e₀, rfl, rfl⟩, ?_⟩, ?_⟩
    · simp only [contains, Eventuality.τ, e₀]; omega
    · intro t' ⟨j, (hj : j = iB), hjt⟩
      subst hj
      simp only [contains, iB] at hjt; omega

/-- The reverse also holds: there exist A, B where narrow-scope holds
    but wide-scope fails. This confirms the two readings are genuinely
    independent.

    Counterexample: event A with runtime [5, 10], B over [3, 7].
    - Wide scope: ¬(any A-time overlaps with B). FALSE — time 5 is in both.
    - Narrow scope: ¬(A before B). TRUE — no A-time (≥ 5) precedes ALL
      B-times (which include 3). -/
theorem scope_readings_independent :
    ∃ (A : EventPred Unit ℤ) (B : SentDenotation ℤ),
      ¬ wideScopeNotUntil A B ∧ narrowScopeNotUntil A B := by
  let e₀ : Eventuality ℤ := ⟨⟨5, 10, by omega⟩⟩
  let A : EventPred Unit ℤ := fun _ e => e = e₀
  let iB : Interval ℤ := ⟨3, 7, by omega⟩
  let B : SentDenotation ℤ := {iB}
  refine ⟨A, B, ?_, ?_⟩
  · -- Wide scope fails: there IS overlap at time 5
    intro hWide
    apply hWide
    refine ⟨5,
      ⟨Interval.point 5, ⟨e₀, rfl, by
        simp only [subinterval, Interval.point, Eventuality.τ, e₀]; omega⟩,
        by simp only [contains, Interval.point]; omega⟩,
      ⟨iB, rfl, by simp only [contains, iB]; omega⟩⟩
  · -- Narrow scope holds: ¬(Anscombe.before (prfvDenotation A) B)
    intro ⟨t, ht_A, hall⟩
    obtain ⟨i, ⟨e, he, hτ⟩, hi⟩ := ht_A
    dsimp only [A] at he; subst he
    -- hτ : e₀.τ = i, so rewrite hi to use e₀'s concrete interval
    rw [← hτ] at hi
    simp only [contains, Eventuality.τ, e₀] at hi
    -- t ≥ 5. But hall says t < all B-times. B contains 3, so t < 3.
    have h3 : (3 : ℤ) ∈ timeTrace B :=
      ⟨iB, rfl, by simp only [contains, iB]; omega⟩
    have := hall 3 h3
    omega

-- ============================================================================
-- § 7: Giannakidou's Generalization (Data)
-- ============================================================================

/-- @cite{giannakidou-2002}'s generalization about viewpoint aspect and scope.
    This is an empirical generalization, not a logical entailment — it
    describes which readings are *available* in natural language, not which
    are logically possible.

    The formalization above proves that the two scope readings are logically
    independent (§6), confirming that the restriction to narrow scope under
    PRFV is a genuine constraint, not a logical consequence. -/
structure ScopeGeneralization where
  /-- Viewpoint aspect of the main clause -/
  viewpoint : ViewpointType
  /-- Is wide-scope negation available? -/
  wideScopeAvailable : Bool
  /-- Is narrow-scope negation available? -/
  narrowScopeAvailable : Bool
  deriving Repr

/-- Imperfective main clause: both scope readings available. -/
def impfScope : ScopeGeneralization where
  viewpoint := .imperfective
  wideScopeAvailable := true
  narrowScopeAvailable := true

/-- Perfective main clause: only narrow scope available. -/
def prfvScope : ScopeGeneralization where
  viewpoint := .perfective
  wideScopeAvailable := false
  narrowScopeAvailable := true

/-- Giannakidou's generalization: perfective blocks wide-scope negation;
    narrow-scope is always available. -/
theorem giannakidou_scope_pattern :
    impfScope.wideScopeAvailable = true ∧
    impfScope.narrowScopeAvailable = true ∧
    prfvScope.wideScopeAvailable = false ∧
    prfvScope.narrowScopeAvailable = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The availability of wide scope correlates with homogeneity:
    imperfective → homogeneous → wide scope available;
    perfective → not homogeneous → wide scope blocked.

    This is the bridge between the data (§7) and the theory (§§1-2):
    IMPF gives homogeneity (§2), homogeneity enables durative *until*,
    and durative *until* enables wide-scope negation. -/
theorem wideScopeAvailable_iff_imperfective (sg : ScopeGeneralization)
    (h : sg = impfScope ∨ sg = prfvScope) :
    sg.wideScopeAvailable = true ↔ sg.viewpoint = .imperfective := by
  cases h with
  | inl h => subst h; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | inr h => subst h; simp [prfvScope]

end Semantics.Tense.TemporalConnectives
