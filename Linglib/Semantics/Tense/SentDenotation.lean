/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.Interval
import Linglib.Semantics.Events.Basic

/-!
# Sentence denotations as run-time interval sets
[krifka-1989]

A sentence denotes the set of its run-time intervals (`SentDenotation`).
Statives denote a maximal interval with all its subintervals
(`stativeDenotation`, a principal downset); accomplishments denote a
singleton (`accomplishmentDenotation`); `timeTrace` projects an interval
set to the time points it covers, and `eventDenotation`
(`Semantics/Events/Basic.lean`) realises the patterns from
neo-Davidsonian event predicates. The temporal-connective analyses that
consume this carrier live in their studies (Anscombe1964, Karttunen1974,
BeaverCondoravdi2003, Rett2020, …).
-/

namespace Tense

open NonemptyInterval

variable {Time : Type*} [LinearOrder Time]

/-! ### Sentence Denotations as NonemptyInterval Sets -/

/-- A sentence denotes a set of temporal intervals (its "run-times").
    Statives denote homogeneous interval sets; accomplishments denote singletons. -/
abbrev SentDenotation (Time : Type*) [LinearOrder Time] := Set (NonemptyInterval Time)

/-- The set of all time points contained in some interval of a denotation.
    This projects from interval-set representation to time-set representation,
    which is what [rett-2020]'s formalization quantifies over. -/
def timeTrace (p : SentDenotation Time) : Set Time :=
  { t | ∃ i ∈ p, t ∈ i }

theorem timeTrace_image {α : Type*} (f : α → NonemptyInterval Time) (s : Set α) :
    timeTrace (f '' s) = { t | ∃ a ∈ s, t ∈ f a } := by
  ext t; simp [timeTrace]

/-- Stative denotation: the maximal interval `i` plus all its subintervals — the
    principal downset `Set.Iic i`. It is therefore an `IsLowerSet` (`isLowerSet_Iic`),
    which *is* the subinterval-closure property.

    This models the idealized *stative* subinterval property (homogeneous down to
    instants). The *activity* case has a minimal-parts floor — a single step is not
    "running" — which is the proper-subinterval *stratified reference* of
    `Aspect/Stratified` / [champollion-2017], not this lower set. -/
def stativeDenotation (i : NonemptyInterval Time) : SentDenotation Time :=
  Set.Iic i

/-- Accomplishment denotation: exactly the singleton interval `i` (`{i}`).
    Captures the quantized property of telic events. -/
def accomplishmentDenotation (i : NonemptyInterval Time) : SentDenotation Time :=
  {i}

/-! ### Basic Properties -/

/-- Every point subinterval of a stative denotation's maximal interval is in the set. -/
theorem stativeDenotation_contains_point (i : NonemptyInterval Time) (t : Time)
    (ht : t ∈ i) : NonemptyInterval.pure t ∈ stativeDenotation i :=
  ⟨ht.1, ht.2⟩

/-- An accomplishment denotation has exactly one member. -/
theorem accomplishmentDenotation_singleton (i : NonemptyInterval Time) :
    ∀ j, j ∈ accomplishmentDenotation i ↔ j = i :=
  λ _ => Iff.rfl

/-- The maximal interval is in its own stative denotation (reflexivity). -/
theorem stativeDenotation_self (i : NonemptyInterval Time) :
    i ∈ stativeDenotation i :=
  ⟨le_refl _, le_refl _⟩

/-- The time trace of a stative denotation is exactly the set of times
    contained in the maximal interval. -/
theorem timeTrace_stativeDenotation (i : NonemptyInterval Time) :
    timeTrace (stativeDenotation i) = { t | t ∈ i } := by
  ext t
  simp only [timeTrace, stativeDenotation, Set.mem_Iic, Set.mem_ofPred_eq, NonemptyInterval.mem_def, NonemptyInterval.le_def]
  constructor
  · rintro ⟨j, ⟨hjs, hjf⟩, hjt_s, hjt_f⟩
    exact ⟨le_trans hjs hjt_s, le_trans hjt_f hjf⟩
  · rintro ⟨hs, hf⟩
    exact ⟨NonemptyInterval.pure t, ⟨hs, hf⟩, le_refl _, le_refl _⟩

/-- The time trace of an accomplishment denotation is exactly the set of times
    contained in the unique interval. -/
theorem timeTrace_accomplishmentDenotation (i : NonemptyInterval Time) :
    timeTrace (accomplishmentDenotation i) = { t | t ∈ i } := by
  ext t
  simp only [timeTrace, accomplishmentDenotation, Set.mem_singleton_iff, Set.mem_ofPred_eq, NonemptyInterval.mem_def]
  constructor
  · rintro ⟨j, rfl, hs, hf⟩
    exact ⟨hs, hf⟩
  · rintro ⟨hs, hf⟩
    exact ⟨i, rfl, hs, hf⟩


theorem timeTrace_eventDenotation (P : Event Time → Prop) :
    timeTrace (eventDenotation P) = { t | ∃ e, P e ∧ t ∈ e.τ } :=
  timeTrace_image Event.τ { e | P e }

theorem eventDenotation_singleton (e₀ : Event Time) :
    eventDenotation (fun e => e = e₀) = accomplishmentDenotation e₀.τ := by
  simp [eventDenotation, accomplishmentDenotation]

theorem eventDenotation_sub_stative (i : NonemptyInterval Time) (P : Event Time → Prop)
    (hP : ∀ e, P e → e.τ ≤ i) :
    eventDenotation P ⊆ stativeDenotation i := by
  rintro j ⟨e, he, rfl⟩; exact hP e he

end Tense
