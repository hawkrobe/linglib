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


variable {Time : Type*} [LinearOrder Time]

/-- A sentence denotes a set of temporal intervals — its "run-times". -/
abbrev SentDenotation (Time : Type*) [LinearOrder Time] := Set (NonemptyInterval Time)

/-- The time points contained in some interval of a denotation. -/
def timeTrace (p : SentDenotation Time) : Set Time :=
  { t | ∃ i ∈ p, t ∈ i }

@[simp] theorem mem_timeTrace {p : SentDenotation Time} {t : Time} :
    t ∈ timeTrace p ↔ ∃ i ∈ p, t ∈ i := Iff.rfl

theorem timeTrace_image {α : Type*} (f : α → NonemptyInterval Time) (s : Set α) :
    timeTrace (f '' s) = { t | ∃ a ∈ s, t ∈ f a } := by
  ext t; simp

/-- Stative denotation: the maximal interval `i` with all its subintervals —
    the principal downset `Set.Iic i`, a lower set, which *is* the
    subinterval-closure property. The *activity* case (a minimal-parts floor:
    a single step is not "running") is the stratified reference of
    `Aspect/Stratified` ([champollion-2017]), not this lower set. -/
def stativeDenotation (i : NonemptyInterval Time) : SentDenotation Time :=
  Set.Iic i

/-- Accomplishment denotation: exactly the singleton `{i}` — quantization. -/
def accomplishmentDenotation (i : NonemptyInterval Time) : SentDenotation Time :=
  {i}

theorem stativeDenotation_self (i : NonemptyInterval Time) :
    i ∈ stativeDenotation i :=
  Set.mem_Iic.mpr le_rfl

theorem timeTrace_stativeDenotation (i : NonemptyInterval Time) :
    timeTrace (stativeDenotation i) = { t | t ∈ i } := by
  ext t
  simp only [mem_timeTrace, stativeDenotation, Set.mem_Iic, Set.mem_ofPred_eq,
    NonemptyInterval.mem_def, NonemptyInterval.le_def]
  grind

theorem timeTrace_accomplishmentDenotation (i : NonemptyInterval Time) :
    timeTrace (accomplishmentDenotation i) = { t | t ∈ i } := by
  ext t; simp [timeTrace, accomplishmentDenotation]


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
