/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Interval

/-!
# Run times

A clause denotes the set of intervals at which it holds, its run times (`RunTimes`).
Statives denote a maximal interval with all its subintervals
(`stativeDenotation`, a principal downset); accomplishments denote a
singleton (`accomplishmentDenotation`); `timeTrace` projects an interval
set to the time points it covers. An event predicate denotes the image of its events under
the temporal trace (`Event.TemporalTrace`). The temporal-connective analyses that
consume this carrier live in their studies (Anscombe1964, Karttunen1974,
BeaverCondoravdi2003, Rett2020a, …).

## References

* [krifka-1989]
-/

@[expose] public section

namespace Tense


variable {T : Type*} [LinearOrder T]

/-- A sentence denotes a set of temporal intervals — its "run-times". -/
abbrev RunTimes (T : Type*) [LinearOrder T] := Set (NonemptyInterval T)

/-- The time points contained in some interval of a denotation. -/
def timeTrace (p : RunTimes T) : Set T :=
  { t | ∃ i ∈ p, t ∈ i }

@[simp] theorem mem_timeTrace {p : RunTimes T} {t : T} :
    t ∈ timeTrace p ↔ ∃ i ∈ p, t ∈ i := Iff.rfl

theorem timeTrace_image {α : Type*} (f : α → NonemptyInterval T) (s : Set α) :
    timeTrace (f '' s) = { t | ∃ a ∈ s, t ∈ f a } := by
  ext t; simp

@[simp] theorem timeTrace_empty : timeTrace (∅ : RunTimes T) = ∅ := by
  ext; simp [timeTrace]

@[simp] theorem timeTrace_singleton (i : NonemptyInterval T) :
    timeTrace {i} = (i : Set T) := by
  ext; simp [timeTrace]

@[simp] theorem timeTrace_insert (i : NonemptyInterval T) (p : RunTimes T) :
    timeTrace (insert i p) = (i : Set T) ∪ timeTrace p := by
  ext; simp [timeTrace]

theorem mem_timeTrace_pure {a t : T} :
    t ∈ timeTrace {NonemptyInterval.pure a} ↔ t = a := by
  simp

/-- A stative clause holding throughout `i` denotes `i` with all its subintervals, the principal
downset `Set.Iic i`. -/
def stativeDenotation (i : NonemptyInterval T) : RunTimes T :=
  Set.Iic i

/-- An accomplishment over `i` denotes the singleton `{i}`. -/
def accomplishmentDenotation (i : NonemptyInterval T) : RunTimes T :=
  {i}

theorem stativeDenotation_self (i : NonemptyInterval T) :
    i ∈ stativeDenotation i :=
  Set.mem_Iic.mpr le_rfl

theorem timeTrace_stativeDenotation (i : NonemptyInterval T) :
    timeTrace (stativeDenotation i) = { t | t ∈ i } := by
  ext t
  simp only [mem_timeTrace, stativeDenotation, Set.mem_Iic, Set.mem_ofPred_eq,
    NonemptyInterval.mem_def, NonemptyInterval.le_def]
  grind

theorem mem_timeTrace_stativeDenotation {i : NonemptyInterval T} {t : T} :
    t ∈ timeTrace (stativeDenotation i) ↔ t ∈ i := by
  rw [timeTrace_stativeDenotation]; rfl

theorem timeTrace_accomplishmentDenotation (i : NonemptyInterval T) :
    timeTrace (accomplishmentDenotation i) = { t | t ∈ i } := by
  ext t; simp [timeTrace, accomplishmentDenotation]

end Tense
