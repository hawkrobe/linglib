/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Interval

/-!
# Run times

After Krifka, a clause denotes its run times, the set of intervals at which it holds. A stative
clause holding throughout `i` denotes `i` with all its subintervals, the principal lower set
`Set.Iic i`, an accomplishment over `i` the singleton `{i}`, and an event predicate the image of
its events under the temporal trace (`Event.TemporalTrace`). This file defines the time trace of
a set of intervals, the time points it covers, and Anscombe's universal *before*, a time of one
clause before every time of the other, the reading he gives *before ever*. The other analyses of
temporal connectives built on run times live in their studies.

## Main definitions

* `Tense.timeTrace`: the time points that a set of intervals covers.
* `Tense.beforeEver`: Anscombe's universal *before*.

## References

* [krifka-1989]
* [anscombe-1964]
-/

@[expose] public section

namespace Tense

variable {T : Type*} [LinearOrder T]

/-- The time trace of a set of intervals is the set of time points they contain. -/
def timeTrace (p : Set (NonemptyInterval T)) : Set T :=
  { t | ∃ i ∈ p, t ∈ i }

@[simp] theorem mem_timeTrace {p : Set (NonemptyInterval T)} {t : T} :
    t ∈ timeTrace p ↔ ∃ i ∈ p, t ∈ i := Iff.rfl

theorem timeTrace_image {α : Type*} (f : α → NonemptyInterval T) (s : Set α) :
    timeTrace (f '' s) = { t | ∃ a ∈ s, t ∈ f a } := by
  ext t; simp

@[simp] theorem timeTrace_empty : timeTrace (∅ : Set (NonemptyInterval T)) = ∅ := by
  ext; simp [timeTrace]

@[simp] theorem timeTrace_singleton (i : NonemptyInterval T) :
    timeTrace {i} = (i : Set T) := by
  ext; simp [timeTrace]

@[simp] theorem timeTrace_insert (i : NonemptyInterval T) (p : Set (NonemptyInterval T)) :
    timeTrace (insert i p) = (i : Set T) ∪ timeTrace p := by
  ext; simp [timeTrace]

theorem mem_timeTrace_pure {a t : T} :
    t ∈ timeTrace {NonemptyInterval.pure a} ↔ t = a := by
  simp

/-- A stative clause covers the times of the interval it holds throughout. -/
@[simp] theorem timeTrace_Iic (i : NonemptyInterval T) : timeTrace (Set.Iic i) = (i : Set T) :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hj, ht⟩ ↦ NonemptyInterval.coe_subset_coe.2 hj ht,
    fun ht ↦ ⟨i, Set.mem_Iic.2 le_rfl, ht⟩⟩

theorem mem_timeTrace_Iic {i : NonemptyInterval T} {t : T} :
    t ∈ timeTrace (Set.Iic i) ↔ t ∈ i := by
  rw [timeTrace_Iic]; rfl

/-- *p before ever q* holds when a time of `p` precedes every time of `q`, Anscombe's universal
rendering of *before* ([anscombe-1964] §IV–V). -/
def beforeEver (A B : Set (NonemptyInterval T)) : Prop :=
  ∃ t ∈ timeTrace A, ∀ t' ∈ timeTrace B, t < t'

end Tense
