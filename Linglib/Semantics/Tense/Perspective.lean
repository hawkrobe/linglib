import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic

/-!
# Perspectival tense

This file defines the perspectival presuppositions of the temporal pronouns of
[tsilia-zhao-2026] and [zhao-2025]. Tenses and the temporal adverb ⌈then⌉ denote times,
intervals of a linear order, and are defined relative to a temporal perspective `π`, itself an
interval: PRES presupposes that its reference overlaps `π`, PAST that it precedes `π`, and
⌈then⌉ that it is disjoint from `π`. The perspective is an interpretation parameter that an
operator rebinds for a whole clause, so a clausemate PRES and ⌈then⌉ read the same `π`, and
since ⌈then⌉ restricts the reference of the tense it modifies, the two presuppositions are
inconsistent: the ⌈then⌉-present puzzle. A PAST reference satisfies ⌈then⌉'s presupposition
itself, and a deleted tense carries no presupposition, so ⌈then⌉ is compatible with both.

## Main definitions

* `Overlaps`, `Precedes`: the temporal relations on intervals.
* `presPresup`, `pastPresup`, `thenPresup`: the presuppositions of PRES, PAST and ⌈then⌉
  relative to a perspective.
* `ThenAdverb`: a lexical entry of the ⌈then⌉ class; entries live in the fragments'
  `TemporalDeictic` files.

## Main results

* `then_present_clash`: a reference overlapping the perspective cannot be restricted by a
  ⌈then⌉ disjoint from it.
* `thenPresup_of_pastPresup`: a reference preceding the perspective satisfies ⌈then⌉'s
  presupposition.

## References

* [tsilia-zhao-2026]
* [zhao-2025]
-/

namespace Tense.Perspective

variable {T : Type*}

/-! ### Temporal relations -/

/-- Two times overlap when they share a point. -/
def Overlaps (s t : Set T) : Prop := (s ∩ t).Nonempty

/-- A time precedes another when every point of the first is before every point of the
second. -/
def Precedes [LT T] (s t : Set T) : Prop := ∀ a ∈ s, ∀ b ∈ t, a < b

theorem Overlaps.symm {s t : Set T} (h : Overlaps s t) : Overlaps t s := by
  rw [Overlaps, Set.inter_comm]
  exact h

/-- A time containing an overlapping time overlaps. -/
theorem Overlaps.mono_left {s s' t : Set T} (h : Overlaps s t) (hs : s ⊆ s') : Overlaps s' t :=
  h.mono (Set.inter_subset_inter_left t hs)

/-- Preceding times are disjoint. -/
theorem Precedes.not_overlaps [Preorder T] {s t : Set T} (h : Precedes s t) : ¬ Overlaps s t :=
  λ ⟨a, ha, ha'⟩ => lt_irrefl a (h a ha a ha')

/-! ### The perspectival presuppositions -/

/-- PRES presupposes that its reference overlaps the perspective. -/
def presPresup (π ref : Set T) : Prop := Overlaps ref π

/-- PAST presupposes that its reference precedes the perspective. -/
def pastPresup [LT T] (π ref : Set T) : Prop := Precedes ref π

/-- ⌈then⌉ presupposes that its reference is disjoint from the perspective. -/
def thenPresup (π ref : Set T) : Prop := ¬ Overlaps ref π

/-- A ⌈then⌉-type temporal adverb, a lexical item denoting a time with the `thenPresup`
presupposition: English *then*, Greek *tóte*, Japanese *tōji*. -/
structure ThenAdverb where
  /-- Surface form -/
  form : String
  /-- English gloss -/
  gloss : String
  deriving Repr, DecidableEq

/-! ### The ⌈then⌉-present clash -/

/-- The ⌈then⌉-present clash: ⌈then⌉ restricts the reference of the tense it modifies, so a
reference overlapping the perspective cannot be restricted by a ⌈then⌉ disjoint from it. -/
theorem then_present_clash {π r th : Set T} (hp : presPresup π r) (hd : r ⊆ th)
    (ht : thenPresup π th) : False :=
  ht (hp.mono_left hd)

/-- A reference preceding the perspective satisfies ⌈then⌉'s presupposition: ⌈then⌉ can
restrict a PAST to its own reference. -/
theorem thenPresup_of_pastPresup [Preorder T] {π r : Set T} (h : pastPresup π r) :
    thenPresup π r :=
  h.not_overlaps

end Tense.Perspective
