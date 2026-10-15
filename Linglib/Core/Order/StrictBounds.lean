module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Set.Basic

/-!
# Strict bounds of a set

`[UPSTREAM]` The strict analogues of mathlib's `upperBounds` and `lowerBounds`:
`strictUpperBounds s` is the set of points strictly above every element of `s`. Mathlib has no
strict-bounds primitive, routing strictness through `Set.Ioi` or `ssubset` instead.
-/

@[expose] public section

variable {α : Type*} [Preorder α] {s : Set α} {a x : α}

/-- The set of points strictly greater than every element of `s`. -/
@[to_dual /-- The set of points strictly less than every element of `s`. -/]
def strictUpperBounds (s : Set α) : Set α := {x | ∀ ⦃a⦄, a ∈ s → a < x}

@[to_dual]
theorem mem_strictUpperBounds : x ∈ strictUpperBounds s ↔ ∀ ⦃a⦄, a ∈ s → a < x :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem strictUpperBounds_singleton : strictUpperBounds {a} = Set.Ioi a := by
  ext; simp [strictUpperBounds]

@[to_dual (attr := simp)]
theorem strictUpperBounds_empty : strictUpperBounds (∅ : Set α) = Set.univ := by
  ext; simp [strictUpperBounds]
