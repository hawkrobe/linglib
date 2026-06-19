import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Strict bounds of a set

`[UPSTREAM]` The strict analogues of mathlib's `upperBounds` / `lowerBounds`:
`strictUpperBounds s` is the set of points strictly above every element of `s`.
mathlib has no strict-bounds primitive — strictness is usually routed through
`Set.Ioi` / `ssubset` — so this file fills the gap as a sibling of `upperBounds`,
modelled on it lemma-for-lemma. It backs the set-standard degree comparative
([hoeksema-1983]'s S-comparative) and any "strictly exceeds a whole set" notion.

## Main definitions

* `strictUpperBounds` / `strictLowerBounds` — the `<`-analogues of
  `upperBounds` / `lowerBounds`.

## Main results

* `mem_strictUpperBounds_iff_subset_Iio` — `x ∈ strictUpperBounds s ↔ s ⊆ Set.Iio x`,
  the strict mirror of `mem_upperBounds_iff_subset_Iic`.
* `strictUpperBounds_singleton` — `strictUpperBounds {a} = Set.Ioi a`, the strict
  mirror of `upperBounds_singleton`.
* `strictUpperBounds_subset_upperBounds` — strict bounds are bounds.
-/

variable {α : Type*} [Preorder α] {s : Set α} {a x : α}

/-- The set of points strictly greater than every element of `s`. Strict analogue
of `upperBounds`. -/
def strictUpperBounds (s : Set α) : Set α := { x | ∀ ⦃a⦄, a ∈ s → a < x }

/-- The set of points strictly less than every element of `s`. Strict analogue
of `lowerBounds`. -/
def strictLowerBounds (s : Set α) : Set α := { x | ∀ ⦃a⦄, a ∈ s → x < a }

theorem mem_strictUpperBounds : x ∈ strictUpperBounds s ↔ ∀ ⦃a⦄, a ∈ s → a < x :=
  Iff.rfl

theorem mem_strictLowerBounds : x ∈ strictLowerBounds s ↔ ∀ ⦃a⦄, a ∈ s → x < a :=
  Iff.rfl

/-- Strict mirror of `mem_upperBounds_iff_subset_Iic`. -/
theorem mem_strictUpperBounds_iff_subset_Iio : x ∈ strictUpperBounds s ↔ s ⊆ Set.Iio x :=
  Iff.rfl

/-- Strict mirror of `mem_lowerBounds_iff_subset_Ici`. -/
theorem mem_strictLowerBounds_iff_subset_Ioi : x ∈ strictLowerBounds s ↔ s ⊆ Set.Ioi x :=
  Iff.rfl

theorem strictUpperBounds_subset_upperBounds : strictUpperBounds s ⊆ upperBounds s :=
  fun _ hx _ ha => (hx ha).le

theorem strictLowerBounds_subset_lowerBounds : strictLowerBounds s ⊆ lowerBounds s :=
  fun _ hx _ ha => (hx ha).le

/-- Strict mirror of `upperBounds_singleton`. -/
@[simp] theorem strictUpperBounds_singleton : strictUpperBounds {a} = Set.Ioi a := by
  ext x
  refine ⟨fun h => h rfl, fun h b hb => ?_⟩
  rw [Set.mem_singleton_iff] at hb
  rw [hb]; exact h

/-- Strict mirror of `lowerBounds_singleton`. -/
@[simp] theorem strictLowerBounds_singleton : strictLowerBounds {a} = Set.Iio a := by
  ext x
  refine ⟨fun h => h rfl, fun h b hb => ?_⟩
  rw [Set.mem_singleton_iff] at hb
  rw [hb]; exact h

@[simp] theorem strictUpperBounds_empty : strictUpperBounds (∅ : Set α) = Set.univ := by
  ext x; simp [strictUpperBounds]

@[simp] theorem strictLowerBounds_empty : strictLowerBounds (∅ : Set α) = Set.univ := by
  ext x; simp [strictLowerBounds]
