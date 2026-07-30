/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.DropRight

/-!
# Length, saturation, and decomposition for `List.rtake`

A handful of facts about `List.rtake` (take from the tail) and `List.rdrop`
(drop from the tail) that mathlib's `Mathlib/Data/List/DropRight.lean` defines but
leaves without an API: the length of a tail-take, when it saturates to the whole
list, how it absorbs a left append, and the `rdrop`/`rtake` decomposition. Each is
the tail mirror of a front-end `take` lemma and is proved by reducing to it through
`List.rtake_eq_reverse_take_reverse` — reverse, then `take`. These flesh out an
under-developed corner of mathlib and are candidates for
`Mathlib/Data/List/DropRight.lean`.

## Main results

* `List.length_rtake` — `(l.rtake n).length = min n l.length`.
* `List.length_rtake_le` — `(l.rtake n).length ≤ n`.
* `List.rtake_of_length_le` — a short list is its own tail-take.
* `List.rtake_append_of_le_length` — a tail-take long enough to fit in the right
  summand ignores the left one.
* `List.rdrop_append_rtake` — `l.rdrop n ++ l.rtake n = l`, the tail analog of
  `List.take_append_drop`.
-/

namespace List

variable {α : Type*}

/-- A tail-take has length `min n l.length` — the tail analog of `List.length_take`. -/
@[simp] theorem length_rtake (l : List α) (n : ℕ) :
    (l.rtake n).length = min n l.length := by
  simp [rtake_eq_reverse_take_reverse]

/-- A tail-take has length at most `n` — the tail analog of `List.length_take_le`. -/
theorem length_rtake_le (l : List α) (n : ℕ) : (l.rtake n).length ≤ n := by
  rw [length_rtake]; exact min_le_left _ _

/-- A list no longer than `n` is its own tail-take — the tail analog of
`List.take_of_length_le`. -/
theorem rtake_of_length_le {l : List α} {n : ℕ} (h : l.length ≤ n) : l.rtake n = l := by
  rw [rtake_eq_reverse_take_reverse, take_of_length_le (by rwa [length_reverse]),
    reverse_reverse]

/-- A tail-take that fits inside the right summand ignores the left one — the tail
analog of `List.take_append_of_le_length`. -/
theorem rtake_append_of_le_length {n : ℕ} (l₁ l₂ : List α) (h : n ≤ l₂.length) :
    (l₁ ++ l₂).rtake n = l₂.rtake n := by
  rw [rtake_eq_reverse_take_reverse, reverse_append,
    take_append_of_le_length (by rwa [length_reverse]), ← rtake_eq_reverse_take_reverse]

/-- Splitting a list at its last `n` symbols — the tail analog of
`List.take_append_drop`. -/
@[simp] theorem rdrop_append_rtake (l : List α) (n : ℕ) : l.rdrop n ++ l.rtake n = l := by
  rw [rdrop_eq_reverse_drop_reverse, rtake_eq_reverse_take_reverse, ← reverse_append,
    take_append_drop, reverse_reverse]

/-- Taking a suffix of a suffix takes the shorter of the two. -/
theorem rtake_rtake (m n : ℕ) (l : List α) : (l.rtake n).rtake m = l.rtake (min m n) := by
  simp [rtake_eq_reverse_take_reverse, take_take]

/-- A suffix long enough to swallow `l₂` splits as a suffix of `l₁` followed by `l₂`. -/
theorem rtake_append_of_length_le {n : ℕ} (l₁ l₂ : List α) (h : l₂.length ≤ n) :
    (l₁ ++ l₂).rtake n = l₁.rtake (n - l₂.length) ++ l₂ := by
  simp [rtake_eq_reverse_take_reverse, take_append, take_of_length_le, h]

/-- Truncating to a suffix window before appending is the same as truncating after: the
last `n` symbols are enough state to compute the next window. -/
theorem rtake_append_rtake (n : ℕ) (l₁ l₂ : List α) :
    (l₁.rtake n ++ l₂).rtake n = (l₁ ++ l₂).rtake n := by
  rcases le_or_gt n l₂.length with h | h
  · rw [rtake_append_of_le_length _ _ h, rtake_append_of_le_length _ _ h]
  · rw [rtake_append_of_length_le _ _ h.le, rtake_append_of_length_le _ _ h.le, rtake_rtake,
      min_eq_left (Nat.sub_le _ _)]

/-- A middle block of length `≥ n` screens off everything to its left: the last `n` symbols
of `a ++ u ++ y` do not depend on `a`. -/
theorem rtake_append_append_of_le_length {n : ℕ} (a u y : List α) (h : n ≤ u.length) :
    (a ++ u ++ y).rtake n = (u ++ y).rtake n := by
  rcases le_or_gt n y.length with hy | hy
  · rw [rtake_append_of_le_length (a ++ u) y hy, rtake_append_of_le_length u y hy]
  · rw [rtake_append_of_length_le _ _ hy.le, rtake_append_of_length_le _ _ hy.le,
      rtake_append_of_le_length a u (show n - y.length ≤ u.length by omega)]

end List
