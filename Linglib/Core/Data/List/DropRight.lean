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

end List
