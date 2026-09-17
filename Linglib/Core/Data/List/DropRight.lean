/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.DropRight

/-!
# Lemmas about `List.rtake`

`Mathlib/Data/List/DropRight.lean` defines `List.rtake l n`, the last `n` elements of `l`, but
proves almost nothing about it. This file supplies the tail mirrors of the `List.take` API in
`Init/Data/List/Nat/TakeDrop.lean`, each proved by reducing to its `take` counterpart through
`List.rtake_eq_reverse_take_reverse`. [UPSTREAM] candidates for `Mathlib/Data/List/DropRight.lean`.

## Main results

* `List.length_rtake`, `List.length_rtake_le`, `List.rtake_of_length_le`: the length of a
  tail-take and its saturation on a short list, mirroring `List.length_take`,
  `List.length_take_le`, and `List.take_of_length_le`.
* `List.getElem?_rtake` and `List.getLast?_rtake`: indexing into a tail-take, mirroring
  `List.getElem?_drop` and `List.head?_take`.
* `List.rtake_rtake` and `List.rtake_append`: nested tail-takes and the tail-take of an append,
  mirroring `List.take_take` and `List.take_append`; `List.rtake_append_of_le_length` is the
  corollary mirroring `List.take_append_of_le_length`.
* `List.rdrop_append_rtake`: the tail analog of `List.take_append_drop`.
* `List.rtake_append_rtake` and `List.rtake_append_append_of_le_length`: the last `n` elements
  are a sufficient state, so truncating before appending, or prepending anything to a block of
  length at least `n`, leaves the tail-take unchanged.
-/

namespace List

variable {α : Type*} {l l₁ l₂ : List α} {m n : ℕ}

@[simp] theorem length_rtake : (l.rtake n).length = min n l.length := by
  simp [rtake_eq_reverse_take_reverse]

theorem length_rtake_le (n : ℕ) (l : List α) : (l.rtake n).length ≤ n := by simp

theorem rtake_of_length_le (h : l.length ≤ n) : l.rtake n = l := by
  rw [rtake_eq_reverse_take_reverse, take_of_length_le (by rwa [length_reverse]), reverse_reverse]

theorem getElem?_rtake {i : ℕ} : (l.rtake n)[i]? = l[l.length - n + i]? :=
  getElem?_drop

theorem getLast?_rtake : (l.rtake n).getLast? = if n = 0 then none else l.getLast? := by
  rw [rtake_eq_reverse_take_reverse, getLast?_reverse, head?_take, head?_reverse]

theorem rtake_rtake : (l.rtake n).rtake m = l.rtake (min m n) := by
  simp [rtake_eq_reverse_take_reverse, take_take]

theorem rtake_append : (l₁ ++ l₂).rtake n = l₁.rtake (n - l₂.length) ++ l₂.rtake n := by
  simp [rtake_eq_reverse_take_reverse, take_append]

theorem rtake_append_of_le_length (h : n ≤ l₂.length) : (l₁ ++ l₂).rtake n = l₂.rtake n := by
  simp [rtake_append, Nat.sub_eq_zero_of_le h]

@[simp] theorem rdrop_append_rtake (n : ℕ) (l : List α) : l.rdrop n ++ l.rtake n = l := by
  rw [rdrop_eq_reverse_drop_reverse, rtake_eq_reverse_take_reverse, ← reverse_append,
    take_append_drop, reverse_reverse]

/-- Truncating to the last `n` elements before appending is the same as truncating after: the
last `n` elements are enough state to compute the next window. -/
theorem rtake_append_rtake (n : ℕ) (l₁ l₂ : List α) :
    (l₁.rtake n ++ l₂).rtake n = (l₁ ++ l₂).rtake n := by
  rw [rtake_append, rtake_append, rtake_rtake, Nat.min_eq_left (Nat.sub_le _ _)]

/-- A middle block of length at least `n` screens off everything to its left: the last `n`
elements of `a ++ u ++ y` do not depend on `a`. -/
theorem rtake_append_append_of_le_length (a u y : List α) (h : n ≤ u.length) :
    (a ++ u ++ y).rtake n = (u ++ y).rtake n := by
  rw [rtake_append, rtake_append, rtake_append,
    Nat.sub_eq_zero_of_le (Nat.le_trans (Nat.sub_le _ _) h), rtake_zero, nil_append]

end List
