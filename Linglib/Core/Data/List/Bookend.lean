/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.DropRight
import Linglib.Core.Data.List.DropRight

/-!
# Lists bookended by `replicate` blocks

Generic facts about `replicate m a ++ l ++ replicate n b` — a list with a left bookend
of `m` copies of `a`, a middle `l`, and a right bookend of `n` copies of `b` — and how
`take`, `rtake`, `filter`, and `Sublist` interact with the bookends. These flesh out
the `replicate`/`append` corner of the List API and are candidates for
`Mathlib/Data/List/`.

## Main results

* `List.take_replicate_append` / `List.rtake_append_replicate` — a short `take`/`rtake`
  reaches only into the adjacent bookend, returning its `replicate`.
* `List.filter_replicate_append_replicate` — filtering distributes over the bookends,
  each width collapsing to `0` when its element is filtered out.
* `List.sublist_replicate_append_replicate` / `List.not_sublist_replicate_append_replicate`
  — a middle-sublist embeds, and a pattern that can borrow neither bookend's element
  for its head or last must come from the middle.
-/

namespace List

variable {α : Type*}

/-- A `take` no longer than the left bookend reaches only into it. -/
theorem take_replicate_append {k m : ℕ} {a : α} {l : List α} (h : k ≤ m) :
    (replicate m a ++ l).take k = replicate k a := by
  rw [take_append_of_le_length (by rw [length_replicate]; exact h), take_replicate,
    Nat.min_eq_left h]

/-- An `rtake` no longer than the right bookend reaches only into it. -/
theorem rtake_append_replicate {k n : ℕ} {b : α} {l : List α} (h : k ≤ n) :
    (l ++ replicate n b).rtake k = replicate k b := by
  rw [rtake_append_of_le_length _ _ (by rw [length_replicate]; exact h),
    rtake_eq_reverse_take_reverse, reverse_replicate, take_replicate, Nat.min_eq_left h,
    reverse_replicate]

/-- Filtering distributes over both bookends; a bookend width collapses to `0` when its
element fails the predicate. -/
theorem filter_replicate_append_replicate (p : α → Bool) (m : ℕ) (a : α) (l : List α)
    (n : ℕ) (b : α) :
    (replicate m a ++ l ++ replicate n b).filter p =
      replicate (if p a then m else 0) a ++ l.filter p ++ replicate (if p b then n else 0) b := by
  by_cases hL : p a = true <;> by_cases hR : p b = true <;>
    simp [filter_append, filter_replicate_of_pos, filter_replicate_of_neg, hL, hR]

/-- A sublist of the middle is a sublist of the bookended list. -/
theorem sublist_replicate_append_replicate {pat l : List α} (h : pat <+ l)
    (m : ℕ) (a : α) (n : ℕ) (b : α) :
    pat <+ replicate m a ++ l ++ replicate n b :=
  (h.trans (sublist_append_right _ _)).trans (sublist_append_left _ _)

/-- A pattern whose head is not `a` and whose last element is not `b`, and which is not a
sublist of the middle, is not a sublist of the bookended list: the `replicate` blocks can
supply neither its head nor its last element, so any embedding must lie in the middle. -/
theorem not_sublist_replicate_append_replicate {pat l : List α} {a b : α}
    (h_head : pat.head? ≠ some a) (h_last : pat.getLast? ≠ some b)
    (h_mid : ¬ pat <+ l) (m n : ℕ) :
    ¬ pat <+ replicate m a ++ l ++ replicate n b := by
  intro hsub
  obtain ⟨s₁, s₂, hs_eq, hs₁_sub, hs₂_sub⟩ := sublist_append_iff.mp hsub
  obtain ⟨j, _, rfl⟩ := sublist_replicate_iff.mp hs₂_sub
  have hj0 : j = 0 := by
    by_contra h_ne
    apply h_last
    have h_eq := congrArg getLast? hs_eq
    rwa [getLast?_append, getLast?_replicate, if_neg h_ne, Option.some_or] at h_eq
  rw [hj0, replicate_zero, append_nil] at hs_eq
  rw [← hs_eq] at hs₁_sub
  obtain ⟨t₁, t₂, ht_eq, ht₁_sub, ht₂_sub⟩ := sublist_append_iff.mp hs₁_sub
  obtain ⟨i, _, rfl⟩ := sublist_replicate_iff.mp ht₁_sub
  have hi0 : i = 0 := by
    by_contra h_ne
    apply h_head
    have h_eq := congrArg head? ht_eq
    rwa [head?_append, head?_replicate, if_neg h_ne, Option.some_or] at h_eq
  rw [hi0, replicate_zero, nil_append] at ht_eq
  rw [← ht_eq] at ht₂_sub
  exact h_mid ht₂_sub

end List
