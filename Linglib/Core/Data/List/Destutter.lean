/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Destutter

/-!
# Append congruence for `List.destutter`

Mathlib's `Mathlib/Data/List/Destutter.lean` has no `destutter`-vs-`append` lemma. These
fill that gap for the `(· ≠ ·)` relation: collapsing either operand before appending is
absorbed by an outer `destutter`, so `destutter (· ≠ ·)` is a congruence for `++`. The
proofs go through `destutter'` boundary scaffolding. Candidates for
`Mathlib/Data/List/Destutter.lean`.

## Main results

* `List.destutter_append_left` / `List.destutter_append_right` — collapsing one operand
  before appending does not change the destuttered result.
* `List.destutter_append_destutter` — the congruence: `destutter (· ≠ ·)` of an append
  equals `destutter (· ≠ ·)` of the destuttered operands.
-/

namespace List

variable {α : Type*} [DecidableEq α]

/-- `destutter' (· ≠ ·) a l` always begins with its running element `a`. Holds for any
`[DecidableRel R]`. -/
private theorem destutter'_head_cons {α : Type*} {R : α → α → Prop} [DecidableRel R]
    (a : α) (l : List α) :
    ∃ t, l.destutter' R a = a :: t := by
  induction l generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons b l ih =>
    by_cases h : R a b
    · exact ⟨l.destutter' R b, by rw [destutter'_cons_pos (h := h)]⟩
    · rw [destutter'_cons_neg (h := h)]; exact ih a

/-- Re-running `destutter' (· ≠ ·)` against its own running element drops the duplicate head. -/
private theorem destutter'_ne_cons_self (a : α) (l : List α) :
    (a :: l).destutter' (· ≠ ·) a = l.destutter' (· ≠ ·) a := by
  rw [destutter'_cons_neg (h := by simp)]

/-- If `destutter' (· ≠ ·) c m = c :: t`, the tail `t` is already fixed by `destutter' c`. -/
private theorem destutter'_ne_tail_fixed {c : α} {m t : List α}
    (ht : m.destutter' (· ≠ ·) c = c :: t) : t.destutter' (· ≠ ·) c = c :: t :=
  destutter'_of_isChain_cons t (· ≠ ·) (ht ▸ isChain_destutter' (· ≠ ·) m c)

/-- `destutter' (· ≠ ·) a` is insensitive to a leading `destutter' (· ≠ ·) a` on its left
operand (running-element form). -/
private theorem destutter'_ne_append_left (a : α) (l y : List α) :
    (l.destutter' (· ≠ ·) a ++ y).destutter' (· ≠ ·) a = (l ++ y).destutter' (· ≠ ·) a := by
  induction l generalizing a with
  | nil => simp [destutter'_cons_neg]
  | cons b l ih =>
    by_cases h : a ≠ b
    · obtain ⟨t, ht⟩ := destutter'_head_cons (R := (· ≠ ·)) b l
      have key := ih b
      rw [ht, cons_append, destutter'_ne_cons_self] at key
      rw [destutter'_cons_pos (h := h), cons_append, destutter'_ne_cons_self, cons_append,
        destutter'_cons_pos (h := h), ht, cons_append, destutter'_cons_pos (h := h), key]
    · rw [destutter'_cons_neg (h := h), cons_append, destutter'_cons_neg (h := h)]; exact ih a

/-- `destutter' (· ≠ ·) a` is insensitive to a leading `destutter (· ≠ ·)` of its argument. -/
private theorem destutter'_ne_destutter (a : α) (y : List α) :
    (y.destutter (· ≠ ·)).destutter' (· ≠ ·) a = y.destutter' (· ≠ ·) a := by
  cases y with
  | nil => simp
  | cons c m =>
    rw [destutter_cons']
    obtain ⟨t, ht⟩ := destutter'_head_cons (R := (· ≠ ·)) c m
    by_cases h : a ≠ c
    · rw [ht, destutter'_cons_pos (h := h), destutter'_cons_pos (h := h),
        destutter'_ne_tail_fixed ht, ht]
    · obtain rfl : a = c := not_not.mp h
      rw [ht, destutter'_cons_neg (h := h), destutter'_cons_neg (h := h),
        destutter'_ne_tail_fixed ht, ht]

/-- `destutter' (· ≠ ·) a` is insensitive to a leading `destutter (· ≠ ·)` on its right
operand (running-element form). -/
private theorem destutter'_ne_append_right (a : α) (l y : List α) :
    (l ++ y.destutter (· ≠ ·)).destutter' (· ≠ ·) a = (l ++ y).destutter' (· ≠ ·) a := by
  induction l generalizing a with
  | nil => simpa using destutter'_ne_destutter a y
  | cons b l ih =>
    by_cases h : a ≠ b
    · rw [cons_append, cons_append, destutter'_cons_pos (h := h),
        destutter'_cons_pos (h := h), ih b]
    · rw [cons_append, cons_append, destutter'_cons_neg (h := h),
        destutter'_cons_neg (h := h), ih a]

/-- Collapsing the left operand before appending does not change the destuttered result. -/
theorem destutter_append_left (l m : List α) :
    (l.destutter (· ≠ ·) ++ m).destutter (· ≠ ·) = (l ++ m).destutter (· ≠ ·) := by
  cases l with
  | nil => simp
  | cons a l =>
    obtain ⟨t, ht⟩ := destutter'_head_cons (R := (· ≠ ·)) a l
    rw [destutter_cons', ht, cons_append, destutter_cons', cons_append, destutter_cons']
    have key := destutter'_ne_append_left a l m
    rwa [ht, cons_append, destutter'_ne_cons_self] at key

/-- Collapsing the right operand before appending does not change the destuttered result. -/
theorem destutter_append_right (l m : List α) :
    (l ++ m.destutter (· ≠ ·)).destutter (· ≠ ·) = (l ++ m).destutter (· ≠ ·) := by
  cases l with
  | nil => simpa using destutter_idem m (· ≠ ·)
  | cons a l =>
    rw [cons_append, cons_append, destutter_cons', destutter_cons', destutter'_ne_append_right]

/-- The append congruence: `destutter (· ≠ ·)` of an append equals `destutter (· ≠ ·)` of
the destuttered operands. -/
theorem destutter_append_destutter (l m : List α) :
    (l ++ m).destutter (· ≠ ·) =
      (l.destutter (· ≠ ·) ++ m.destutter (· ≠ ·)).destutter (· ≠ ·) := by
  rw [destutter_append_left, destutter_append_right]

end List
