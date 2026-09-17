/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Destutter

/-!
# `List.destutter` and `++`

`Mathlib/Data/List/Destutter.lean` has no lemma relating `destutter` to `++`. The primitive is
the append decomposition `List.destutter'_append`: destuttering `l ++ m` from `a` destutters `l`
from `a` and then `m` from the last element kept. From it, destuttering the left operand first
changes nothing for any relation, and for `(· ≠ ·)` the same holds on the right, so
`destutter (· ≠ ·)` is a congruence for `++`. Lemmas specific to `(· ≠ ·)` carry the `_ne` suffix
as in `List.map_destutter_ne`. [UPSTREAM] candidates for that file.

## Main results

* `List.head?_destutter'`, `List.head?_destutter`, `List.destutter'_eq_cons`: the running
  element stays in front, so `destutter` preserves the head.
* `List.destutter'_append`: the append decomposition.
* `List.destutter_append_left`, `List.destutter_append_right_ne`,
  `List.destutter_append_destutter_ne`: absorbing a `destutter` of either operand, and the
  `++`-congruence.
* `List.destutter_replicate`: a constant run fuses to one element when the relation is
  irreflexive at it.
* `List.IsChain.length_destutter_ne_append`: two chains concatenated and destuttered lose exactly
  one element when the seam matches, the numerical core of the autosegmental OCP quotient.
-/

namespace List
variable {α : Type*} {R : α → α → Prop} [DecidableRel R] {a b : α} {l m : List α}

/-- Destuttering from `a` keeps `a` in front. -/
theorem head?_destutter' (a : α) (l : List α) : (l.destutter' R a).head? = some a := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => by_cases h : R a b <;> simp [h, ih]

/-- `destutter` preserves the head. -/
theorem head?_destutter (l : List α) : (l.destutter R).head? = l.head? := by
  cases l <;> simp [destutter_cons', head?_destutter']

theorem destutter'_eq_cons (a : α) (l : List α) : ∃ t, l.destutter' R a = a :: t :=
  ⟨_, (cons_head?_tail (head?_destutter' a l)).symm⟩

theorem getLastD_destutter' (a : α) (l : List α) (x y : α) :
    (l.destutter' R a).getLastD x = (l.destutter' R a).getLastD y := by
  obtain ⟨t, ht⟩ := destutter'_eq_cons (R := R) a l
  rw [ht, getLastD_cons, getLastD_cons]

/-- The append decomposition: destuttering `l ++ m` from `a` destutters `l` from `a`, then
destutters `m` from the last element kept. -/
theorem destutter'_append (a : α) (l m : List α) :
    (l ++ m).destutter' R a =
      l.destutter' R a ++ (m.destutter' R ((l.destutter' R a).getLastD a)).tail := by
  induction l generalizing a with
  | nil =>
    obtain ⟨t, ht⟩ := destutter'_eq_cons (R := R) a m
    simp [ht]
  | cons b l ih =>
    by_cases h : R a b
    · rw [cons_append, destutter'_cons_pos (h := h), destutter'_cons_pos (h := h), ih b,
        cons_append, getLastD_cons, getLastD_destutter' b l a b]
    · rw [cons_append, destutter'_cons_neg (h := h), destutter'_cons_neg (h := h), ih a]

/-- Destuttering the left operand before appending does not change the result. -/
theorem destutter_append_left (l m : List α) :
    (l.destutter R ++ m).destutter R = (l ++ m).destutter R := by
  cases l with
  | nil => simp
  | cons a l =>
    obtain ⟨t, ht⟩ := destutter'_eq_cons (R := R) a l
    have hc : (a :: t).IsChain R := ht ▸ isChain_destutter' R l a
    rw [destutter_cons', ht, cons_append, destutter_cons', cons_append, destutter_cons',
      destutter'_append, destutter'_append, ht, destutter'_of_isChain_cons _ _ hc]

theorem destutter'_replicate (h : ¬ R a a) (n : ℕ) : (replicate n a).destutter' R a = [a] := by
  induction n with
  | zero => rfl
  | succ m ih => rw [replicate_succ, destutter'_cons_neg _ h, ih]

/-- `destutter` fuses a constant run whenever the relation is irreflexive at its element. -/
theorem destutter_replicate (h : ¬ R a a) (n : ℕ) : (replicate (n + 1) a).destutter R = [a] := by
  rw [replicate_succ, destutter_cons', destutter'_replicate h]

variable [DecidableEq α]

/-- Destuttering from `a` is insensitive to a prior `destutter (· ≠ ·)` of the argument: after
collapsing, `a` either differs from the head or equals it, and both cases agree. -/
theorem destutter'_destutter_ne (a : α) (m : List α) :
    (m.destutter (· ≠ ·)).destutter' (· ≠ ·) a = m.destutter' (· ≠ ·) a := by
  cases m with
  | nil => simp
  | cons c m =>
    obtain ⟨t, ht⟩ := destutter'_eq_cons (R := (· ≠ ·)) c m
    have hc : (c :: t).IsChain (· ≠ ·) := ht ▸ isChain_destutter' _ m c
    rw [destutter_cons', ht]
    by_cases h : a ≠ c
    · rw [destutter'_cons_pos (h := h), destutter'_cons_pos (h := h),
        destutter'_of_isChain_cons _ _ hc, ht]
    · obtain rfl : a = c := not_not.mp h
      rw [destutter'_cons_neg (h := h), destutter'_cons_neg (h := h),
        destutter'_of_isChain_cons _ _ hc, ht]

/-- Destuttering the right operand before appending does not change the result. Unlike
`List.destutter_append_left`, this needs `(· ≠ ·)`: a dropped element must behave like the
running one, which for `(· ≠ ·)` means being equal to it. -/
theorem destutter_append_right_ne (l m : List α) :
    (l ++ m.destutter (· ≠ ·)).destutter (· ≠ ·) = (l ++ m).destutter (· ≠ ·) := by
  cases l with
  | nil => simpa using destutter_idem m (· ≠ ·)
  | cons a l =>
    rw [cons_append, cons_append, destutter_cons', destutter_cons', destutter'_append,
      destutter'_append, destutter'_destutter_ne]

/-- `destutter (· ≠ ·)` is a congruence for `++`. -/
theorem destutter_append_destutter_ne (l m : List α) :
    (l ++ m).destutter (· ≠ ·) =
      (l.destutter (· ≠ ·) ++ m.destutter (· ≠ ·)).destutter (· ≠ ·) := by
  rw [destutter_append_left, destutter_append_right_ne]

/-- For a chain `m`, destuttering it from `z` drops one element exactly when `z` heads `m`. -/
private theorem length_tail_destutter'_ne_of_isChain {z : α} (h2 : m.IsChain (· ≠ ·)) :
    ((m.destutter' (· ≠ ·) z).tail).length = m.length - (if some z = m.head? then 1 else 0) := by
  cases m with
  | nil => simp [destutter'_nil]
  | cons b m =>
    have hbm : m.destutter' (· ≠ ·) b = b :: m := destutter'_of_isChain_cons _ _ h2
    by_cases hzb : z ≠ b
    · rw [destutter'_cons_pos (h := hzb), hbm]
      simp [ite_eq_right hzb]
    · obtain rfl : z = b := not_not.mp hzb
      rw [destutter'_cons_neg (h := by simp), hbm]; simp

/-- Two chains concatenated and destuttered merge only at the seam: the length is the sum of
lengths minus one exactly when the last element of `l` equals the first of `m`. -/
theorem IsChain.length_destutter_ne_append (h1 : l.IsChain (· ≠ ·)) (h2 : m.IsChain (· ≠ ·)) :
    ((l ++ m).destutter (· ≠ ·)).length =
      l.length + m.length - (if l.getLast? = m.head? then 1 else 0) := by
  cases l with
  | nil =>
    cases m with
    | nil => simp
    | cons b m => simp [destutter_of_isChain _ _ h2]
  | cons a l =>
    rw [cons_append, destutter_cons', destutter'_append, destutter'_of_isChain_cons _ _ h1,
      length_append, length_cons, length_tail_destutter'_ne_of_isChain h2,
      getLastD_eq_getLast?, getLast?_eq_some_getLast (cons_ne_nil a l), Option.getD_some]
    split_ifs with h
    · have := length_pos_of_ne_nil (l := m) (by rintro rfl; simp at h)
      omega
    · omega
end List
