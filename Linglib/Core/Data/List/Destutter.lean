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
* `List.destutter_head?` — `destutter` preserves the head.
* `List.destutter_append_length_clean` — the clean-clean boundary length: two `(· ≠ ·)`
  chains concatenated and destuttered merge exactly one element iff the seam matches.
* `List.destutterConcat` — append then destutter; the multiplication of the destutter
  quotient monoid, with its associativity and unit laws (pure `List` facts).
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

/-! ### Head and the clean-clean boundary -/

omit [DecidableEq α] in
/-- `destutter` preserves the head: the running element is the input's head. -/
theorem destutter_head? {R : α → α → Prop} [DecidableRel R] (l : List α) :
    (l.destutter R).head? = l.head? := by
  cases l with
  | nil => simp
  | cons a l =>
    obtain ⟨t, ht⟩ := destutter'_head_cons (R := R) a l
    rw [destutter_cons', ht]; simp

/-- The destutter of a chain `a :: l` appended to anything is `a :: l` followed by the
right operand destuttered against the chain's last element (with the duplicated head
dropped). The structural form behind `destutter_append_length_clean`. -/
private theorem destutter'_append_clean {a : α} {l m : List α}
    (h1 : (a :: l).IsChain (· ≠ ·)) :
    (l ++ m).destutter' (· ≠ ·) a =
      a :: l ++ (m.destutter' (· ≠ ·) ((a :: l).getLast (cons_ne_nil a l))).tail := by
  induction l generalizing a with
  | nil =>
    simp only [nil_append, getLast_singleton]
    obtain ⟨t, ht⟩ := destutter'_head_cons (R := (· ≠ ·)) a m
    rw [ht]; rfl
  | cons b l ih =>
    have hab : a ≠ b := (isChain_cons_cons.mp h1).1
    rw [cons_append, destutter'_cons_pos (h := hab), ih (isChain_cons_cons.mp h1).2,
      getLast_cons (cons_ne_nil b l)]
    rfl

/-- For a chain `m`, the tail of `m.destutter' (· ≠ ·) z` has length `m.length` minus one
when the running element `z` already heads `m` (the seam merge), else `m.length`. -/
private theorem destutter'_tail_length_clean {z : α} {m : List α} (h2 : m.IsChain (· ≠ ·)) :
    ((m.destutter' (· ≠ ·) z).tail).length =
      m.length - (if some z = m.head? then 1 else 0) := by
  cases m with
  | nil => simp [destutter'_nil]
  | cons b m =>
    have hbm : m.destutter' (· ≠ ·) b = b :: m := destutter'_of_isChain_cons _ _ h2
    by_cases hzb : z ≠ b
    · rw [destutter'_cons_pos (h := hzb), hbm]
      simp only [tail_cons, length_cons, head?_cons, Option.some.injEq, if_neg hzb, Nat.sub_zero]
    · obtain rfl : z = b := not_not.mp hzb
      rw [destutter'_cons_neg (h := by simp), hbm]; simp

/-- **The clean-clean boundary length.** Two chains concatenated and destuttered merge only
at the seam: the length is the sum of lengths minus one exactly when the last element of `l`
equals the first of `m`. The numerical core of the autosegmental OCP quotient
(`Phonology/Autosegmental/Collapse.lean`). -/
theorem destutter_append_length_clean {l m : List α}
    (h1 : l.IsChain (· ≠ ·)) (h2 : m.IsChain (· ≠ ·)) :
    ((l ++ m).destutter (· ≠ ·)).length =
      l.length + m.length - (if l.getLast? = m.head? then 1 else 0) := by
  cases l with
  | nil =>
    cases m with
    | nil => simp
    | cons b m => simp [destutter_of_isChain _ _ h2]
  | cons a l =>
    rw [cons_append, destutter_cons', destutter'_append_clean h1, length_append, length_cons,
      destutter'_tail_length_clean h2, getLast?_eq_getLast_of_ne_nil (cons_ne_nil a l)]
    split_ifs with h
    · have := length_pos_of_ne_nil (l := m) (by rintro rfl; simp at h)
      omega
    · omega

/-! ### Append-then-destutter

`destutterConcat` — append, then collapse the single run that may form at the seam — is the
multiplication of the destutter quotient monoid (built on the free monoid in
`Mathlib.Algebra.FreeMonoid.Destutter`). Associativity and the unit laws reduce to the
`++`-congruences above, so they are pure `List` facts and live here. -/

/-- **Append then destutter**: concatenate, then collapse the single run that may form at
the seam. The multiplication of the destutter quotient monoid. -/
def destutterConcat (x y : List α) : List α := (x ++ y).destutter (· ≠ ·)

/-- `destutterConcat` outputs are stutter-free. -/
theorem isChain_destutterConcat (x y : List α) :
    (destutterConcat x y).IsChain (· ≠ ·) := isChain_destutter (· ≠ ·) (x ++ y)

/-- `destutterConcat` is associative — inherited from `++` through `destutter`. -/
theorem destutterConcat_assoc (x y z : List α) :
    destutterConcat (destutterConcat x y) z = destutterConcat x (destutterConcat y z) := by
  simp only [destutterConcat, destutter_append_left, destutter_append_right, List.append_assoc]

theorem nil_destutterConcat (x : List α) :
    destutterConcat [] x = x.destutter (· ≠ ·) := rfl

theorem destutterConcat_nil (x : List α) :
    destutterConcat x [] = x.destutter (· ≠ ·) := by simp [destutterConcat]

/-- `destutter (· ≠ ·)` carries `(List α, ++)` onto `(·, destutterConcat)`. -/
theorem destutter_append_eq_destutterConcat (x y : List α) :
    (x ++ y).destutter (· ≠ ·)
      = destutterConcat (x.destutter (· ≠ ·)) (y.destutter (· ≠ ·)) := by
  rw [destutterConcat, ← destutter_append_destutter]

end List
