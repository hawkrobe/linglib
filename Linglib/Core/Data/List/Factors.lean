/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Infix

/-!
# `k`-Factors of a List

The contiguous length-`k` infixes of a list — the infix sibling of
`List.sublistsLen` (length-`k` subsequences). A generic list combinator with no
domain content; used by the subregular hierarchy and a candidate for
`Mathlib/Data/List/`.

## Main definitions

* `List.kFactors k xs` — the contiguous length-`k` infixes of `xs`.

## Main results

* `List.mem_kFactors` — `f` is a `k`-factor of `xs` iff it is a length-`k` infix
  (the infix analog of `List.mem_sublistsLen`).
* `List.take_append_take` — truncating the right operand of an append before taking
  a length-`n` prefix is a no-op (a candidate for `Mathlib/Data/List/`).
-/

namespace List

variable {α : Type*}

/-- Truncating the right operand to length `n` before taking the length-`n` prefix of an
append is a no-op: the prefix already ignores everything past position `n`. -/
lemma take_append_take (n : ℕ) (X Y : List α) :
    (X ++ Y.take n).take n = (X ++ Y).take n := by
  rw [take_append, take_append, take_take, min_eq_left (by omega)]

/-- A list is an infix of another iff some shift aligns every position of `S` with
`A` (`getElem?`-wise): `S <:+: A` exactly when there is an offset `δ` with
`A[i + δ]? = S[i]?` for every `i < S.length`. The equations force the offset in
bounds when `S` is nonempty. The positional companion of `mem_kFactors`. -/
theorem isInfix_iff_exists_offset (S A : List α) :
    S <:+: A ↔ ∃ δ, ∀ i < S.length, A[i + δ]? = S[i]? := by
  constructor
  · rintro ⟨s, t, rfl⟩
    refine ⟨s.length, fun i hi => ?_⟩
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel,
      List.getElem?_append_left hi]
  · rintro ⟨δ, hmatch⟩
    rcases Nat.eq_zero_or_pos S.length with h0 | hpos
    · obtain rfl : S = [] := List.length_eq_zero_iff.mp h0
      exact List.nil_infix
    · have hS : (A.drop δ).take S.length = S := by
        apply List.ext_getElem?
        intro i
        rcases lt_or_ge i S.length with hi | hi
        · rw [List.getElem?_take_of_lt hi, List.getElem?_drop, Nat.add_comm δ i]; exact hmatch i hi
        · rw [List.getElem?_take_eq_none hi, List.getElem?_eq_none hi]
      refine ⟨A.take δ, A.drop (δ + S.length), ?_⟩
      conv_rhs => rw [← List.take_append_drop δ A, ← List.take_append_drop S.length (A.drop δ)]
      rw [hS, List.drop_drop, List.append_assoc]

section KFactors

variable (k : ℕ) (xs : List α)

/-- The contiguous length-`k` infixes of `xs`. Built by enumerating suffixes
and taking each one's length-`k` prefix; suffixes shorter than `k` are
filtered out. (For `k = 0` every suffix qualifies, so `kFactors 0 xs` is
`xs.length + 1` copies of `[]`; the subregular hierarchy only uses `k ≥ 1`.) -/
def kFactors : List (List α) :=
  (xs.tails.filter (k ≤ ·.length)).map (·.take k)

variable {k xs} {f : List α}

/-- A list is a `k`-factor of `xs` iff it is a length-`k` infix. The infix
analog of `List.mem_sublistsLen`. -/
lemma mem_kFactors : f ∈ kFactors k xs ↔ f <:+: xs ∧ f.length = k := by
  constructor
  · intro h
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    obtain ⟨hs_tail, hlen⟩ := List.mem_filter.mp hs
    have hsuffix : s <:+ xs := (List.mem_tails ..).mp hs_tail
    exact ⟨(List.take_prefix _ s).isInfix.trans hsuffix.isInfix,
      List.length_take_of_le (by simpa using hlen)⟩
  · rintro ⟨⟨s, t, rfl⟩, rfl⟩
    refine List.mem_map.mpr ⟨f ++ t, List.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [List.mem_tails, List.append_assoc]; exact List.suffix_append s (f ++ t)
    · simp
    · simp

/-- Every member of `kFactors k xs` has length exactly `k`. -/
lemma length_of_mem_kFactors (h : f ∈ kFactors k xs) : f.length = k :=
  (mem_kFactors.mp h).2

/-- A `k`-factor of `xs` is a contiguous infix of `xs`. -/
lemma isInfix_of_mem_kFactors (h : f ∈ kFactors k xs) : f <:+: xs :=
  (mem_kFactors.mp h).1

/-- The 2-factors of `a :: b :: rest` are `[a, b]` followed by the 2-factors
of `b :: rest`: the inductive step for chain-based characterizations of the
SL₂ and TSL₂ languages. -/
lemma kFactors_two_cons_cons (a b : α) (rest : List α) :
    kFactors 2 (a :: b :: rest) = [a, b] :: kFactors 2 (b :: rest) := by
  simp [kFactors, List.tails, List.filter, List.take]

/-- An empty list has no 2-factors. -/
@[simp] lemma kFactors_two_nil : kFactors 2 ([] : List α) = [] := rfl

/-- A singleton list has no 2-factors. -/
@[simp] lemma kFactors_two_singleton (a : α) : kFactors 2 [a] = [] := rfl

end KFactors

end List
