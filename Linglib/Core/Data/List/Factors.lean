/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Infix

/-!
# Length-`k` infixes of a list

`List.kFactors k xs` lists the contiguous length-`k` infixes of `xs`, the infix sibling of
`List.sublistsLen` (length-`k` subsequences): `List.mem_kFactors` characterizes membership as
`f <:+: xs ∧ f.length = k`, and `List.kFactors_cons` is the recursion that computes it. The
name is the subregular literature's "`k`-factor"; mathlib has no length-`k` infix enumerator.

## Main definitions

* `List.kFactors`: the contiguous length-`k` infixes of a list, in order of occurrence.

## Main results

* `List.mem_kFactors`: membership is being a length-`k` infix, mirroring `List.mem_sublistsLen`.
* `List.kFactors_nil`, `List.kFactors_cons`, `List.kFactors_two_cons_cons`: the recursion, and its
  `k = 2` form used by chain characterizations of the strictly 2-local languages.
-/

@[expose] public section

namespace List

variable {α : Type*} {k : ℕ} {xs f : List α}

/-- The contiguous length-`k` infixes of `xs`, in order of occurrence: the length-`k` prefixes
of the suffixes long enough to have one. -/
def kFactors (k : ℕ) (xs : List α) : List (List α) :=
  (xs.tails.filter (k ≤ ·.length)).map (·.take k)

/-- A list is a `k`-factor of `xs` iff it is a length-`k` infix. -/
theorem mem_kFactors : f ∈ kFactors k xs ↔ f <:+: xs ∧ f.length = k := by
  simp only [kFactors, mem_map, mem_filter, mem_tails, decide_eq_true_eq]
  constructor
  · rintro ⟨s, ⟨hs, hk⟩, rfl⟩
    exact ⟨(take_prefix _ s).isInfix.trans hs.isInfix, length_take_of_le hk⟩
  · rintro ⟨⟨s, t, rfl⟩, rfl⟩
    exact ⟨f ++ t, ⟨⟨s, by simp⟩, by simp⟩, by simp⟩

@[simp] theorem kFactors_nil : kFactors k ([] : List α) = if k = 0 then [[]] else [] := by
  rcases k with _ | k <;> simp [kFactors]

@[simp] theorem kFactors_cons (a : α) (l : List α) :
    kFactors k (a :: l) =
      if k ≤ l.length + 1 then (a :: l).take k :: kFactors k l else kFactors k l := by
  simp only [kFactors, tails_cons, filter_cons, length_cons, decide_eq_true_eq]
  split_ifs <;> simp

/-- The 2-factors of `a :: b :: rest` are `[a, b]` followed by those of `b :: rest`. -/
theorem kFactors_two_cons_cons (a b : α) (rest : List α) :
    kFactors 2 (a :: b :: rest) = [a, b] :: kFactors 2 (b :: rest) := by
  rw [kFactors_cons, ite_eq_left (by simp)]; rfl

end List
