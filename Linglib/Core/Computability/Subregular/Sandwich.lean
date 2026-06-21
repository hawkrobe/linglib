/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Definite

/-!
# Sandwich words: `replicate kL aL ++ mid ++ replicate kR aR`

A *sandwich word* is a list of the form `replicate kL aL ++ mid ++
replicate kR aR` — `kL` copies of the left bookend `aL`, then a middle,
then `kR` copies of the right bookend `aR`. Bookends may be asymmetric
(`aL ≠ aR`, `kL ≠ kR`), accommodating both symmetric phenomena (e.g.
[lambert-2026] §5.1 Luganda, where `aL = aR = low`) and asymmetric
ones (e.g. [lambert-2026] §4.2 Tsuut'ina, where `aL = posterior`,
`aR = anterior`).

This shape is the workhorse of [lambert-2026]'s parameterised
counterexamples to multitier generalised definiteness (`IsBTLI k`):
given a phonotactic constraint, exhibit two sandwich words sharing the
same bookends that differ in the target language but match on every
length-`k` tier-affix. The substrate factors out the algebraic content:

* `takeAt_left_sandwich` / `takeAt_right_sandwich` — tier-affixes always
  project to `replicate k aL` / `replicate k aR` regardless of `mid`,
  provided `k ≤ kL` / `k ≤ kR`.
* `filter_sandwich_*` — filtering preserves the sandwich shape, with
  bookend widths becoming 0 when the bookend character is dropped.
* `sublist_sandwich_of_sublist_mid` — any sublist of `mid` is a sublist
  of the sandwich.
* `not_sublist_sandwich` — under non-bookend conditions on the
  pattern's head and last element, a sublist of the sandwich must come
  from `mid` alone.

The symmetric specialisation `aL = aR`, `kL = kR` is handled by passing
the same arguments twice; no separate definition is provided.
-/

namespace Subregular

open List  -- for `<+` (List.Sublist) infix

variable {α : Type*}

/-- A *sandwich word* with possibly asymmetric bookends: `kL` copies of
`aL` on the left, then `mid`, then `kR` copies of `aR` on the right. -/
def sandwich (kL : ℕ) (aL : α) (mid : List α) (kR : ℕ) (aR : α) : List α :=
  List.replicate kL aL ++ mid ++ List.replicate kR aR

@[simp] lemma length_sandwich {kL : ℕ} {aL : α} {mid : List α} {kR : ℕ} {aR : α} :
    (sandwich kL aL mid kR aR).length = kL + mid.length + kR := by
  simp only [sandwich, List.length_append, List.length_replicate, Nat.add_assoc]

/-- The length-`k` left tier-affix of a sandwich is `replicate k aL`,
provided the left bookend is at least `k` wide. Side condition keeps
this from `@[simp]` tagging — callers `rw` explicitly. -/
lemma takeAt_left_sandwich {k kL : ℕ} {aL : α} {mid : List α}
    {kR : ℕ} {aR : α} (h : k ≤ kL) :
    Edge.left.takeAt k (sandwich kL aL mid kR aR) = List.replicate k aL := by
  show (List.replicate kL aL ++ mid ++ List.replicate kR aR).take k = List.replicate k aL
  rw [List.append_assoc,
      List.take_append_of_le_length (by simp [List.length_replicate]; exact h),
      List.take_replicate]
  congr 1
  omega

/-- The length-`k` right tier-affix of a sandwich is `replicate k aR`,
provided the right bookend is at least `k` wide. Side condition keeps
this from `@[simp]` tagging — callers `rw` explicitly. -/
lemma takeAt_right_sandwich {k kL : ℕ} {aL : α} {mid : List α}
    {kR : ℕ} {aR : α} (h : k ≤ kR) :
    Edge.right.takeAt k (sandwich kL aL mid kR aR) = List.replicate k aR := by
  show ((List.replicate kL aL ++ mid) ++ List.replicate kR aR).drop
        (((List.replicate kL aL ++ mid) ++ List.replicate kR aR).length - k) =
       List.replicate k aR
  rw [List.drop_append,
      List.drop_of_length_le
        (by simp [List.length_append, List.length_replicate]; omega),
      List.nil_append, List.drop_replicate]
  congr 1
  simp [List.length_append, List.length_replicate]
  omega

/-- Sandwich filter, both bookends kept: shape preserved with original widths. -/
lemma filter_sandwich_of_pos_pos {T : α → Bool} {aL aR : α}
    (hL : T aL = true) (hR : T aR = true)
    {kL : ℕ} {mid : List α} {kR : ℕ} :
    (sandwich kL aL mid kR aR).filter T = sandwich kL aL (mid.filter T) kR aR := by
  unfold sandwich
  simp only [List.filter_append, List.filter_replicate_of_pos hL,
             List.filter_replicate_of_pos hR]

/-- Sandwich filter, left bookend dropped, right kept. -/
lemma filter_sandwich_of_neg_pos {T : α → Bool} {aL aR : α}
    (hL : ¬ T aL = true) (hR : T aR = true)
    {kL : ℕ} {mid : List α} {kR : ℕ} :
    (sandwich kL aL mid kR aR).filter T = mid.filter T ++ List.replicate kR aR := by
  unfold sandwich
  simp only [List.filter_append, List.filter_replicate_of_neg hL,
             List.filter_replicate_of_pos hR, List.nil_append]

/-- Sandwich filter, left bookend kept, right dropped. -/
lemma filter_sandwich_of_pos_neg {T : α → Bool} {aL aR : α}
    (hL : T aL = true) (hR : ¬ T aR = true)
    {kL : ℕ} {mid : List α} {kR : ℕ} :
    (sandwich kL aL mid kR aR).filter T = List.replicate kL aL ++ mid.filter T := by
  unfold sandwich
  simp only [List.filter_append, List.filter_replicate_of_pos hL,
             List.filter_replicate_of_neg hR, List.append_nil]

/-- Sandwich filter, both bookends dropped: collapses to filtered middle. -/
lemma filter_sandwich_of_neg_neg {T : α → Bool} {aL aR : α}
    (hL : ¬ T aL = true) (hR : ¬ T aR = true)
    {kL : ℕ} {mid : List α} {kR : ℕ} :
    (sandwich kL aL mid kR aR).filter T = mid.filter T := by
  unfold sandwich
  simp only [List.filter_append, List.filter_replicate_of_neg hL,
             List.filter_replicate_of_neg hR, List.append_nil, List.nil_append]

/-- Any sublist of the middle is a sublist of the sandwich. -/
lemma sublist_sandwich_of_sublist_mid {pat mid : List α} (h : pat <+ mid)
    (kL : ℕ) (aL : α) (kR : ℕ) (aR : α) :
    pat <+ sandwich kL aL mid kR aR :=
  (h.trans (List.sublist_append_right _ _)).trans (List.sublist_append_left _ _)

/-- A pattern that doesn't start with `aL` or end with `aR`, and isn't a
sublist of `mid`, is not a sublist of the sandwich. The bookend
`replicate` blocks can't supply the head or last element of `pat`, so
any sublist witness must come from `mid` alone. -/
lemma not_sublist_sandwich {pat mid : List α} {aL aR : α}
    (h_first : pat.head? ≠ some aL) (h_last : pat.getLast? ≠ some aR)
    (h_inner : ¬ pat <+ mid) (kL kR : ℕ) :
    ¬ pat <+ sandwich kL aL mid kR aR := by
  intro hsub
  unfold sandwich at hsub
  -- Peel trailing `replicate kR aR` via getLast?.
  obtain ⟨s₁, s₂, hs_eq, hs₁_sub, hs₂_sub⟩ := List.sublist_append_iff.mp hsub
  obtain ⟨n, _, rfl⟩ := List.sublist_replicate_iff.mp hs₂_sub
  have hn0 : n = 0 := by
    by_contra h_ne
    apply h_last
    have h_eq := congrArg List.getLast? hs_eq
    rw [List.getLast?_append, List.getLast?_replicate, if_neg h_ne, Option.some_or] at h_eq
    exact h_eq
  rw [hn0, List.replicate_zero, List.append_nil] at hs_eq
  rw [← hs_eq] at hs₁_sub
  -- Peel leading `replicate kL aL` via head?.
  obtain ⟨t₁, t₂, ht_eq, ht₁_sub, ht₂_sub⟩ := List.sublist_append_iff.mp hs₁_sub
  obtain ⟨m, _, rfl⟩ := List.sublist_replicate_iff.mp ht₁_sub
  have hm0 : m = 0 := by
    by_contra h_ne
    apply h_first
    have h_eq := congrArg List.head? ht_eq
    rw [List.head?_append, List.head?_replicate, if_neg h_ne, Option.some_or] at h_eq
    exact h_eq
  rw [hm0, List.replicate_zero, List.nil_append] at ht_eq
  rw [← ht_eq] at ht₂_sub
  exact h_inner ht₂_sub

end Subregular
