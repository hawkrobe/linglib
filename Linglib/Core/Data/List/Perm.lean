/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Forall2

/-!
# Permutations of `List.map` images

Two facts about `l₁.map f ~ l₂.map f`: it lifts through `f` to a permutation of `l₁` agreeing
with `l₂` pointwise up to `f`, and it is decided by greedy matching along any Boolean relation
that computes `f a = f b` on the members.

## Main definitions

* `List.isPermBy p l₁ l₂`: greedy matching of `l₁` against `l₂` along `p`, the algorithm of
  `List.isPerm` with `p` in place of `==`.

## Main statements

* `List.exists_perm_forall₂_of_map_perm`: a permutation of `f`-images lifts through `f`.
* `List.isPermBy_iff_perm_map`: if `p a b` computes `f a = f b` for `a ∈ l₁` and `b ∈ l₂`, then
  `isPermBy p l₁ l₂` decides `l₁.map f ~ l₂.map f`.

## Implementation notes

`isPermBy` looks up each match with `findIdx?` and removes it with `eraseIdx`, so `p` is
evaluated once per comparison. The `contains`-then-`erase` shape of `List.isPerm` evaluates every
comparison up to the match twice, which doubles the cost at each level when `p` itself calls
`isPermBy`, as the comparison of unordered trees in `UnorderedTree/DecEq.lean` does.

[UPSTREAM] candidates for `Mathlib/Data/List/Perm/Basic.lean`.
-/

@[expose] public section

namespace List

variable {α β : Type*} {f : α → β}

/-- A permutation of `f`-images lifts through `f`, to a permutation of `l₁` whose `f`-image
agrees pointwise with that of `l₂`. This is the `map` instance of
`List.forall₂_comp_perm_eq_perm_comp_forall₂`. -/
theorem exists_perm_forall₂_of_map_perm {l₁ l₂ : List α} (h : (l₁.map f).Perm (l₂.map f)) :
    ∃ l, l₁.Perm l ∧ Forall₂ (fun a b ↦ f a = f b) l l₂ := by
  have h₁ : Forall₂ (fun a b ↦ f a = b) l₁ (l₁.map f) := forall₂_map_right_iff.2 (forall₂_refl _)
  obtain ⟨l, hl, hF⟩ := (forall₂_comp_perm_eq_perm_comp_forall₂ ▸ ⟨_, h₁, h⟩ :
    Relation.Comp Perm (Forall₂ fun a b ↦ f a = b) l₁ (l₂.map f))
  exact ⟨l, hl, forall₂_map_right_iff.1 hF⟩

/-- Greedy matching of `l₁` against `l₂` along `p`, which pairs each element of `l₁` with the
first `p`-related element of `l₂` still unmatched. -/
def isPermBy (p : α → α → Bool) : List α → List α → Bool
  | [], l₂ => l₂.isEmpty
  | a :: l₁, l₂ =>
    match l₂.findIdx? (p a) with
    | some i => isPermBy p l₁ (l₂.eraseIdx i)
    | none => false

/-- Greedy matching along a Boolean relation computing `f a = f b` decides permutation of the
`f`-images. At `p := (· == ·)` and `f := id` this is `List.isPerm_iff`. -/
theorem isPermBy_iff_perm_map {p : α → α → Bool} :
    ∀ {l₁ l₂ : List α}, (∀ a ∈ l₁, ∀ b ∈ l₂, p a b ↔ f a = f b) →
      (isPermBy p l₁ l₂ ↔ l₁.map f ~ l₂.map f)
  | [], l₂, _ => by simp [isPermBy]
  | a :: l₁, l₂, h => by
    rw [isPermBy]
    split
    · next i hi =>
      obtain ⟨hil, hpi, -⟩ := findIdx?_eq_some_iff_getElem.1 hi
      have := (getElem_cons_eraseIdx_perm hil).map f
      rw [map_cons, ← (h a mem_cons_self _ (getElem_mem hil)).1 hpi] at this
      rw [isPermBy_iff_perm_map fun x hx y hy ↦
        h x (mem_cons_of_mem _ hx) y ((eraseIdx_sublist _ _).subset hy), map_cons,
        ← rel_congr_right this, perm_cons]
    · next hi =>
      refine iff_of_false Bool.false_ne_true fun hp ↦ ?_
      obtain ⟨b, hb, hfb⟩ := mem_map.1 (hp.subset mem_cons_self)
      simpa [(h a mem_cons_self b hb).2 hfb.symm] using findIdx?_eq_none_iff.1 hi b hb

end List
