/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Forall2

/-!
# Lifting a permutation of images through `List.map`

`List.exists_perm_forall₂_of_map_perm`: if `l₁.map f` is a permutation of `l₂.map f`, then `l₁`
permutes to a list whose `f`-images agree pointwise with those of `l₂`. This is the `map`
instance of mathlib's relator law `List.forall₂_comp_perm_eq_perm_comp_forall₂`, with
`R a b := f a = b`. [UPSTREAM] candidate for `Mathlib/Data/List/Perm/Basic.lean`, beside
`List.Perm.map`.
-/

@[expose] public section

namespace List

variable {α β : Type*} {f : α → β} {l₁ l₂ : List α}

/-- A permutation of `f`-images lifts through `f`: `l₁` permutes to a list whose `f`-image
agrees pointwise with that of `l₂`. -/
theorem exists_perm_forall₂_of_map_perm (h : (l₁.map f).Perm (l₂.map f)) :
    ∃ l, l₁.Perm l ∧ Forall₂ (fun a b ↦ f a = f b) l l₂ := by
  have h₁ : Forall₂ (fun a b ↦ f a = b) l₁ (l₁.map f) := forall₂_map_right_iff.2 (forall₂_refl _)
  obtain ⟨l, hl, hF⟩ := (forall₂_comp_perm_eq_perm_comp_forall₂ ▸ ⟨_, h₁, h⟩ :
    Relation.Comp Perm (Forall₂ fun a b ↦ f a = b) l₁ (l₂.map f))
  exact ⟨l, hl, forall₂_map_right_iff.1 hF⟩

end List
