/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Perm.Basic

/-!
# Permutation invariance from binary symmetry

`List.Perm.congr_arity₂`: a list function symmetric on pairs and constant above
length two is `Perm`-invariant. Keystone for node algebras whose only
order-sensitive shape is binary (Merge-style algebras over unordered daughters).

`List.exists_perm_forall₂_of_map_perm`: a permutation of images lifts to a permutation of the
sources followed by a pointwise identification of images.
-/

/-- A list function symmetric on pairs and constant above length two is
    `Perm`-invariant: lengths ≤ 1 are rigid under permutation, pairs by the
    symmetry, longer lists by the constancy. -/
theorem List.Perm.congr_arity₂ {β γ : Type*} {g : List β → γ} {c : γ}
    (hswap : ∀ x y, g [x, y] = g [y, x])
    (hbig : ∀ l : List β, 2 < l.length → g l = c)
    {l₁ l₂ : List β} (h : l₁.Perm l₂) : g l₁ = g l₂ := by
  induction h with
  | nil => rfl
  | @cons x l₁ l₂ h _ih =>
    match l₁, l₂, h with
    | [], l₂, h => rw [show l₂ = [] from h.symm.eq_nil]
    | [y], l₂, h => rw [show l₂ = [y] from List.perm_singleton.mp h.symm]
    | _ :: _ :: _, l₂, h =>
      have hl := h.length_eq
      rw [hbig _ (by simp +arith), hbig _ (by simp only [List.length_cons] at hl ⊢; omega)]
  | swap x y l =>
    match l with
    | [] => exact hswap y x
    | _ :: _ => rw [hbig _ (by simp +arith), hbig _ (by simp +arith)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A permutation of `f`-images lifts through `f`: `l₁` permutes to a list whose `f`-image
    agrees pointwise with that of `l₂`. -/
theorem List.exists_perm_forall₂_of_map_perm {α β : Type*} [DecidableEq α] (f : α → β) :
    ∀ {l₂ l₁ : List α}, (l₁.map f).Perm (l₂.map f) →
      ∃ l, l₁.Perm l ∧ List.Forall₂ (fun a b => f a = f b) l l₂
  | [], l₁, h =>
    ⟨[], List.map_eq_nil_iff.mp h.eq_nil ▸ List.Perm.refl _, List.Forall₂.nil⟩
  | b :: l₂, l₁, h => by
    obtain ⟨a, ha, hfa⟩ := List.mem_map.mp (h.symm.subset List.mem_cons_self)
    have h' := ((List.perm_cons_erase ha).map f).symm.trans h
    rw [List.map_cons, List.map_cons, hfa] at h'
    obtain ⟨l, hl, hF⟩ := exists_perm_forall₂_of_map_perm f h'.cons_inv
    exact ⟨a :: l, (List.perm_cons_erase ha).trans (hl.cons a), List.Forall₂.cons hfa hF⟩
