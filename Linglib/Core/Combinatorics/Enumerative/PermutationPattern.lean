/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Permutations realizing an order pattern

Fix an injective tuple `q : Fin k ↪ α` in a finite linear order. Each
permutation of `α` sorts `q` in exactly one of the `k !` possible orders, and
the resulting classes are equinumerous, so one permutation in `k !` leaves `q`
in increasing order.

## Main declarations

* `factorial_mul_card_monotone_comp` — `k ! * #{σ | Monotone (σ ∘ q)} = n !`.
* `card_monotone_comp_eq` — the `k !` classes are equinumerous.

## Implementation notes

`Tuple.comp_sort_eq_comp_iff_monotone` supplies uniqueness of the sorting
reordering and `Equiv.Perm.viaEmbedding` transports a reordering of `Fin k`
to a permutation of `α` fixing everything off the tuple, which turns
precomposition into postcomposition and gives the bijections between classes.

[UPSTREAM] Mathlib has no permutation-pattern material; this belongs at
`Mathlib/Combinatorics/Enumerative/PermutationPattern.lean`.
-/

open Finset Equiv Nat

variable {α : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] {k : ℕ}

omit [LinearOrder α] [Fintype α] [DecidableEq α] in
/-- Transporting `ρ` along `q` turns precomposition by `ρ` into postcomposition. -/
private theorem viaEmbedding_comp (q : Fin k ↪ α) (ρ : Perm (Fin k)) (i : Fin k) :
    (ρ.viaEmbedding q) (q i) = q (ρ i) := Perm.viaEmbedding_apply ρ q i

/-- The permutations sorting a fixed injective tuple into a given order all
    number the same: `Perm α` splits into `k !` equinumerous classes, one per
    reordering of the tuple. -/
theorem card_monotone_comp_eq (q : Fin k ↪ α) (ρ : Perm (Fin k)) :
    #{σ : Perm α | Monotone (σ ∘ q ∘ ρ)} = #{σ : Perm α | Monotone (σ ∘ q)} := by
  apply Finset.card_bij (fun σ _ => σ * (ρ.viaEmbedding q))
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    have : (σ * ρ.viaEmbedding q) ∘ q = σ ∘ q ∘ ρ := by
      funext i; simp [viaEmbedding_comp]
    rwa [this]
  · intro σ _ τ _ h
    exact mul_right_cancel h
  · intro τ hτ
    refine ⟨τ * (ρ.viaEmbedding q)⁻¹, ?_, inv_mul_cancel_right _ _⟩
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    have : (τ * (ρ.viaEmbedding q)⁻¹) ∘ q ∘ ρ = τ ∘ q := by
      funext i
      simp only [Function.comp_apply, Perm.mul_apply]
      simp [← viaEmbedding_comp q ρ i]
    rwa [this]

omit [Fintype α] [DecidableEq α] in
private theorem sort_eq_iff_monotone {f : Fin k → α} (hf : Function.Injective f)
    (ρ : Perm (Fin k)) : Tuple.sort f = ρ ↔ Monotone (f ∘ ρ) := by
  constructor
  · rintro rfl; exact Tuple.monotone_sort f
  · intro h
    exact (Equiv.ext fun i =>
      hf (congrFun (Tuple.comp_sort_eq_comp_iff_monotone.mpr h) i)).symm

/-- **A fixed injective tuple is sorted by one permutation in `k !`.** -/
theorem factorial_mul_card_monotone_comp (q : Fin k ↪ α) :
    k ! * #{σ : Perm α | Monotone (σ ∘ q)} = (Fintype.card α)! := by
  have hfib : ∀ ρ : Perm (Fin k),
      #{σ : Perm α | Tuple.sort (σ ∘ q) = ρ} = #{σ : Perm α | Monotone (σ ∘ q)} := by
    intro ρ
    rw [← card_monotone_comp_eq q ρ]
    congr 1
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    exact sort_eq_iff_monotone ((σ : Perm α).injective.comp q.injective) ρ
  have key : (Fintype.card α)! =
      ∑ ρ : Perm (Fin k), #{σ : Perm α | Tuple.sort (σ ∘ q) = ρ} := by
    rw [← Fintype.card_perm (α := α), ← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [key, Finset.sum_congr rfl (fun ρ _ => hfib ρ), Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  simp
