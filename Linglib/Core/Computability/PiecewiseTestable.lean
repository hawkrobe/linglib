/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Set.Finite.List
public import Linglib.Core.Logic.Function.FactorsThrough

/-!
# Piecewise testable languages

A language is *piecewise `k`-testable* when membership of a word depends only on the set of its
subsequences of length at most `k`. These are the piecewise testable events of Simon.

## Main definitions

* `subseqSet k w`: the subsequences of `w` of length at most `k`.
* `Language.IsPiecewiseTestable`: membership in the language factors through `subseqSet k`.

## Main results

* `subseqSet_append_congr`: words with the same subsequences of length at most `k` still have the
  same ones after concatenation.
* `Language.IsPiecewiseTestable.isRegular`: over a finite alphabet, piecewise testable languages
  are regular.

## References

* [simon-1975]
-/

@[expose] public section

open List

variable {α : Type*}

/-- The subsequences of `w` of length at most `k`. The bound is at most `k`, not exactly `k`, so
that words shorter than `k` stay distinguishable. -/
def subseqSet (k : ℕ) (w : List α) : Set (List α) :=
  { s | s <+ w ∧ s.length ≤ k }

@[simp] lemma mem_subseqSet {k : ℕ} {s w : List α} :
    s ∈ subseqSet k w ↔ s <+ w ∧ s.length ≤ k :=
  Iff.rfl

/-- Words with the same `subseqSet k` have the same subsequences of length at most `k`. -/
lemma subseqSet_eq_iff {k : ℕ} {w₁ w₂ : List α}
    (heq : subseqSet k w₁ = subseqSet k w₂) {s : List α} (hlen : s.length ≤ k) :
    s <+ w₁ ↔ s <+ w₂ := by
  simpa [hlen] using Set.ext_iff.mp heq s

/-- Sharing `subseqSet k` is preserved by concatenation, since a subsequence of `u ++ v` splits
as a subsequence of `u` followed by one of `v`. -/
theorem subseqSet_append_congr {k : ℕ} {u₁ u₂ v₁ v₂ : List α}
    (hu : subseqSet k u₁ = subseqSet k u₂) (hv : subseqSet k v₁ = subseqSet k v₂) :
    subseqSet k (u₁ ++ v₁) = subseqSet k (u₂ ++ v₂) := by
  have aux : ∀ {u₁ u₂ v₁ v₂ : List α}, subseqSet k u₁ = subseqSet k u₂ →
      subseqSet k v₁ = subseqSet k v₂ →
      subseqSet k (u₁ ++ v₁) ⊆ subseqSet k (u₂ ++ v₂) := by
    rintro u₁ u₂ v₁ v₂ hu hv s ⟨hsub, hlen⟩
    obtain ⟨s₁, s₂, rfl, h₁, h₂⟩ := sublist_append_iff.mp hsub
    rw [length_append] at hlen
    exact ⟨((subseqSet_eq_iff hu (by omega)).mp h₁).append
      ((subseqSet_eq_iff hv (by omega)).mp h₂), by simp [length_append]; omega⟩
  exact Set.Subset.antisymm (aux hu hv) (aux hu.symm hv.symm)

/-- Over a finite alphabet `subseqSet k` takes finitely many values. -/
theorem finite_range_subseqSet [Finite α] (k : ℕ) :
    (Set.range (subseqSet (α := α) k)).Finite :=
  ((List.finite_length_le α k).finite_subsets).subset
    (by rintro _ ⟨w, rfl⟩; exact fun s hs ↦ hs.2)

namespace Language

/-- A language is *piecewise `k`-testable* when membership factors through the set `subseqSet k`
of subsequences of length at most `k`. -/
def IsPiecewiseTestable (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (subseqSet k)

lemma isPiecewiseTestable_iff {L : Language α} {k : ℕ} :
    L.IsPiecewiseTestable k ↔
      ∀ w₁ w₂, subseqSet k w₁ = subseqSet k w₂ → (w₁ ∈ L ↔ w₂ ∈ L) :=
  ⟨fun h _ _ h' ↦ iff_of_eq (h h'), fun h _ _ h' ↦ propext (h _ _ h')⟩

variable {L M : Language α} {k : ℕ}

theorem IsPiecewiseTestable.compl (h : L.IsPiecewiseTestable k) : Lᶜ.IsPiecewiseTestable k :=
  isPiecewiseTestable_iff.mpr fun w₁ w₂ he ↦ not_congr (isPiecewiseTestable_iff.mp h w₁ w₂ he)

theorem IsPiecewiseTestable.inter (hL : L.IsPiecewiseTestable k)
    (hM : M.IsPiecewiseTestable k) : (L ⊓ M).IsPiecewiseTestable k :=
  isPiecewiseTestable_iff.mpr fun w₁ w₂ he ↦
    and_congr (isPiecewiseTestable_iff.mp hL w₁ w₂ he) (isPiecewiseTestable_iff.mp hM w₁ w₂ he)

theorem IsPiecewiseTestable.union (hL : L.IsPiecewiseTestable k)
    (hM : M.IsPiecewiseTestable k) : (L ⊔ M).IsPiecewiseTestable k :=
  isPiecewiseTestable_iff.mpr fun w₁ w₂ he ↦
    or_congr (isPiecewiseTestable_iff.mp hL w₁ w₂ he) (isPiecewiseTestable_iff.mp hM w₁ w₂ he)

/-- Over a finite alphabet piecewise testable languages are regular, since left quotients factor
through the finitely many values of `subseqSet k`. -/
theorem IsPiecewiseTestable.isRegular [Finite α] (h : L.IsPiecewiseTestable k) : L.IsRegular :=
  .of_finite_range_leftQuotient <| Function.FactorsThrough.finite_range
    (fun _ _ hw ↦ Set.ext fun _ ↦
      isPiecewiseTestable_iff.mp h _ _ (subseqSet_append_congr hw rfl))
    (finite_range_subseqSet k)

end Language
