/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.StrictlyPiecewise
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Finite.List
import Mathlib.Logic.Function.Basic

/-!
# Piecewise testable languages (PT_k)

A language is **piecewise `k`-testable** when its membership depends only on the set of
length-`≤ k` subsequences (scattered subwords) of the input [simon-1975] — i.e. membership
factors through the map `subseqSet k`. PT_k is the Boolean closure of SP_k, the
piecewise analogue of locally testable over strictly local.

## Main definitions

* `subseqSet k w`: the subsequences of `w` of length `≤ k`.
* `Language.IsPiecewiseTestable L k`: `Function.FactorsThrough (· ∈ L) (subseqSet k)`.

## Main results

* `Language.IsStrictlyPiecewise.toIsPiecewiseTestable`: `SP_k ⊆ PT_k`.
* `subseqSet_append_congr`: sharing `subseqSet k` is a congruence for concatenation.
* `Language.IsPiecewiseTestable.isRegular`: over a finite alphabet PT languages are regular.
* Closure under complement comes from `Function.FactorsThrough.comp_left`.
-/

open List

variable {α : Type*}

/-- The subsequences of `w` of length **at most** `k`. The "≤ k" (rather than
"exactly k") bound is what keeps strings shorter than `k` distinguishable. -/
def subseqSet (k : ℕ) (w : List α) : Set (List α) :=
  { s | s <+ w ∧ s.length ≤ k }

@[simp] lemma mem_subseqSet {k : ℕ} {s w : List α} :
    s ∈ subseqSet k w ↔ s <+ w ∧ s.length ≤ k :=
  Iff.rfl

/-- Subsequences of length at most `k` are interchangeable across strings sharing
their `subseqSet k`. The ratchet for proving piecewise testability from a predicate
depending only on length-`≤ k` subsequence presence. -/
lemma subseqSet_eq_iff {k : ℕ} {w₁ w₂ : List α}
    (heq : subseqSet k w₁ = subseqSet k w₂) {s : List α} (hlen : s.length ≤ k) :
    s <+ w₁ ↔ s <+ w₂ := by
  simpa [hlen] using Set.ext_iff.mp heq s

/-- Sharing `subseqSet k` is a **congruence** for concatenation: a subsequence of `u ++ v`
splits as a subsequence of `u` followed by one of `v`, each transferable separately. -/
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

/-- Over a finite alphabet `subseqSet k` takes finitely many values: the piecewise
congruence has finite index. -/
theorem finite_range_subseqSet [Finite α] (k : ℕ) :
    (Set.range (subseqSet (α := α) k)).Finite :=
  ((List.finite_length_le α k).finite_subsets).subset
    (by rintro _ ⟨w, rfl⟩; exact fun s hs => hs.2)

namespace Language


variable {α : Type*}

/-- A language is **piecewise `k`-testable**: membership factors through the
length-`≤ k` subsequence set `subseqSet k`. -/
def IsPiecewiseTestable (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (subseqSet k)

/-- Pointwise form: strings with equal `subseqSet k` are `L`-equivalent. -/
lemma isPiecewiseTestable_iff {L : Language α} {k : ℕ} :
    L.IsPiecewiseTestable k ↔
      ∀ w₁ w₂, subseqSet k w₁ = subseqSet k w₂ → (w₁ ∈ L ↔ w₂ ∈ L) :=
  ⟨fun h _ _ h' => iff_of_eq (h h'), fun h _ _ h' => propext (h _ _ h')⟩

/-- **SP_k ⊆ PT_k**: the strictly-piecewise test ("every subsequence of length at most `k`
is permitted") depends only on `subseqSet k`. -/
theorem IsStrictlyPiecewise.toIsPiecewiseTestable {k : ℕ} {L : Language α}
    (h : L.IsStrictlyPiecewise k) : L.IsPiecewiseTestable k := by
  obtain ⟨G, rfl⟩ := h
  refine fun w₁ w₂ heq => propext ⟨fun hw s hlen hs => ?_, fun hw s hlen hs => ?_⟩
  · exact hw s hlen ((subseqSet_eq_iff heq hlen).mpr hs)
  · exact hw s hlen ((subseqSet_eq_iff heq hlen).mp hs)

/-- Over a finite alphabet piecewise testable languages are **regular**: left quotients
factor through the finitely many values of `subseqSet k`. -/
theorem IsPiecewiseTestable.isRegular [Finite α] {L : Language α} {k : ℕ}
    (h : L.IsPiecewiseTestable k) : L.IsRegular := by
  have hft : Function.FactorsThrough L.leftQuotient (subseqSet k) := fun w₁ w₂ hw =>
    Set.ext fun x => isPiecewiseTestable_iff.mp h _ _ (subseqSet_append_congr hw rfl)
  refine isRegular_iff_finite_range_leftQuotient.mpr
    (((finite_range_subseqSet k).image
      (Function.extend (subseqSet k) L.leftQuotient fun _ => ⊥)).subset ?_)
  rintro _ ⟨w, rfl⟩
  exact ⟨subseqSet k w, ⟨w, rfl⟩, hft.extend_apply _ w⟩

end Language
