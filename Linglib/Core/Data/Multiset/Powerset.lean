/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Nat.Choose.Basic

/-!
# Counting sub-multisets in `Multiset.powerset`

The multiplicity of `s` in `t.powerset` is a product of binomial coefficients: a
sub-multiset picks `s.count x` of the `t.count x` copies of each distinct `x`. (This
product of binomials is not `Nat.multinomial`, which is the quotient `(∑ᵢ kᵢ)! / ∏ᵢ kᵢ!`.)

## Main results

* `Multiset.count_powerset_of_le`: for `s ≤ t`,
  `t.powerset.count s = ∏ x ∈ t.toFinset, (t.count x).choose (s.count x)`.
* `Multiset.count_powerset`: the hypothesis-free form, indexed by `(s + t).toFinset` so
  that `Nat.choose` vanishing makes both sides `0` when `s ≰ t`.

## Implementation notes

The induction runs over a fixed ambient `Finset` containing both supports
(`count_powerset_subset`): the index set stays constant through the recursion and the
unconditional induction hypothesis absorbs the `s ≰ t` boundary cases by
`Nat.choose` vanishing. `[UPSTREAM]` candidate; eventual mathlib home
`Mathlib.Data.Multiset.Powerset`.

## Tags

multiset, powerset, count, binomial coefficient
-/

namespace Multiset

variable {α : Type*} [DecidableEq α]

/-- Workhorse for `count_powerset`: the product may be taken over any fixed `Finset`
    containing the supports of both multisets. -/
private theorem count_powerset_subset {S : Finset α} :
    ∀ t : Multiset α, t.toFinset ⊆ S → ∀ s : Multiset α, s.toFinset ⊆ S →
      t.powerset.count s = ∏ x ∈ S, (t.count x).choose (s.count x) := by
  intro t
  induction t using Multiset.induction_on with
  | empty =>
    intro _ s hs
    rw [powerset_zero, count_singleton]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨x, hx⟩ := exists_mem_of_ne_zero h
      symm
      rw [← Finset.mul_prod_erase S _ (hs (mem_toFinset.mpr hx)), count_zero,
          Nat.choose_eq_zero_of_lt (count_pos.mpr hx), Nat.zero_mul]
  | cons a t' ih =>
    intro ht s hs
    have haS : a ∈ S := ht (mem_toFinset.mpr (mem_cons_self a t'))
    have ht' : t'.toFinset ⊆ S := fun x hx => ht (by
      rw [toFinset_cons]; exact Finset.mem_insert_of_mem hx)
    have hQ : ∏ x ∈ S.erase a, ((a ::ₘ t').count x).choose (s.count x)
        = ∏ x ∈ S.erase a, (t'.count x).choose (s.count x) :=
      Finset.prod_congr rfl fun x hx => by
        rw [count_cons_of_ne (Finset.ne_of_mem_erase hx)]
    rw [powerset_cons, count_add, ih ht' s hs,
        ← Finset.mul_prod_erase S (fun x => ((a ::ₘ t').count x).choose (s.count x)) haS,
        ← Finset.mul_prod_erase S (fun x => (t'.count x).choose (s.count x)) haS,
        count_cons_self, hQ]
    by_cases has : a ∈ s
    · have hs' : (s.erase a).toFinset ⊆ S := fun x hx =>
        hs (mem_toFinset.mpr (mem_of_subset (erase_subset a s) (mem_toFinset.mp hx)))
      have hmap : (t'.powerset.map (Multiset.cons a)).count s
          = t'.powerset.count (s.erase a) := by
        conv_lhs => rw [← cons_erase has]
        exact count_map_eq_count' _ _ (fun _ _ h => (cons_inj_right a).mp h) _
      have hR : ∏ x ∈ S.erase a, (t'.count x).choose ((s.erase a).count x)
          = ∏ x ∈ S.erase a, (t'.count x).choose (s.count x) :=
        Finset.prod_congr rfl fun x hx => by
          rw [count_erase_of_ne (Finset.ne_of_mem_erase hx)]
      rw [hmap, ih ht' (s.erase a) hs',
          ← Finset.mul_prod_erase S (fun x => (t'.count x).choose ((s.erase a).count x)) haS,
          count_erase_self, hR, Nat.choose_succ_left _ _ (count_pos.mpr has),
          ← Nat.add_mul, Nat.add_comm ((t'.count a).choose (s.count a))]
    · have hmap : (t'.powerset.map (Multiset.cons a)).count s = 0 :=
        count_eq_zero.mpr fun hmem => by
          obtain ⟨u, -, rfl⟩ := mem_map.mp hmem
          exact has (mem_cons_self a u)
      rw [hmap, count_eq_zero.mpr has]
      simp

/-- Count of a sub-multiset `s ≤ t` among the sub-multisets of `t`: for each distinct
    `x`, choose `s.count x` of the `t.count x` copies. -/
theorem count_powerset_of_le {s t : Multiset α} (h : s ≤ t) :
    t.powerset.count s = ∏ x ∈ t.toFinset, (t.count x).choose (s.count x) :=
  count_powerset_subset t Finset.Subset.rfl s (toFinset_subset.mpr (subset_of_le h))

/-- Hypothesis-free form of `count_powerset_of_le`: over `(s + t).toFinset`, some factor
    `(t.count x).choose (s.count x)` vanishes whenever `s ≰ t`, so both sides are `0`. -/
theorem count_powerset (s t : Multiset α) :
    t.powerset.count s = ∏ x ∈ (s + t).toFinset, (t.count x).choose (s.count x) :=
  count_powerset_subset t (by rw [toFinset_add]; exact Finset.subset_union_right)
    s (by rw [toFinset_add]; exact Finset.subset_union_left)

@[simp] theorem count_zero_powerset (t : Multiset α) : t.powerset.count 0 = 1 := by
  rw [count_powerset_of_le (zero_le t)]
  simp

@[simp] theorem count_powerset_self (t : Multiset α) : t.powerset.count t = 1 := by
  rw [count_powerset_of_le le_rfl]
  simp

end Multiset
