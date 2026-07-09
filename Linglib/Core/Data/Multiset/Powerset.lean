/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel

/-!
# Decomposing and counting `Multiset.powerset`

Structural decompositions of `Multiset.powerset` (mathlib has only the `zero`/`cons`
forms), and the multiplicity of `s` in `t.powerset` as a product of binomial
coefficients: a sub-multiset picks `s.count x` of the `t.count x` copies of each
distinct `x`. (This product of binomials is not `Nat.multinomial`, which is the
quotient `(∑ᵢ kᵢ)! / ∏ᵢ kᵢ!`.)

## Main results

* `Multiset.powerset_add`: `(F + G).powerset` as a bind/map product of the summands'
  powersets — the `+` analogue of `Multiset.powerset_cons`.
* `Multiset.powerset_powerset_pair_swap`: the two iteration orders over nested
  sub-multiset pairs enumerate the same multiset of pairs.
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

-/

namespace Multiset

variable {α : Type*}

/-- `powerset` of a sum, as a bind/map product over the summands' powersets: each
    sub-multiset of `F + G` splits (with multiplicity) into a sub-multiset of `F` plus a
    sub-multiset of `G`. The `+` analogue of `powerset_cons`. -/
theorem powerset_add (F G : Multiset α) :
    (F + G).powerset =
      F.powerset.bind (fun F₁ => G.powerset.map (fun G₁ => F₁ + G₁)) := by
  induction F using Multiset.induction_on with
  | empty =>
    simp [powerset_zero, singleton_bind]
  | cons a s ih =>
    rw [cons_add, powerset_cons, powerset_cons,
        add_bind]
    have h₂ : map (cons a) ((s + G).powerset) =
              (map (cons a) s.powerset).bind
                (fun F₁ => G.powerset.map (fun G₁ => F₁ + G₁)) := by
      rw [bind_map, ih, map_bind]
      apply bind_congr
      intros s₁ _
      rw [map_map]
      apply map_congr rfl
      intros G₁ _
      show cons a (s₁ + G₁) = cons a s₁ + G₁
      rw [cons_add]
    rw [h₂, ih]

variable [DecidableEq α]

/-- Nested-powerset reparameterization: iterating `F₁ ⊆ F` then `A ⊆ F₁` enumerates the
    same multiset of pairs as iterating `A ⊆ F` then `B ⊆ F - A`, via the bijection
    `(F₁, A) ↦ (A, F₁ - A)`. -/
theorem powerset_powerset_pair_swap (F : Multiset α) :
    F.powerset.bind (fun F₁ : Multiset α =>
      F₁.powerset.map (fun A : Multiset α => (A, F₁ - A))) =
    F.powerset.bind (fun A : Multiset α =>
      (F - A).powerset.map (fun B : Multiset α => (A, B))) := by
  induction F using Multiset.induction with
  | empty =>
    rw [powerset_zero]
    simp [singleton_bind]
  | cons a s ih =>
    rw [powerset_cons, add_bind, add_bind]
    rw [bind_map]
    -- Split LHS into 3 parts via inner powerset_cons:
    -- LHS = s.powerset.bind (fun F₁' => F₁'.powerset.map (fun A => (A, F₁' - A))) [a ∉ F₁ case]
    --     + s.powerset.bind (fun F₁' => (a ::ₘ F₁').powerset.map (...)) [a ∈ F₁ case]
    -- Inner (a ∈ F₁) splits via powerset_cons of (a ::ₘ F₁'):
    --   (a ::ₘ F₁').powerset = F₁'.powerset + F₁'.powerset.map (cons a)
    --   For A ∈ F₁'.powerset (a ∉ A): (a ::ₘ F₁') - A = a ::ₘ (F₁' - A)
    --   For A = a ::ₘ A' (a ∈ A): (a ::ₘ F₁') - A = F₁' - A'
    have h_inner_split : ∀ F₁' : Multiset α,
        (a ::ₘ F₁').powerset.map (fun A => (A, (a ::ₘ F₁') - A)) =
        F₁'.powerset.map (fun A => (A, a ::ₘ (F₁' - A))) +
        F₁'.powerset.map (fun A' => (a ::ₘ A', F₁' - A')) := by
      intro F₁'
      rw [powerset_cons, map_add]
      congr 1
      · refine map_congr rfl fun A hA => ?_
        congr 1
        exact cons_sub_of_le a (mem_powerset.mp hA)
      · rw [map_map]
        refine map_congr rfl fun A' _ => ?_
        show (cons a A', (a ::ₘ F₁') - (a ::ₘ A')) = (a ::ₘ A', F₁' - A')
        rw [sub_cons, erase_cons_head]
    -- Apply h_inner_split inside the second LHS bind
    rw [show (s.powerset.bind fun F₁' => (a ::ₘ F₁').powerset.map (fun A => (A, (a ::ₘ F₁') - A))) =
            (s.powerset.bind fun F₁' =>
              F₁'.powerset.map (fun A => (A, a ::ₘ (F₁' - A))) +
              F₁'.powerset.map (fun A' => (a ::ₘ A', F₁' - A'))) from
          bind_congr fun F₁' _ => h_inner_split F₁']
    rw [bind_add]
    -- Rewrite each LHS piece using LHS_for_s.map (fun p => ...)
    have h_lhs_part2 : (s.powerset.bind fun F₁' =>
                          F₁'.powerset.map (fun A => (A, a ::ₘ (F₁' - A)))) =
        (s.powerset.bind fun F₁' =>
          F₁'.powerset.map (fun A => (A, F₁' - A))).map (fun p => (p.1, a ::ₘ p.2)) := by
      rw [map_bind]
      refine bind_congr fun F₁' _ => ?_
      rw [map_map]; rfl
    have h_lhs_part3 : (s.powerset.bind fun F₁' =>
                          F₁'.powerset.map (fun A' => (a ::ₘ A', F₁' - A'))) =
        (s.powerset.bind fun F₁' =>
          F₁'.powerset.map (fun A' => (A', F₁' - A'))).map (fun p => (a ::ₘ p.1, p.2)) := by
      rw [map_bind]
      refine bind_congr fun F₁' _ => ?_
      rw [map_map]; rfl
    rw [h_lhs_part2, h_lhs_part3, ih]
    -- Now LHS = RHS_for_s + (RHS_for_s).map (p ↦ (p.1, a ::ₘ p.2)) + (RHS_for_s).map (p ↦ (a ::ₘ p.1, p.2))
    -- Compute RHS for (a ::ₘ s) similarly.
    -- RHS = ((a ::ₘ s).powerset.bind fun A => ((a ::ₘ s) - A).powerset.map (fun B => (A, B)))
    --     = s.powerset.bind ... [a ∉ A case]
    --       + (s.powerset.map (cons a)).bind ... [a ∈ A case]
    rw [bind_map]
    -- For the "a ∉ A" piece: A ⊆ s, so (a ::ₘ s) - A = a ::ₘ (s - A).
    have h_a_notin_A : ∀ A : Multiset α, A ∈ s.powerset →
        ((a ::ₘ s) - A).powerset.map (fun B => (A, B)) =
        (s - A).powerset.map (fun B => (A, B)) +
        (s - A).powerset.map (fun B' => (A, a ::ₘ B')) := by
      intros A hA
      have hA_le : A ≤ s := mem_powerset.mp hA
      rw [show (a ::ₘ s) - A = a ::ₘ (s - A) from cons_sub_of_le a hA_le]
      rw [powerset_cons, map_add]
      congr 1
      rw [map_map]; rfl
    -- Apply for the "a ∉ A" branch
    rw [show (s.powerset.bind fun A => ((a ::ₘ s) - A).powerset.map (fun B => (A, B))) =
            (s.powerset.bind fun A =>
              (s - A).powerset.map (fun B => (A, B)) +
              (s - A).powerset.map (fun B' => (A, a ::ₘ B'))) from
          bind_congr h_a_notin_A]
    rw [bind_add]
    -- For the "a ∈ A" branch: A = cons a A', A' ⊆ s, (a ::ₘ s) - (a ::ₘ A') = s - A'.
    have h_rhs_part3 : (s.powerset.bind fun A' =>
                          ((a ::ₘ s) - (a ::ₘ A')).powerset.map (fun B => (a ::ₘ A', B))) =
        (s.powerset.bind fun A' => (s - A').powerset.map (fun B => (A', B))).map
          (fun p => (a ::ₘ p.1, p.2)) := by
      rw [map_bind]
      refine bind_congr fun A' _ => ?_
      rw [show (a ::ₘ s) - (a ::ₘ A') = s - A' from by
            rw [sub_cons, erase_cons_head]]
      rw [map_map]; rfl
    rw [h_rhs_part3]
    -- The "a ∈ A, a ∉ B" piece via map identity
    have h_rhs_part2 : (s.powerset.bind fun A => (s - A).powerset.map (fun B' => (A, a ::ₘ B'))) =
        (s.powerset.bind fun A => (s - A).powerset.map (fun B => (A, B))).map
          (fun p => (p.1, a ::ₘ p.2)) := by
      rw [map_bind]
      refine bind_congr fun A _ => ?_
      rw [map_map]; rfl
    rw [h_rhs_part2]
    -- Both sides are now base + second-slot lift + first-slot lift; `abel` reorders.
    abel

/-- Workhorse for `count_powerset_of_le` and `count_powerset`: the product may be taken
    over any fixed `Finset` containing the supports of both multisets. -/
private theorem count_powerset_subset {S : Finset α} {t s : Multiset α} (ht : t.toFinset ⊆ S)
    (hs : s.toFinset ⊆ S) : t.powerset.count s = ∏ x ∈ S, (t.count x).choose (s.count x) := by
  induction t using Multiset.induction_on generalizing s hs with
  | empty =>
    rw [powerset_zero, count_singleton]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨x, hx⟩ := exists_mem_of_ne_zero h
      symm
      rw [← Finset.mul_prod_erase S _ (hs (mem_toFinset.mpr hx)), count_zero,
          Nat.choose_eq_zero_of_lt (count_pos.mpr hx), Nat.zero_mul]
  | cons a t' ih =>
    have haS : a ∈ S := ht (mem_toFinset.mpr (mem_cons_self a t'))
    have ht' : t'.toFinset ⊆ S := (toFinset_subset.mpr (subset_cons t' a)).trans ht
    have hQ : ∏ x ∈ S.erase a, ((a ::ₘ t').count x).choose (s.count x)
        = ∏ x ∈ S.erase a, (t'.count x).choose (s.count x) :=
      Finset.prod_congr rfl fun x hx => by
        rw [count_cons_of_ne (Finset.ne_of_mem_erase hx)]
    rw [powerset_cons, count_add, ih ht' hs,
        ← Finset.mul_prod_erase S (fun x => ((a ::ₘ t').count x).choose (s.count x)) haS,
        ← Finset.mul_prod_erase S (fun x => (t'.count x).choose (s.count x)) haS,
        count_cons_self, hQ]
    by_cases has : a ∈ s
    · have hs' : (s.erase a).toFinset ⊆ S := (toFinset_subset.mpr (erase_subset a s)).trans hs
      have hmap : (t'.powerset.map (Multiset.cons a)).count s
          = t'.powerset.count (s.erase a) := by
        conv_lhs => rw [← cons_erase has]
        exact count_map_eq_count' _ _ (fun _ _ h => (cons_inj_right a).mp h) _
      have hR : ∏ x ∈ S.erase a, (t'.count x).choose ((s.erase a).count x)
          = ∏ x ∈ S.erase a, (t'.count x).choose (s.count x) :=
        Finset.prod_congr rfl fun x hx => by
          rw [count_erase_of_ne (Finset.ne_of_mem_erase hx)]
      rw [hmap, ih ht' hs',
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
  count_powerset_subset Finset.Subset.rfl (toFinset_subset.mpr (subset_of_le h))

/-- Hypothesis-free form of `count_powerset_of_le`: over `(s + t).toFinset`, some factor
    `(t.count x).choose (s.count x)` vanishes whenever `s ≰ t`, so both sides are `0`. -/
theorem count_powerset (s t : Multiset α) :
    t.powerset.count s = ∏ x ∈ (s + t).toFinset, (t.count x).choose (s.count x) :=
  count_powerset_subset (by rw [toFinset_add]; exact Finset.subset_union_right)
    (by rw [toFinset_add]; exact Finset.subset_union_left)

/-- A multiset that is not below `t` does not occur in `t.powerset`. -/
theorem count_powerset_eq_zero {s t : Multiset α} (h : ¬s ≤ t) : t.powerset.count s = 0 :=
  count_eq_zero.mpr (mt mem_powerset.mp h)

@[simp] theorem count_zero_powerset (t : Multiset α) : t.powerset.count 0 = 1 := by
  rw [count_powerset_of_le (zero_le t)]
  simp

@[simp] theorem count_powerset_self (t : Multiset α) : t.powerset.count t = 1 := by
  rw [count_powerset_of_le le_rfl]
  simp

end Multiset
