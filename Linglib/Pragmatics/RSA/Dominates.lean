/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Multiset.Bind

/-!
# Inverse-power sums over multisets of naturals

`Multiset.invPowSum α m` sums `n⁻ᵅ` over `m`. `t.Dominates s` says some submultiset of `t`
matches `s` element-for-element with each matched entry of `t` at most its partner in `s`;
that alone forces `s.invPowSum α ≤ t.invPowSum α` simultaneously for every exponent
`0 ≤ α`, and a spare entry of `t` makes the inequality strict.

Domination is equivalent to a Hall-type counting condition — `s` has no more entries below
any threshold than `t` has — which decides it with `card s * (card s + card t)` comparisons.
Certificates therefore close by `decide` for multisets of a few hundred entries, given a
`maxRecDepth` of roughly `8 * card t`.

## Main results

* `Multiset.Dominates.invPowSum_le`, `Multiset.StrictDominates.invPowSum_lt`
* `Multiset.dominates_iff_forall`, `Multiset.dominates_iff_forall_mem`
* `Multiset.invPowSum_prodMul`
-/

open scoped ENNReal

namespace Multiset

variable {α : ℝ} {m s t : Multiset ℕ}

/-! ### Inverse-power sums -/

/-- The sum of `n⁻ᵅ` over `m`. Entries equal to `0` contribute `⊤`. -/
noncomputable def invPowSum (α : ℝ) (m : Multiset ℕ) : ℝ≥0∞ :=
  (m.map fun n : ℕ => (n : ℝ≥0∞)⁻¹ ^ α).sum

@[simp] theorem invPowSum_zero (α : ℝ) : (0 : Multiset ℕ).invPowSum α = 0 := rfl

@[simp]
theorem invPowSum_cons (α : ℝ) (n : ℕ) (m : Multiset ℕ) :
    (n ::ₘ m).invPowSum α = (n : ℝ≥0∞)⁻¹ ^ α + m.invPowSum α := by
  simp [invPowSum]

@[simp]
theorem invPowSum_singleton (α : ℝ) (n : ℕ) :
    ({n} : Multiset ℕ).invPowSum α = (n : ℝ≥0∞)⁻¹ ^ α := by
  simp [invPowSum]

@[simp]
theorem invPowSum_add (α : ℝ) (m₁ m₂ : Multiset ℕ) :
    (m₁ + m₂).invPowSum α = m₁.invPowSum α + m₂.invPowSum α := by
  simp [invPowSum]

@[gcongr]
theorem invPowSum_mono (h : s ≤ t) : s.invPowSum α ≤ t.invPowSum α := by
  obtain ⟨u, rfl⟩ := le_iff_exists_add.1 h
  simp

theorem invPowSum_pos (hα : 0 ≤ α) (hm : m ≠ 0) : 0 < m.invPowSum α := by
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero hm
  obtain ⟨m', rfl⟩ := exists_cons_of_mem hn
  rw [invPowSum_cons]
  exact lt_of_lt_of_le
    (ENNReal.rpow_pos_of_nonneg (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)) hα) le_self_add

theorem invPowSum_ne_top (hα : 0 ≤ α) (hs : 0 ∉ s) : s.invPowSum α ≠ ⊤ := by
  refine ne_top_of_le_ne_top (by simp) (sum_le_card_nsmul _ 1 ?_)
  intro x hx
  obtain ⟨n, hn, rfl⟩ := mem_map.1 hx
  have hn' : (1 : ℝ≥0∞) ≤ n := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h => hs (h ▸ hn)
  simpa using ENNReal.rpow_le_rpow (ENNReal.inv_le_one.2 hn') hα

/-! ### Domination -/

/-- `t.Dominates s`: some submultiset of `t` matches `s` element-for-element, each matched
entry of `t` being at most its partner in `s`. -/
def Dominates (t s : Multiset ℕ) : Prop := ∃ t' ≤ t, Rel (· ≤ ·) t' s

/-- `t` dominates `s` with an entry of `t` left over. -/
def StrictDominates (t s : Multiset ℕ) : Prop := ∃ n ∈ t, (t.erase n).Dominates s

theorem StrictDominates.dominates (h : t.StrictDominates s) : t.Dominates s := by
  obtain ⟨n, -, t', ht', hrel⟩ := h
  exact ⟨t', ht'.trans (erase_le n t), hrel⟩

theorem invPowSum_le_invPowSum_of_rel (hα : 0 ≤ α) (h : Rel (· ≤ ·) t s) :
    s.invPowSum α ≤ t.invPowSum α := by
  induction h with
  | zero => simp
  | cons hab _ ih =>
    rw [invPowSum_cons, invPowSum_cons]
    exact add_le_add (ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.2 (Nat.cast_le.2 hab)) hα) ih

theorem Dominates.invPowSum_le (h : t.Dominates s) (hα : 0 ≤ α) :
    s.invPowSum α ≤ t.invPowSum α := by
  obtain ⟨t', ht', hrel⟩ := h
  exact (invPowSum_le_invPowSum_of_rel hα hrel).trans (invPowSum_mono ht')

theorem StrictDominates.invPowSum_lt (h : t.StrictDominates s) (hα : 0 ≤ α) (hs : 0 ∉ s) :
    s.invPowSum α < t.invPowSum α := by
  obtain ⟨n, hn, hdom⟩ := h
  have hpos : 0 < (n : ℝ≥0∞)⁻¹ ^ α := by
    simpa using invPowSum_pos (m := {n}) hα (by simp)
  rw [← cons_erase hn, invPowSum_cons, add_comm]
  rcases eq_or_ne ((t.erase n).invPowSum α) ⊤ with h₁ | h₁
  · exact h₁ ▸ (invPowSum_ne_top hα hs).lt_top
  · exact (hdom.invPowSum_le hα).trans_lt (ENNReal.lt_add_right h₁ hpos.ne')

/-! ### The Hall criterion -/

private theorem exists_min (hs : s ≠ 0) : ∃ x ∈ s, ∀ y ∈ s, x ≤ y :=
  let h := exists_mem_of_ne_zero hs
  ⟨Nat.find h, Nat.find_spec h, fun _ hy => Nat.find_min' h hy⟩

theorem card_filter_le_card_filter_of_rel (h : Rel (· ≤ ·) t s) (k : ℕ) :
    card (s.filter (· ≤ k)) ≤ card (t.filter (· ≤ k)) := by
  induction h with
  | zero => simp
  | @cons a b as bs hab _ ih =>
    by_cases hb : b ≤ k
    · have h₁ : (b ::ₘ bs).filter (· ≤ k) = b ::ₘ bs.filter (· ≤ k) := filter_cons_of_pos _ hb
      have h₂ : (a ::ₘ as).filter (· ≤ k) = a ::ₘ as.filter (· ≤ k) :=
        filter_cons_of_pos _ (hab.trans hb)
      simpa [h₁, h₂] using ih
    · have h₁ : (b ::ₘ bs).filter (· ≤ k) = bs.filter (· ≤ k) := filter_cons_of_neg _ hb
      exact h₁ ▸ ih.trans (card_le_card (filter_le_filter _ (le_cons_self _ _)))

theorem Dominates.card_filter_le (h : t.Dominates s) (k : ℕ) :
    card (s.filter (· ≤ k)) ≤ card (t.filter (· ≤ k)) := by
  obtain ⟨t', ht', hrel⟩ := h
  exact (card_filter_le_card_filter_of_rel hrel k).trans (card_le_card (filter_le_filter _ ht'))

/-- Greedy matching: pair the least entry of `s` with any entry of `t` below it, which the
counting condition supplies and which leaves the condition intact for what remains. -/
theorem dominates_of_forall_mem
    (h : ∀ k ∈ s, card (s.filter (· ≤ k)) ≤ card (t.filter (· ≤ k))) : t.Dominates s := by
  induction s using Multiset.strongInductionOn generalizing t with
  | _ s ih =>
  rcases eq_or_ne s 0 with rfl | hs
  · exact ⟨0, zero_le _, Rel.zero⟩
  obtain ⟨x, hx, hmin⟩ := exists_min hs
  have hxx : x ∈ s.filter (· ≤ x) := mem_filter.2 ⟨hx, le_rfl⟩
  obtain ⟨y, hy⟩ := card_pos_iff_exists_mem.1 <|
    lt_of_lt_of_le (card_pos_iff_exists_mem.2 ⟨x, hxx⟩) (h x hx)
  obtain ⟨hyt, hyx⟩ := mem_filter.1 hy
  obtain ⟨t', ht', hrel⟩ := @ih (s.erase x) (erase_lt.2 hx) (t.erase y) fun k hk => by
    have hxk : x ≤ k := hmin k (mem_of_mem_erase hk)
    have hsk : s.filter (· ≤ k) = x ::ₘ (s.erase x).filter (· ≤ k) := by
      conv_lhs => rw [← cons_erase hx]
      exact filter_cons_of_pos _ hxk
    have htk : t.filter (· ≤ k) = y ::ₘ (t.erase y).filter (· ≤ k) := by
      conv_lhs => rw [← cons_erase hyt]
      exact filter_cons_of_pos _ (hyx.trans hxk)
    have := h k (mem_of_mem_erase hk)
    rw [hsk, htk, card_cons, card_cons] at this
    omega
  exact ⟨y ::ₘ t', cons_erase hyt ▸ cons_le_cons _ ht', cons_erase hx ▸ Rel.cons hyx hrel⟩

theorem dominates_iff_forall_mem :
    t.Dominates s ↔ ∀ k ∈ s, card (s.filter (· ≤ k)) ≤ card (t.filter (· ≤ k)) :=
  ⟨fun h k _ => h.card_filter_le k, dominates_of_forall_mem⟩

theorem dominates_iff_forall :
    t.Dominates s ↔ ∀ k, card (s.filter (· ≤ k)) ≤ card (t.filter (· ≤ k)) :=
  ⟨Dominates.card_filter_le, fun h => dominates_of_forall_mem fun k _ => h k⟩

instance decidableDominates : DecidableRel Dominates :=
  fun _ _ => decidable_of_iff _ dominates_iff_forall_mem.symm

instance decidableStrictDominates : DecidableRel StrictDominates :=
  fun _ _ => Multiset.decidableExistsMultiset

/-! ### Pairwise products -/

/-- The multiset of pairwise products of `s` and `t`. -/
def prodMul (s t : Multiset ℕ) : Multiset ℕ := (s ×ˢ t).map fun p => p.1 * p.2

@[simp] theorem zero_prodMul (t : Multiset ℕ) : prodMul 0 t = 0 := rfl

@[simp]
theorem cons_prodMul (n : ℕ) (s t : Multiset ℕ) :
    prodMul (n ::ₘ s) t = t.map (n * ·) + prodMul s t := by
  simp [prodMul]

private theorem natCast_inv_rpow_mul (hα : 0 ≤ α) (a b : ℕ) :
    ((a * b : ℕ) : ℝ≥0∞)⁻¹ ^ α = (a : ℝ≥0∞)⁻¹ ^ α * (b : ℝ≥0∞)⁻¹ ^ α := by
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top b))
    (Or.inl (ENNReal.natCast_ne_top a)), ENNReal.mul_rpow_of_nonneg _ _ hα]

theorem invPowSum_map_mul (hα : 0 ≤ α) (n : ℕ) (t : Multiset ℕ) :
    (t.map (n * ·)).invPowSum α = (n : ℝ≥0∞)⁻¹ ^ α * t.invPowSum α := by
  simp only [invPowSum, map_map, Function.comp_def, natCast_inv_rpow_mul hα, sum_map_mul_left]

theorem invPowSum_prodMul (hα : 0 ≤ α) (s t : Multiset ℕ) :
    (prodMul s t).invPowSum α = s.invPowSum α * t.invPowSum α := by
  induction s using Multiset.induction with
  | empty => simp
  | cons n s ih =>
    rw [cons_prodMul, invPowSum_add, ih, invPowSum_map_mul hα, invPowSum_cons, add_mul]

/-! ### Certificates -/

example : Dominates {1, 2, 3} {2, 3} := by decide

example : ¬ Dominates {2, 3} {1, 2} := by decide

example : StrictDominates {1, 1, 5} {2, 7} := by decide

example : ¬ StrictDominates {1, 2} {1, 2} := by decide

theorem zero_notMem_prodMul (hs : 0 ∉ s) (ht : 0 ∉ t) : 0 ∉ prodMul s t := by
  simp only [prodMul, Multiset.mem_map, not_exists, not_and]
  intro p hp h0
  rcases Nat.mul_eq_zero.mp h0 with h | h
  · exact hs (h ▸ (Multiset.mem_product.mp hp).1)
  · exact ht (h ▸ (Multiset.mem_product.mp hp).2)

set_option maxRecDepth 2000 in
example : (prodMul {1, 2, 3, 4} {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}).StrictDominates
    {2, 4, 6, 8, 10} := by decide

set_option maxRecDepth 2000 in
example : ¬ (prodMul {2, 3} {5, 7, 11, 13, 17}).Dominates {1, 4} := by decide

end Multiset
