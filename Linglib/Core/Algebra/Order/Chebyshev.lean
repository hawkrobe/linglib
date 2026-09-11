import Mathlib.Algebra.Order.Monovary
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Weighted Chebyshev sum inequality

Mathlib's Chebyshev sum inequality (`MonovaryOn.sum_mul_sum_le_card_mul_sum`) counts every
index once. This file weights the indices: under nonnegative weights, two functions that
monovary have a nonnegative weighted covariance, and two that antivary a nonpositive one. With
the weights a probability distribution this is the covariance inequality
`E[f] E[g] ≤ E[f g]` for similarly ordered `f` and `g`.

## Main results

* `two_mul_sum_mul_sum_mul_mul_sub` — twice the covariance defect is the double sum of the
  weighted products of pairwise differences.
* `MonovaryOn.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul`,
  `AntivaryOn.sum_mul_sum_mul_mul_le_sum_mul_mul_sum_mul` — the weighted Chebyshev sum
  inequality on a finset, and `Monovary.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul`,
  `Antivary.sum_mul_sum_mul_mul_le_sum_mul_mul_sum_mul` over a finite type.
-/

open Finset

variable {ι α : Type*}

section CommRing

variable [CommRing α] (w f g : ι → α) (s : Finset ι)

/-- Twice the covariance defect of weighted sums is the weighted double sum of the products of
pairwise differences. -/
theorem two_mul_sum_mul_sum_mul_mul_sub :
    2 * ((∑ i ∈ s, w i) * ∑ i ∈ s, w i * (f i * g i) -
        (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) := by
  have h₁ : (∑ i ∈ s, w i) * ∑ i ∈ s, w i * (f i * g i) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (f j * g j) := by
    rw [sum_mul_sum]; exact sum_congr rfl λ i _ => sum_congr rfl λ j _ => by ring
  have h₁' : (∑ i ∈ s, w i) * ∑ i ∈ s, w i * (f i * g i) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i * g i) := by
    rw [h₁, sum_comm]; exact sum_congr rfl λ i _ => sum_congr rfl λ j _ => by ring
  have h₂ : (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i * g j) := by
    rw [sum_mul_sum]; exact sum_congr rfl λ i _ => sum_congr rfl λ j _ => by ring
  have h₂' : (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (f j * g i) := by
    rw [h₂, sum_comm]; exact sum_congr rfl λ i _ => sum_congr rfl λ j _ => by ring
  calc 2 * ((∑ i ∈ s, w i) * ∑ i ∈ s, w i * (f i * g i) -
        (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i)
      = (∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i * g i)) +
          (∑ i ∈ s, ∑ j ∈ s, w i * w j * (f j * g j)) -
          (∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i * g j)) -
          ∑ i ∈ s, ∑ j ∈ s, w i * w j * (f j * g i) := by
        rw [← h₁', ← h₁, ← h₂, ← h₂']; ring
    _ = _ := by
        simp only [← sum_add_distrib, ← sum_sub_distrib]
        exact sum_congr rfl λ i _ => sum_congr rfl λ j _ => by ring

end CommRing

section OrderedRing

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] {w f g : ι → α} {s : Finset ι}

/-- **Weighted Chebyshev sum inequality**: functions that monovary have nonnegative
covariance under nonnegative weights. -/
theorem MonovaryOn.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul (hfg : MonovaryOn f g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * (f i * g i) := by
  have h : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) := by
    refine sum_nonneg λ i hi => sum_nonneg λ j hj =>
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) ?_
    rcases lt_trichotomy (g i) (g j) with h | h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hfg hi hj h)) (sub_nonpos.2 h.le)
    · rw [h, sub_self, mul_zero]
    · exact mul_nonneg (sub_nonneg.2 (hfg hj hi h)) (sub_nonneg.2 h.le)
  linarith [two_mul_sum_mul_sum_mul_mul_sub w f g s]

/-- **Weighted Chebyshev sum inequality**: functions that antivary have nonpositive
covariance under nonnegative weights. -/
theorem AntivaryOn.sum_mul_sum_mul_mul_le_sum_mul_mul_sum_mul (hfg : AntivaryOn f g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i) * ∑ i ∈ s, w i * (f i * g i) ≤
      (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i := by
  have h : ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) ≤ 0 := by
    refine sum_nonpos λ i hi => sum_nonpos λ j hj =>
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hw i hi) (hw j hj)) ?_
    rcases lt_trichotomy (g i) (g j) with h | h | h
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hfg hi hj h)) (sub_nonpos.2 h.le)
    · rw [h, sub_self, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hfg hj hi h)) (sub_nonneg.2 h.le)
  linarith [two_mul_sum_mul_sum_mul_mul_sub w f g s]

variable [Fintype ι]

theorem Monovary.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul (hfg : Monovary f g)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * f i) * ∑ i, w i * g i ≤ (∑ i, w i) * ∑ i, w i * (f i * g i) :=
  (hfg.monovaryOn _).sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul λ i _ => hw i

theorem Antivary.sum_mul_sum_mul_mul_le_sum_mul_mul_sum_mul (hfg : Antivary f g)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i) * ∑ i, w i * (f i * g i) ≤ (∑ i, w i * f i) * ∑ i, w i * g i :=
  (hfg.antivaryOn _).sum_mul_sum_mul_mul_le_sum_mul_mul_sum_mul λ i _ => hw i

end OrderedRing
