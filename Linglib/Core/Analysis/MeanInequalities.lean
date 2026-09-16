import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weighted geometric means of two numbers

The weighted geometric mean `p₁ ^ w₁ * p₂ ^ w₂` of two non-negative reals, with
`w₁ + w₂ = 1`, lies between `min p₁ p₂` and `max p₁ p₂`, strictly when the two
numbers differ and both weights are positive. These are the multiplicative
counterparts of `Convex.min_le_combo` and `Convex.combo_le_max`, and companions
of `Real.geom_mean_le_arith_mean2_weighted` in
`Mathlib/Analysis/MeanInequalities.lean`. `[UPSTREAM]` candidate.

## Main results

* `Real.min_le_geom_mean2_weighted`, `Real.geom_mean2_weighted_le_max` — the
  weighted geometric mean of two numbers lies between them.
* `Real.min_lt_geom_mean2_weighted`, `Real.geom_mean2_weighted_lt_max` — strictly
  so for distinct numbers and positive weights.
-/

namespace Real

variable {w₁ w₂ p₁ p₂ : ℝ}

private theorem rpow_mul_rpow_self (hp : 0 ≤ p₁) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₁ ^ w₂ = p₁ := by
  rw [← rpow_add' hp (hw.trans_ne one_ne_zero), hw, rpow_one]

theorem min_le_geom_mean2_weighted (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hp₁ : 0 ≤ p₁)
    (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) : min p₁ p₂ ≤ p₁ ^ w₁ * p₂ ^ w₂ :=
  calc min p₁ p₂ = min p₁ p₂ ^ w₁ * min p₁ p₂ ^ w₂ :=
        (rpow_mul_rpow_self (le_min hp₁ hp₂) hw).symm
    _ ≤ p₁ ^ w₁ * p₂ ^ w₂ := by gcongr <;> simp

theorem geom_mean2_weighted_le_max (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hp₁ : 0 ≤ p₁)
    (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) : p₁ ^ w₁ * p₂ ^ w₂ ≤ max p₁ p₂ :=
  calc p₁ ^ w₁ * p₂ ^ w₂ ≤ max p₁ p₂ ^ w₁ * max p₁ p₂ ^ w₂ := by gcongr <;> simp
    _ = max p₁ p₂ := rpow_mul_rpow_self (le_max_of_le_left hp₁) hw

theorem geom_mean2_weighted_lt_max (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hp₁ : 0 ≤ p₁)
    (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) (hne : p₁ ≠ p₂) :
    p₁ ^ w₁ * p₂ ^ w₂ < max p₁ p₂ := by
  wlog h : p₁ < p₂ generalizing w₁ w₂ p₁ p₂
  · rw [mul_comm, max_comm]
    exact this hw₂ hw₁ hp₂ hp₁ ((add_comm _ _).trans hw) hne.symm (hne.lt_of_le' (not_lt.1 h))
  have hp₂' : 0 < p₂ := hp₁.trans_lt h
  rw [max_eq_right h.le]
  calc p₁ ^ w₁ * p₂ ^ w₂ < p₂ ^ w₁ * p₂ ^ w₂ := by gcongr
    _ = p₂ := rpow_mul_rpow_self hp₂ hw

theorem min_lt_geom_mean2_weighted (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hp₁ : 0 < p₁)
    (hp₂ : 0 < p₂) (hw : w₁ + w₂ = 1) (hne : p₁ ≠ p₂) :
    min p₁ p₂ < p₁ ^ w₁ * p₂ ^ w₂ := by
  wlog h : p₁ < p₂ generalizing w₁ w₂ p₁ p₂
  · rw [mul_comm, min_comm]
    exact this hw₂ hw₁ hp₂ hp₁ ((add_comm _ _).trans hw) hne.symm (hne.lt_of_le' (not_lt.1 h))
  rw [min_eq_left h.le]
  calc p₁ = p₁ ^ w₁ * p₁ ^ w₂ := (rpow_mul_rpow_self hp₁.le hw).symm
    _ < p₁ ^ w₁ * p₂ ^ w₂ := by gcongr

end Real
