/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Weighted products of extended nonnegative reals

A weighted geometric mean `∏ i ∈ s, z i ^ w i` with nonnegative real weights collapses to a single
power when the `z i` agree wherever the weight is nonzero.

`[UPSTREAM]` candidate for `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`, beside
`ENNReal.prod_rpow_of_nonneg`.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

variable {ι : Type*} {s : Finset ι} {w : ι → ℝ}

theorem rpow_sum_of_nonneg (x : ℝ≥0∞) (hw : ∀ i ∈ s, 0 ≤ w i) :
    x ^ ∑ i ∈ s, w i = ∏ i ∈ s, x ^ w i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi,
      rpow_add_of_nonneg _ _ (hw i (Finset.mem_insert_self i s))
        (Finset.sum_nonneg fun j hj ↦ hw j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hw j (Finset.mem_insert_of_mem hj)]

/-- A weighted geometric mean of values that agree wherever the weight is nonzero is their common
value to the power of the total weight. -/
theorem prod_rpow_of_forall_eq {z : ι → ℝ≥0∞} {c : ℝ≥0∞} (hw : ∀ i ∈ s, 0 ≤ w i)
    (h : ∀ i ∈ s, w i ≠ 0 → z i = c) : ∏ i ∈ s, z i ^ w i = c ^ ∑ i ∈ s, w i := by
  rw [rpow_sum_of_nonneg c hw]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rcases eq_or_ne (w i) 0 with h0 | h0
  · rw [h0, rpow_zero, rpow_zero]
  · rw [h i hi h0]

end ENNReal
