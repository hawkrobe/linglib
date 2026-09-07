import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# The logistic function as a two-term softmax

The share of one of two exponentials in their sum is the logistic function of the difference
of their exponents.
-/

namespace Real

/-- The share of `exp x` in `exp x + exp y` is the logistic function of `x - y`. -/
theorem exp_div_add_exp_eq_sigmoid (x y : ℝ) : exp x / (exp x + exp y) = sigmoid (x - y) := by
  have hx := exp_pos x
  have hy := exp_pos y
  rw [sigmoid_def, neg_sub, exp_sub]
  field_simp

end Real
