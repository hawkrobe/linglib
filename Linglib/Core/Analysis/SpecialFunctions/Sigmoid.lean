import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# The logistic function as a two-term softmax

The share of one of two exponentials in their sum is the logistic function of the difference
of their exponents, and the logistic function inverts the log-odds.
-/

namespace Real

/-- The share of `exp x` in `exp x + exp y` is the logistic function of `x - y`. -/
theorem exp_div_add_exp_eq_sigmoid (x y : ℝ) : exp x / (exp x + exp y) = sigmoid (x - y) := by
  have hx := exp_pos x
  have hy := exp_pos y
  rw [sigmoid_def, neg_sub, exp_sub]
  field_simp

/-- The logistic function at the log-odds of a level in `(0, 1)` is that level. -/
theorem sigmoid_log_div_one_sub {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    sigmoid (log (t / (1 - t))) = t := by
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  rw [sigmoid_def, ← log_inv, exp_log (inv_pos.2 (div_pos ht0 h1t)), inv_div]
  field_simp
  ring

end Real
