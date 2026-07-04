/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Algebraic identities for `negMulLog`

Mathlib's `Analysis.SpecialFunctions.Log.NegMulLog` has the product identity
`Real.negMulLog_mul` but neither its inverse nor quotient companions
(cf. `Real.log_inv`/`Real.log_div` beside `Real.log_mul`). This file completes
the family; the division identity is the pointwise step of the entropy chain
rule. `[UPSTREAM]` candidate for that file.
-/

namespace Real

/-- `negMulLog` at an inverse. Holds with junk at `y = 0` (both sides vanish). -/
theorem negMulLog_inv (y : ℝ) : negMulLog y⁻¹ = y⁻¹ * log y := by
  simp [negMulLog, log_inv]

/-- The quotient rule for `negMulLog`, weighted by the denominator: the
    companion of `negMulLog_mul`. Holds with junk at `x = 0` (both sides
    vanish). -/
theorem negMulLog_div (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    y * negMulLog (x / y) = negMulLog x + x * log y := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · simp only [negMulLog, log_div hx hy]
    field_simp
    ring

end Real
