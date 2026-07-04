/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Algebraic identities for `negMulLog`

Mathlib's `Analysis.SpecialFunctions.Log.NegMulLog` develops the analysis of
`x ↦ -x * log x` (continuity, derivatives, convexity) but none of its algebra.
This file supplies the division identity behind the entropy chain rule.
`[UPSTREAM]` candidate for that file.
-/

namespace Real

/-- Splitting `negMulLog` at a quotient: the weighted entropy summand of a
    conditional `x / y` is the joint summand corrected by the marginal log.
    Holds with junk at `x = 0` (both sides vanish). -/
theorem negMulLog_div (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    y * negMulLog (x / y) = negMulLog x + x * log y := by
  by_cases hx : x = 0
  · simp [hx, negMulLog]
  · unfold negMulLog
    rw [log_div hx hy]
    field_simp
    ring

end Real
