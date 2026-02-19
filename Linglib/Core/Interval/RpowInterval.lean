import Linglib.Core.Interval.QInterval
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# RpowInterval — Exact Rational Power for Nonneg Intervals

For nonneg intervals with natural exponents, `rpow(x, n) = x^n` is exact
ℚ arithmetic. This covers the dominant case in RSA: belief-based utility
uses `rpow(L0(w|u), α)` where α is typically 1 (or another natural number).

## Key property

Zero approximation error: the entire interval computation is exact when
α ∈ ℕ and the base data is rational.
-/

namespace Linglib.Interval

open Linglib.Interval.QInterval

-- ============================================================================
-- rpow for natural exponents
-- ============================================================================

/-- Exact rational power for nonneg intervals: [lo^n, hi^n].
    Requires 0 ≤ lo (so the interval is nonneg) and n : ℕ.
    Exact — no approximation error. -/
def rpowNat (a : QInterval) (n : ℕ) (ha : 0 ≤ a.lo) : QInterval where
  lo := a.lo ^ n
  hi := a.hi ^ n
  valid := pow_le_pow_left₀ ha a.valid n

theorem rpowNat_containsReal {a : QInterval} {x : ℝ} {n : ℕ}
    (ha : 0 ≤ a.lo) (hx : a.containsReal x) :
    (rpowNat a n ha).containsReal (x ^ (↑n : ℝ)) := by
  have hx_nn : (0 : ℝ) ≤ x := le_trans (by exact_mod_cast ha) hx.1
  rw [Real.rpow_natCast]
  simp only [rpowNat, containsReal]
  push_cast
  constructor
  · exact pow_le_pow_left₀ (by exact_mod_cast ha) hx.1 n
  · exact pow_le_pow_left₀ hx_nn hx.2 n

-- ============================================================================
-- Special cases
-- ============================================================================

/-- Interval for rpow(x, 0) = [1, 1]. -/
def rpowZero : QInterval := QInterval.exact 1

theorem rpowZero_containsReal (x : ℝ) :
    rpowZero.containsReal (x ^ (0 : ℝ)) := by
  simp only [rpowZero, Real.rpow_zero]
  exact_mod_cast QInterval.exact_containsReal 1

/-- For rpow(x, 1) with x ∈ interval a, the result is just a. -/
theorem rpowOne_containsReal {a : QInterval} {x : ℝ}
    (_ha : 0 ≤ a.lo) (hx : a.containsReal x) :
    a.containsReal (x ^ (1 : ℝ)) := by
  rw [Real.rpow_one]
  exact hx

end Linglib.Interval
