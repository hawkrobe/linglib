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

namespace Interval

open Interval.QInterval

-- ============================================================================
-- rpow for natural exponents
-- ============================================================================

/-- Exact rational power for nonneg intervals: [lo^n, hi^n].
    Requires 0 ≤ lo (so the interval is nonneg) and n : ℕ.
    Exact — no approximation error.

    Thin wrapper around `QInterval.rpowNat`; kept under `Interval` namespace so
    rpow-shaped consumers (RSA reflection backend) call it directly. -/
def rpowNat (a : QInterval) (n : ℕ) (ha : 0 ≤ a.lo) : QInterval :=
  a.rpowNat n ha

theorem rpowNat_containsReal {a : QInterval} {x : ℝ} {n : ℕ}
    (ha : 0 ≤ a.lo) (hx : a.containsReal x) :
    (rpowNat a n ha).containsReal (x ^ (↑n : ℝ)) := by
  rw [Real.rpow_natCast]
  exact QInterval.powNat_containsReal n ha hx

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

end Interval
