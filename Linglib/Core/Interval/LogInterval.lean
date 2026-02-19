import Linglib.Core.Interval.PadeExp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

/-!
# LogInterval — Interval Arithmetic for Real.log via Bisection

Computes `log(q)` for rational `q > 0` by bisecting against `expPoint`:
find `lo`, `hi` such that `exp(lo) ≤ q ≤ exp(hi)`, then refine by bisection.

## Strategy

1. Initial bracket: `log(q) ∈ [-(q.den), q.num.natAbs]`
   (since `exp(-d) ≤ 1/d ≤ q` and `exp(p) ≥ 1 + p ≥ p ≥ q` where `q = p/d`)
2. Bisect 50 iterations: check `exp(mid)` vs `q` using `expPoint` bounds
3. Return `[lo, hi]` as `QInterval` containing `Real.log q`

## Precision

50 bisection iterations on a bracket of width `W` give precision `W/2^50 ≈ W × 10⁻¹⁵`.
For typical values (`q ∈ [10⁻⁴, 1]`, `W ≤ 10⁴`), precision ≈ `10⁻¹¹`.
-/

namespace Linglib.Interval

open Linglib.Interval.QInterval

-- ============================================================================
-- Bisection
-- ============================================================================

/-- Bisection loop: narrow `[lo, hi]` such that `exp(lo) ≤ q ≤ exp(hi)`.

    Three-way check at the midpoint for soundness:
    - If `expPoint(mid).hi ≤ q`: `exp(mid) ≤ q`, so `mid ≤ log(q)` → narrow to `[mid, hi]`
    - If `q ≤ expPoint(mid).lo`: `q ≤ exp(mid)`, so `log(q) ≤ mid` → narrow to `[lo, mid]`
    - Otherwise: Padé interval straddles `q`, don't narrow (decrement `n` only) -/
private def logBisectCore (q : ℚ) :
    (lo hi : ℚ) → lo ≤ hi → ℕ → { p : ℚ × ℚ // p.1 ≤ p.2 }
  | lo, hi, h, 0 => ⟨(lo, hi), h⟩
  | lo, hi, h, n + 1 =>
    let mid := (lo + hi) / 2
    have hmid : mid = (lo + hi) / 2 := rfl
    if (expPoint mid).hi ≤ q then
      logBisectCore q mid hi (by linarith [hmid]) n
    else if q ≤ (expPoint mid).lo then
      logBisectCore q lo mid (by linarith [hmid]) n
    else
      logBisectCore q lo hi h n

/-- Number of bisection iterations. -/
def logIterations : ℕ := 50

-- ============================================================================
-- logPoint
-- ============================================================================

/-- Point interval containing `log(q)` for rational `q > 0`.

    Initial bracket: `[-(q.den), q.num.natAbs]`.
    - Lower: `exp(-d) ≤ 1/d ≤ p/d = q` (since `p ≥ 1`, `d ≥ 1`)
    - Upper: `exp(p) ≥ 1 + p ≥ p ≥ p/d = q`

    50 bisection iterations narrow this to precision `bracket_width / 2^50`. -/
def logPoint (q : ℚ) (_hq : 0 < q) : QInterval :=
  -- Special case: log(1) = 0 exactly. This is the only rational q with
  -- log(q) ∈ ℚ (by Lindemann-Weierstrass), so the bisection stalls here
  -- because exp(0) = 1 = q and the Padé interval straddles the target.
  if q = 1 then QInterval.exact 0
  else
  let lo₀ : ℚ := -(↑q.den : ℚ)
  let hi₀ : ℚ := ↑q.num.natAbs
  have hle₀ : lo₀ ≤ hi₀ := by
    show -(↑q.den : ℚ) ≤ ↑q.num.natAbs
    have : (0 : ℚ) ≤ ↑q.den := Nat.cast_nonneg _
    have : (0 : ℚ) ≤ ↑q.num.natAbs := Nat.cast_nonneg _
    linarith
  let ⟨(lo, hi), hle⟩ := logBisectCore q lo₀ hi₀ hle₀ logIterations
  ⟨lo, hi, hle⟩

/-- Containment theorem for logPoint.

    Proof sketch: the bisection invariant is `exp(lo) ≤ q ≤ exp(hi)`, which
    by monotonicity of log gives `lo ≤ log(q) ≤ hi`. Each bisection step
    preserves the invariant via the `expPoint` bound check.

    TODO: prove from the bisection invariant + `expPoint_containsReal`. -/
axiom logPoint_containsReal (q : ℚ) (hq : 0 < q) :
    (logPoint q hq).containsReal (Real.log (↑q : ℝ))

-- ============================================================================
-- logInterval
-- ============================================================================

/-- Interval containing `log(x)` for `x` in a positive rational interval `I`.

    Uses monotonicity of log: for `x ∈ [lo, hi]` with `lo > 0`,
      `log(lo) ≤ log(x) ≤ log(hi)`
    so `log(x) ∈ [logPoint(lo).lo, logPoint(hi).hi]`. -/
def logInterval (I : QInterval) (hI : 0 < I.lo) : QInterval where
  lo := (logPoint I.lo hI).lo
  hi := (logPoint I.hi (lt_of_lt_of_le hI I.valid)).hi
  valid := by
    have hlog_lo := logPoint_containsReal I.lo hI
    have hlog_hi := logPoint_containsReal I.hi (lt_of_lt_of_le hI I.valid)
    have hmon : Real.log (↑I.lo : ℝ) ≤ Real.log (↑I.hi : ℝ) :=
      Real.log_le_log (by exact_mod_cast hI) (by exact_mod_cast I.valid)
    have h : (↑(logPoint I.lo hI).lo : ℝ) ≤
        ↑(logPoint I.hi (lt_of_lt_of_le hI I.valid)).hi :=
      le_trans (le_trans hlog_lo.1 hmon) hlog_hi.2
    exact_mod_cast h

/-- Containment theorem for logInterval: monotonicity of log + logPoint containment. -/
theorem logInterval_containsReal {I : QInterval} {x : ℝ}
    (hI : 0 < I.lo) (hx : I.containsReal x) :
    (logInterval I hI).containsReal (Real.log x) := by
  simp only [logInterval, QInterval.containsReal]
  have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le (by exact_mod_cast hI) hx.1
  have hlog_lo := logPoint_containsReal I.lo hI
  have hlog_hi := logPoint_containsReal I.hi (lt_of_lt_of_le hI I.valid)
  constructor
  · exact le_trans hlog_lo.1 (Real.log_le_log (by exact_mod_cast hI) hx.1)
  · exact le_trans (Real.log_le_log hx_pos hx.2) hlog_hi.2

end Linglib.Interval
