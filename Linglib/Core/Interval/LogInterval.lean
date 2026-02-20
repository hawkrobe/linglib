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

/-- n ≤ exp(n) for natural numbers, since exp(x) ≥ 1 + x ≥ x. -/
private theorem nat_le_exp (n : ℕ) : (↑n : ℝ) ≤ Real.exp (↑n : ℝ) :=
  le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp _)

/-- logBisectCore preserves the bisection invariant exp(lo) ≤ q ≤ exp(hi). -/
private theorem logBisectCore_sound (q : ℚ) (lo hi : ℚ) (hle : lo ≤ hi) (n : ℕ)
    (h_lo : Real.exp (↑lo : ℝ) ≤ ↑q) (h_hi : (↑q : ℝ) ≤ Real.exp (↑hi : ℝ)) :
    Real.exp (↑(logBisectCore q lo hi hle n).val.1 : ℝ) ≤ ↑q ∧
    (↑q : ℝ) ≤ Real.exp (↑(logBisectCore q lo hi hle n).val.2 : ℝ) := by
  induction n generalizing lo hi with
  | zero => simp [logBisectCore]; exact ⟨h_lo, h_hi⟩
  | succ n ih =>
    simp only [logBisectCore]
    split
    · rename_i h_mid_le
      exact ih _ _ _
        (le_trans (expPoint_containsReal _).2 (by exact_mod_cast h_mid_le)) h_hi
    · split
      · rename_i _ h_le_mid
        exact ih _ _ _ h_lo
          (le_trans (by exact_mod_cast h_le_mid) (expPoint_containsReal _).1)
      · exact ih _ _ _ h_lo h_hi

/-- Initial lower bracket: exp(-den) ≤ q for q > 0.
    Since exp(d) ≥ d, we get exp(-d) = 1/exp(d) ≤ 1/d ≤ num/d = q. -/
private theorem initial_lower_bound (q : ℚ) (hq : 0 < q) :
    Real.exp (↑(-(↑q.den : ℚ)) : ℝ) ≤ (↑q : ℝ) := by
  have hd_pos : (0 : ℝ) < ↑q.den := by exact_mod_cast Nat.cast_pos.mpr q.pos
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  push_cast
  calc Real.exp (-(↑q.den : ℝ))
      = (Real.exp (↑q.den : ℝ))⁻¹ := Real.exp_neg _
    _ ≤ (↑q.den : ℝ)⁻¹ := inv_anti₀ hd_pos (nat_le_exp q.den)
    _ = 1 / (↑q.den : ℝ) := (one_div (↑q.den : ℝ)).symm
    _ ≤ ↑q.num / ↑q.den := by
        apply div_le_div_of_nonneg_right _ hd_pos.le
        exact_mod_cast hnum_pos
    _ = ↑q := by exact_mod_cast Rat.num_div_den q

/-- Initial upper bracket: q ≤ exp(natAbs(q.num)) for q > 0. -/
private theorem initial_upper_bound (q : ℚ) (hq : 0 < q) :
    (↑q : ℝ) ≤ Real.exp (↑(↑q.num.natAbs : ℚ) : ℝ) := by
  have hd_pos : (0 : ℚ) < ↑q.den := Nat.cast_pos.mpr q.pos
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have h_q_le : q ≤ (↑q.num.natAbs : ℚ) := by
    -- q * den = num, and den ≥ 1, so q ≤ num = natAbs
    have h1 : q * ↑q.den = ↑q.num := by exact_mod_cast Rat.mul_den_eq_num q
    have h2 : (1 : ℚ) ≤ ↑q.den := by exact_mod_cast q.pos
    have h3 : q ≤ q * ↑q.den :=
      le_mul_of_one_le_right (le_of_lt (by exact_mod_cast hq)) h2
    have h4 : q ≤ ↑q.num := by linarith
    exact le_trans h4 (by
      show (↑q.num : ℚ) ≤ ↑(↑q.num.natAbs : ℤ)
      exact_mod_cast le_of_eq (Int.natAbs_of_nonneg hnum_pos.le).symm)
  calc (↑q : ℝ) ≤ (↑(↑q.num.natAbs : ℚ) : ℝ) := by push_cast; exact_mod_cast h_q_le
    _ ≤ Real.exp (↑(↑q.num.natAbs : ℚ) : ℝ) := by push_cast; exact nat_le_exp _

/-- Containment theorem for logPoint: the bisection invariant exp(lo) ≤ q ≤ exp(hi)
    implies lo ≤ log(q) ≤ hi by monotonicity of log. -/
theorem logPoint_containsReal (q : ℚ) (hq : 0 < q) :
    (logPoint q hq).containsReal (Real.log (↑q : ℝ)) := by
  unfold logPoint
  simp only []
  split
  · -- q = 1: exact 0 contains log(1) = 0
    subst ‹q = 1›
    simp [QInterval.exact, QInterval.containsReal, Real.log_one]
  · -- q ≠ 1: bisection
    simp only [QInterval.containsReal]
    have hle₀ : -(↑q.den : ℚ) ≤ (↑q.num.natAbs : ℚ) := by
      linarith [Nat.cast_nonneg (α := ℚ) q.den, Nat.cast_nonneg (α := ℚ) q.num.natAbs]
    have hsound := logBisectCore_sound q (-(↑q.den : ℚ)) (↑q.num.natAbs) hle₀
        logIterations (initial_lower_bound q hq) (initial_upper_bound q hq)
    have hq_pos : (0 : ℝ) < ↑q := by exact_mod_cast hq
    constructor
    · -- lo ≤ log(q): from exp(lo) ≤ q, take log
      have h := Real.log_le_log (Real.exp_pos _) hsound.1
      rwa [Real.log_exp] at h
    · -- log(q) ≤ hi: from q ≤ exp(hi), take log
      have h := Real.log_le_log hq_pos hsound.2
      rwa [Real.log_exp] at h

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
