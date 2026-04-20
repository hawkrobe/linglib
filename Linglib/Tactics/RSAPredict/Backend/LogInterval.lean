import Linglib.Tactics.RSAPredict.Backend.PadeExp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-!
# LogInterval — Interval Arithmetic for Real.log via Bisection

Computes `log(q)` for rational `q > 0` by bisecting against `expPoint`:
find `lo`, `hi` such that `exp(lo) ≤ q ≤ exp(hi)`, then refine by bisection.

## Strategy

1. Initial bracket: `log(q) ∈ [-(log₂(den)+1), log₂(num)+1]`
   Uses bit lengths for a tight bracket proportional to `log(q)`, not `q` itself.
   (since `n < 2^(log₂ n + 1) ≤ exp(log₂ n + 1)` for positive n)
2. Bisect 50 iterations: check `exp(mid)` vs `q` using `expPoint` bounds
3. Return `[lo, hi]` as `QInterval` containing `Real.log q`

## Precision

50 bisection iterations on a bracket of width `W` give precision `W/2^50 ≈ W × 10⁻¹⁵`.
Bracket width is `log₂(num) + log₂(den) + 2`, so for 64-bit rationals: `W ≤ 130`,
precision ≈ `1.2 × 10⁻¹³`.
-/

namespace Interval

open Interval.QInterval

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

    Initial bracket: `[-(Nat.log 2 q.den + 1), Nat.log 2 q.num.natAbs + 1]`.
    This uses bit lengths instead of raw values, giving a bracket width
    proportional to `log₂(q)` rather than `q` itself — critical for
    large-denominator rationals from interval arithmetic chains.

    Lower: `exp(-(log₂ d + 1)) < 1/d ≤ q` since `d < 2^(log₂ d + 1) ≤ exp(log₂ d + 1)`.
    Upper: `q ≤ p ≤ exp(log₂ p + 1)` by the same argument.

    50 bisection iterations narrow this to precision `bracket_width / 2^50`. -/
def logPoint (q : ℚ) (_hq : 0 < q) : QInterval :=
  -- Special case: log(1) = 0 exactly. This is the only rational q with
  -- log(q) ∈ ℚ (by Lindemann-Weierstrass), so the bisection stalls here
  -- because exp(0) = 1 = q and the Padé interval straddles the target.
  if q = 1 then QInterval.exact 0
  else
  let lo₀ : ℚ := -(↑(Nat.log 2 q.den + 1) : ℚ)
  let hi₀ : ℚ := ↑(Nat.log 2 q.num.natAbs + 1)
  have hle₀ : lo₀ ≤ hi₀ := by
    show -(↑(Nat.log 2 q.den + 1) : ℚ) ≤ ↑(Nat.log 2 q.num.natAbs + 1)
    have : (0 : ℚ) ≤ ↑(Nat.log 2 q.den + 1) := Nat.cast_nonneg _
    have : (0 : ℚ) ≤ ↑(Nat.log 2 q.num.natAbs + 1) := Nat.cast_nonneg _
    linarith
  let ⟨(lo, hi), hle⟩ := logBisectCore q lo₀ hi₀ hle₀ logIterations
  ⟨lo, hi, hle⟩

/-- n ≤ exp(n) for natural numbers, since exp(x) ≥ 1 + x ≥ x. -/
private theorem nat_le_exp (n : ℕ) : (↑n : ℝ) ≤ Real.exp (↑n : ℝ) :=
  le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp _)

/-- 2^k ≤ exp(k) for natural k, since exp(1) ≥ 2 and exp is multiplicative. -/
private theorem pow2_le_exp (k : ℕ) : (2 : ℝ) ^ k ≤ Real.exp (↑k : ℝ) := by
  induction k with
  | zero => simp [Real.exp_zero]
  | succ n ih =>
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      _ = 2 * 2 ^ n := by ring
      _ ≤ Real.exp 1 * Real.exp (↑n) := mul_le_mul h2 ih (pow_nonneg (by norm_num) n)
            (Real.exp_nonneg _)
      _ = Real.exp (1 + ↑n) := (Real.exp_add 1 ↑n).symm
      _ = Real.exp (↑(n + 1) : ℝ) := by push_cast; ring_nf

/-- n < exp(Nat.log 2 n + 1) for positive n, using n < 2^(log₂ n + 1) ≤ exp(log₂ n + 1). -/
private theorem lt_exp_log2_succ (n : ℕ) (_hn : 0 < n) :
    (↑n : ℝ) < Real.exp (↑(Nat.log 2 n + 1) : ℝ) := by
  have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  calc (↑n : ℝ) < ↑(2 ^ (Nat.log 2 n + 1) : ℕ) := by exact_mod_cast h1
    _ = (2 : ℝ) ^ (Nat.log 2 n + 1) := by push_cast; ring
    _ ≤ Real.exp (↑(Nat.log 2 n + 1) : ℝ) := pow2_le_exp _

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

/-- Initial lower bracket: exp(-(Nat.log 2 den + 1)) ≤ q for q > 0.
    Since den < 2^(log₂ den + 1) ≤ exp(log₂ den + 1), we get
    exp(-(log₂ den + 1)) ≤ 1/den ≤ q. -/
private theorem initial_lower_bound (q : ℚ) (hq : 0 < q) :
    Real.exp (↑(-(↑(Nat.log 2 q.den + 1) : ℚ)) : ℝ) ≤ (↑q : ℝ) := by
  have hd_pos : (0 : ℝ) < ↑q.den := by exact_mod_cast Nat.cast_pos.mpr q.pos
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have hd_lt_exp : (↑q.den : ℝ) < Real.exp (↑(Nat.log 2 q.den + 1) : ℝ) :=
    lt_exp_log2_succ q.den q.pos
  have hgoal : Real.exp (-(↑(Nat.log 2 q.den + 1) : ℝ)) ≤ (↑q : ℝ) := by
    calc Real.exp (-(↑(Nat.log 2 q.den + 1) : ℝ))
        = (Real.exp (↑(Nat.log 2 q.den + 1) : ℝ))⁻¹ := Real.exp_neg _
      _ ≤ (↑q.den : ℝ)⁻¹ := inv_anti₀ hd_pos hd_lt_exp.le
      _ = 1 / (↑q.den : ℝ) := (one_div (↑q.den : ℝ)).symm
      _ ≤ ↑q.num / ↑q.den := by
          apply div_le_div_of_nonneg_right _ hd_pos.le
          exact_mod_cast hnum_pos
      _ = ↑q := by exact_mod_cast Rat.num_div_den q
  simp only [Rat.cast_neg, Rat.cast_natCast] at hgoal ⊢
  exact hgoal

/-- Initial upper bracket: q ≤ exp(Nat.log 2 num + 1) for q > 0. -/
private theorem initial_upper_bound (q : ℚ) (hq : 0 < q) :
    (↑q : ℝ) ≤ Real.exp (↑(↑(Nat.log 2 q.num.natAbs + 1) : ℚ) : ℝ) := by
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have hna_pos : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnum_pos)
  have h_q_le : q ≤ (↑q.num.natAbs : ℚ) := by
    have h1 : q * ↑q.den = ↑q.num := by exact_mod_cast Rat.mul_den_eq_num q
    have h2 : (1 : ℚ) ≤ ↑q.den := by exact_mod_cast q.pos
    have h3 : q ≤ q * ↑q.den :=
      le_mul_of_one_le_right (le_of_lt (by exact_mod_cast hq)) h2
    have h4 : q ≤ ↑q.num := by linarith
    exact le_trans h4 (by
      show (↑q.num : ℚ) ≤ ↑(↑q.num.natAbs : ℤ)
      exact_mod_cast le_of_eq (Int.natAbs_of_nonneg hnum_pos.le).symm)
  have hgoal : (↑q : ℝ) ≤ Real.exp (↑(Nat.log 2 q.num.natAbs + 1) : ℝ) := by
    calc (↑q : ℝ) ≤ (↑q.num.natAbs : ℝ) := by exact_mod_cast h_q_le
      _ ≤ Real.exp (↑(Nat.log 2 q.num.natAbs + 1) : ℝ) :=
            le_of_lt (lt_exp_log2_succ q.num.natAbs hna_pos)
  simp only [Rat.cast_natCast] at hgoal ⊢
  exact hgoal

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
    have hle₀ : -(↑(Nat.log 2 q.den + 1) : ℚ) ≤ (↑(Nat.log 2 q.num.natAbs + 1) : ℚ) := by
      linarith [Nat.cast_nonneg (α := ℚ) (Nat.log 2 q.den + 1),
                Nat.cast_nonneg (α := ℚ) (Nat.log 2 q.num.natAbs + 1)]
    have hsound := logBisectCore_sound q
        (-(↑(Nat.log 2 q.den + 1) : ℚ)) (↑(Nat.log 2 q.num.natAbs + 1)) hle₀
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

/-- When the argument is known to be zero (from interval [0,0]),
    `Real.log x = Real.log 0 = 0`, contained in `exact 0`. -/
theorem log_zero_containsReal {I : QInterval} {x : ℝ}
    (hx : I.containsReal x) (hlo : 0 ≤ I.lo) (hhi : I.hi ≤ 0) :
    (QInterval.exact 0).containsReal (Real.log x) := by
  have : x = 0 := QInterval.eq_zero_of_contained_nonneg hx hlo hhi
  rw [this, Real.log_zero]
  exact QInterval.exact_zero_containsReal

end Interval
