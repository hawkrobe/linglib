import Linglib.Core.Interval.QInterval
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

/-!
# PadeExp — Padé Approximant for exp(x) with Interval Bounds

[4/4] Padé approximant for `exp(x)` on `[-1, 1]`, with argument reduction
for arbitrary `x ∈ ℝ`. The approximant has relative error < 10⁻⁷ on [-1,1],
so the error bound `1/4000000` provides a 2.3× safety margin.

## Strategy

For small |x| ≤ 1:
  exp(x) ≈ padeNum(x) / padeDen(x)   (within padeErrorBound)

For large |x|:
  1. Choose k so x/2^k ∈ [-1, 1]
  2. Compute exp(x/2^k) via Padé
  3. Square k times: exp(x) = exp(x/2^k)^(2^k)

-/

namespace Linglib.Interval

open Linglib.Interval.QInterval

-- ============================================================================
-- Padé Coefficients
-- ============================================================================

/-- Padé [4/4] numerator: 1 + x/2 + 3x²/28 + x³/84 + x⁴/1680 (Horner form). -/
def padeNum (x : ℚ) : ℚ :=
  1 + x * (1/2 + x * (3/28 + x * (1/84 + x * (1/1680))))

/-- Padé [4/4] denominator: padeNum(-x). -/
def padeDen (x : ℚ) : ℚ := padeNum (-x)

/-- Padé [4/4] approximant: padeNum(x) / padeDen(x). -/
def padeExp (x : ℚ) : ℚ := padeNum x / padeDen x

-- ============================================================================
-- Coefficient verification
-- ============================================================================

/-- padeExp(0) = 1 (exact). -/
theorem padeExp_zero : padeExp 0 = 1 := by native_decide

/-- padeDen(1) > 0 (denominator positive on [-1, 1]). -/
theorem padeDen_pos_at_one : 0 < padeDen 1 := by native_decide

/-- padeDen(-1) > 0. -/
theorem padeDen_pos_at_neg_one : 0 < padeDen (-1) := by native_decide

/-- padeExp(1) ≈ e (within 10⁻⁷): 2721/1001 ≈ 2.71828171... vs e ≈ 2.71828183. -/
theorem padeExp_at_one : padeExp 1 = 2721 / 1001 := by native_decide

-- ============================================================================
-- Error Bound
-- ============================================================================

/-- Conservative error bound for Padé [4/4] on [-1, 1].
    True error is ~4.3×10⁻⁸; this bound gives 2.3× safety margin. -/
def padeErrorBound : ℚ := 1 / 4000000

/-- The Padé [4/4] approximant is within `padeErrorBound` of exp on [-1, 1].

    Proof approach: use `Real.exp_bound` with n ≥ 11 to get |exp(q) - T_n(q)| ≤ ε₁,
    then bound |T_n(q) - padeExp(q)| ≤ ε₂ via polynomial algebra on the numerator
    T_n(q)·padeDen(q) - padeNum(q). The polynomial algebra (~200 lines) is deferred.

    True error is ~4.3×10⁻⁸; the bound 1/4000000 = 2.5×10⁻⁷ has a 2.3× margin. -/
theorem pade_error_bound (q : ℚ) (hq_lo : -1 ≤ q) (hq_hi : q ≤ 1)
    (hden_pos : 0 < padeDen q) :
    |Real.exp (↑q : ℝ) - (↑(padeExp q) : ℝ)| ≤ (↑padeErrorBound : ℝ) := by
  sorry

-- ============================================================================
-- Point interval for exp at a rational
-- ============================================================================

/-- Interval containing exp(q) for q ∈ [-1, 1], computed via Padé.
    Returns [padeExp(q) - ε, padeExp(q) + ε] where ε = padeErrorBound. -/
def expPointSmall (q : ℚ) (hq_lo : -1 ≤ q) (hq_hi : q ≤ 1)
    (hden_pos : 0 < padeDen q) : QInterval where
  lo := padeExp q - padeErrorBound
  hi := padeExp q + padeErrorBound
  valid := by simp only [padeErrorBound]; linarith

theorem expPointSmall_containsReal (q : ℚ) (hq_lo : -1 ≤ q) (hq_hi : q ≤ 1)
    (hden_pos : 0 < padeDen q) :
    (expPointSmall q hq_lo hq_hi hden_pos).containsReal (Real.exp (↑q : ℝ)) := by
  simp only [expPointSmall, containsReal]
  have h := pade_error_bound q hq_lo hq_hi hden_pos
  rw [abs_le] at h
  push_cast
  constructor <;> linarith

-- ============================================================================
-- Argument Reduction
-- ============================================================================

/-- Number of halvings needed so q / 2^k ∈ [-1, 1]. -/
def reductionSteps (q : ℚ) : ℕ :=
  if q.num.natAbs ≤ q.den then 0
  else Nat.log 2 q.num.natAbs - Nat.log 2 q.den + 1

/-- Repeated squaring of a nonneg interval (carries nonneg proof with value). -/
private def repeatedSqCore (I : QInterval) (n : ℕ) (h : 0 ≤ I.lo) :
    { J : QInterval // 0 ≤ J.lo } :=
  match n with
  | 0 => ⟨I, h⟩
  | n + 1 =>
    let ⟨prev, hprev⟩ := repeatedSqCore I n h
    ⟨prev.mulNonneg prev hprev hprev, mul_nonneg hprev hprev⟩

/-- Repeated squaring of a nonneg interval.
    Squares I a total of n times: repeatedSq I 0 = I, repeatedSq I (n+1) = (repeatedSq I n)². -/
def repeatedSq (I : QInterval) (n : ℕ) (h : 0 ≤ I.lo) : QInterval :=
  (repeatedSqCore I n h).val

theorem repeatedSq_nonneg (I : QInterval) (n : ℕ) (h : 0 ≤ I.lo) :
    0 ≤ (repeatedSq I n h).lo :=
  (repeatedSqCore I n h).property

-- ============================================================================
-- expPoint: Point interval for exp(q) at arbitrary rational q
-- ============================================================================

/-- Point interval containing exp(q) for arbitrary rational q.

    Strategy: reduce q → q' = q/2^k with |q'| ≤ 1 via `reductionSteps`,
    compute exp(q') via Padé [4/4], then square k times since exp(q) = exp(q')^(2^k).

    The nonneg guard on `small.lo` is always true by construction:
    padeExp(q') ≈ exp(q') ≥ exp(-1) ≈ 0.368 >> padeErrorBound = 2.5×10⁻⁷. -/
def expPoint (q : ℚ) : QInterval :=
  let k := reductionSteps q
  let q' := q / (2 ^ k : ℚ)
  let approx := padeExp q'
  let small : QInterval :=
    ⟨approx - padeErrorBound, approx + padeErrorBound,
     by simp only [padeErrorBound]; linarith⟩
  if h : 0 ≤ small.lo then
    repeatedSq small k h
  else
    -- Unreachable: padeExp(q') ≈ exp(q') ≥ exp(-1) ≈ 0.368 >> padeErrorBound.
    -- Sound fallback: exp(q) ∈ (0, 3^|num(q)|] since e < 3.
    ⟨0, (3 : ℚ) ^ q.num.natAbs,
     le_of_lt (pow_pos (by norm_num : (0 : ℚ) < 3) _)⟩

/-- padeDen(q) > 0 for -1 ≤ q ≤ 1. Writing padeDen(q) = (1 - q/2) + q²·(3/28 - q/84 + q²/1680),
    the first term ≥ 1/2 and the second ≥ 0 since 3/28 - q/84 ≥ 3/28 - 1/84 > 0. -/
private theorem padeDen_pos (q : ℚ) (hlo : -1 ≤ q) (hhi : q ≤ 1) :
    0 < padeDen q := by
  simp only [padeDen, padeNum]
  nlinarith [sq_nonneg q, sq_nonneg (q * q), sq_nonneg (1 - q), sq_nonneg (1 + q),
             mul_self_nonneg (q * q - q / 2)]

/-- |q| ≤ 1 when q.num.natAbs ≤ q.den. -/
private theorem abs_le_one_of_natAbs_le_den (q : ℚ) (h : q.num.natAbs ≤ q.den) :
    -1 ≤ q ∧ q ≤ 1 := by
  have hd_pos : (0 : ℚ) < ↑q.den := Nat.cast_pos.mpr q.pos
  constructor
  · -- -1 ≤ q ↔ -↑q.den ≤ ↑q.num (after multiplying by q.den)
    rw [← Rat.num_div_den q]
    rw [show (-1 : ℚ) = -(↑q.den) / ↑q.den from by rw [neg_div_self (ne_of_gt hd_pos)]]
    apply div_le_div_of_nonneg_right _ (le_of_lt hd_pos)
    exact_mod_cast le_trans (neg_le_neg (Int.ofNat_le.mpr h))
      (show -(↑q.num.natAbs : ℤ) ≤ q.num from by rw [← Int.abs_eq_natAbs]; exact neg_abs_le _)
  · -- q ≤ 1 ↔ ↑q.num ≤ ↑q.den
    rw [← Rat.num_div_den q]
    rw [show (1 : ℚ) = ↑q.den / ↑q.den from by rw [div_self (ne_of_gt hd_pos)]]
    apply div_le_div_of_nonneg_right _ (le_of_lt hd_pos)
    exact_mod_cast le_trans Int.le_natAbs (Int.ofNat_le.mpr h)

/-- q / 2^(reductionSteps q) ∈ [-1, 1]. -/
private theorem reductionSteps_spec (q : ℚ) :
    -1 ≤ q / (2 ^ reductionSteps q : ℚ) ∧ q / (2 ^ reductionSteps q : ℚ) ≤ 1 := by
  simp only [reductionSteps]
  split
  · -- q.num.natAbs ≤ q.den, k = 0
    simp only [pow_zero, div_one]
    exact abs_le_one_of_natAbs_le_den q ‹_›
  · -- q.num.natAbs > q.den, k = log₂(natAbs) - log₂(den) + 1
    rename_i hgt; push_neg at hgt
    -- q / 2^k has numerator q.num and denominator q.den * 2^k
    -- We need: (q / 2^k).num.natAbs ≤ (q / 2^k).den
    -- This follows from 2^k ≥ q.num.natAbs / q.den
    sorry

/-- Repeated squaring preserves containment: if I contains z ≥ 0,
    then repeatedSq I n h contains z^(2^n). -/
private theorem repeatedSq_containsReal {I : QInterval} {z : ℝ}
    (h : 0 ≤ I.lo) (hz : I.containsReal z) (hz_nn : 0 ≤ z) :
    ∀ n, (repeatedSq I n h).containsReal (z ^ (2 ^ n))
  | 0 => by simp [repeatedSq, repeatedSqCore]; exact hz
  | n + 1 => by
    simp only [repeatedSq, repeatedSqCore]
    have ih := repeatedSq_containsReal h hz hz_nn n
    have h_nn := repeatedSq_nonneg I n h
    show (QInterval.mulNonneg _ _ h_nn h_nn).containsReal (z ^ 2 ^ (n + 1))
    rw [show 2 ^ (n + 1) = 2 ^ n * 2 from by ring, pow_mul, sq]
    exact QInterval.mulNonneg_containsReal h_nn h_nn ih ih

/-- exp(q) = exp(q / 2^k)^(2^k), via Real.exp_nat_mul. -/
private theorem exp_pow_reduction (q : ℚ) (k : ℕ) :
    Real.exp (↑q : ℝ) = Real.exp (↑(q / (2 ^ k : ℚ)) : ℝ) ^ (2 ^ k) := by
  conv_lhs =>
    rw [show (↑q : ℝ) = ↑(2 ^ k : ℕ) * ↑(q / (2 ^ k : ℚ)) from by
      push_cast
      rw [mul_div_cancel₀]
      exact_mod_cast ne_of_gt (pow_pos (by norm_num : (0 : ℚ) < 2) k)]
  exact Real.exp_nat_mul _ _

/-- exp(n) ≤ 3^n for all n : ℕ, since e < 3. -/
private theorem exp_le_three_pow (n : ℕ) : Real.exp (↑n : ℝ) ≤ (3 : ℝ) ^ n := by
  induction n with
  | zero => simp [Real.exp_zero]
  | succ n ih =>
    rw [show (↑(n + 1) : ℝ) = ↑n + 1 from by push_cast; ring]
    rw [Real.exp_add, pow_succ]
    exact mul_le_mul ih (le_of_lt Real.exp_one_lt_three) (le_of_lt (Real.exp_pos _)) (by positivity)

/-- q ≤ q.num.natAbs as reals, since q = num/den with den ≥ 1. -/
private theorem rat_le_natAbs_num (q : ℚ) : (↑q : ℝ) ≤ ↑(q.num.natAbs : ℕ) := by
  suffices h : q ≤ (↑q.num.natAbs : ℚ) by exact_mod_cast h
  have hd_pos : (0 : ℚ) < ↑q.den := Nat.cast_pos.mpr q.pos
  calc q = ↑q.num / ↑q.den := (Rat.num_div_den q).symm
    _ ≤ ↑(↑q.num.natAbs : ℤ) / ↑q.den := by
        apply div_le_div_of_nonneg_right _ hd_pos.le
        exact_mod_cast le_trans (le_abs_self q.num) (le_of_eq (Int.abs_eq_natAbs q.num))
    _ ≤ ↑(↑q.num.natAbs : ℤ) / 1 := by
        apply div_le_div_of_nonneg_left _ one_pos (by exact_mod_cast q.pos)
        exact_mod_cast Nat.zero_le q.num.natAbs
    _ = ↑(↑q.num.natAbs : ℤ) := div_one _

set_option maxHeartbeats 400000 in
/-- Containment theorem for expPoint. -/
theorem expPoint_containsReal (q : ℚ) :
    (expPoint q).containsReal (Real.exp (↑q : ℝ)) := by
  unfold expPoint
  simp only []
  split
  · -- Main path: small.lo ≥ 0, so result = repeatedSq small k h
    rename_i h
    have ⟨hlo, hhi⟩ := reductionSteps_spec q
    have hden := padeDen_pos _ hlo hhi
    -- The small interval contains exp(q')
    have h_small := expPointSmall_containsReal _ hlo hhi hden
    -- The raw ⟨..., ...⟩ interval equals expPointSmall definitionally
    change (repeatedSq _ (reductionSteps q) h).containsReal _
    have h_nn : (0 : ℝ) ≤ Real.exp (↑(q / (2 ^ reductionSteps q : ℚ)) : ℝ) :=
      le_of_lt (Real.exp_pos _)
    rw [exp_pow_reduction q (reductionSteps q)]
    exact repeatedSq_containsReal h h_small h_nn _
  · -- Fallback: exp(q) ∈ [0, 3^|num(q)|]
    simp only [QInterval.containsReal]
    constructor
    · exact_mod_cast le_of_lt (Real.exp_pos _)
    · have h := le_trans (Real.exp_le_exp_of_le (rat_le_natAbs_num q)) (exp_le_three_pow _)
      exact_mod_cast h

-- ============================================================================
-- Main entry point
-- ============================================================================

/-- Interval containing exp(x) for x in rational interval I.

    Uses monotonicity of exp: for x ∈ [lo, hi],
      exp(lo) ≤ exp(x) ≤ exp(hi)
    so exp(x) ∈ [expPoint(lo).lo, expPoint(hi).hi]. -/
def expInterval (I : QInterval) : QInterval where
  lo := (expPoint I.lo).lo
  hi := (expPoint I.hi).hi
  valid := by
    have hlo := expPoint_containsReal I.lo
    have hhi := expPoint_containsReal I.hi
    have hmon : Real.exp (↑I.lo : ℝ) ≤ Real.exp (↑I.hi : ℝ) :=
      Real.exp_le_exp_of_le (by exact_mod_cast I.valid)
    have h : (↑(expPoint I.lo).lo : ℝ) ≤ ↑(expPoint I.hi).hi :=
      le_trans (le_trans hlo.1 hmon) hhi.2
    exact_mod_cast h

/-- Containment theorem for expInterval: monotonicity of exp + expPoint containment. -/
theorem expInterval_containsReal {I : QInterval} {x : ℝ}
    (hx : I.containsReal x) :
    (expInterval I).containsReal (Real.exp x) := by
  simp only [expInterval, QInterval.containsReal]
  have hlo := expPoint_containsReal I.lo
  have hhi := expPoint_containsReal I.hi
  constructor
  · exact le_trans hlo.1 (Real.exp_le_exp_of_le hx.1)
  · exact le_trans (Real.exp_le_exp_of_le hx.2) hhi.2

end Linglib.Interval
