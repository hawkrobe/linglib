import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Order

/-!
# Casting nonnegative rationals into `ℝ≥0∞`

The cast `ℚ≥0 → ℝ≥0∞` factors through `ℝ≥0` (`ENNReal.coe_nnratCast`), so it commutes with
the semifield operations, with inversion and division away from zero, and reflects order and
equality; its real part is the real cast. An exact rational computation, certified by kernel
reduction in `ℚ≥0`, is transported to a statement about `ℝ≥0∞`-valued measures through these
lemmas.

## References

* [potts-levy-2015]
-/

open scoped NNRat NNReal ENNReal

namespace ENNReal

variable {ι : Type*} (p q : ℚ≥0)

@[simp, norm_cast]
theorem nnratCast_zero : ((0 : ℚ≥0) : ℝ≥0∞) = 0 := by
  simp only [← coe_nnratCast, NNRat.cast_zero, coe_zero]

@[simp, norm_cast]
theorem nnratCast_one : ((1 : ℚ≥0) : ℝ≥0∞) = 1 := by
  simp only [← coe_nnratCast, NNRat.cast_one, coe_one]

@[simp, norm_cast]
theorem nnratCast_mul : ((p * q : ℚ≥0) : ℝ≥0∞) = p * q := by
  simp only [← coe_nnratCast, NNRat.cast_mul, coe_mul]

@[simp, norm_cast]
theorem nnratCast_pow (n : ℕ) : ((q ^ n : ℚ≥0) : ℝ≥0∞) = (q : ℝ≥0∞) ^ n := by
  simp only [← coe_nnratCast, NNRat.cast_pow, coe_pow]

@[simp, norm_cast]
theorem nnratCast_natCast (n : ℕ) : ((n : ℚ≥0) : ℝ≥0∞) = n := by
  simp only [← coe_nnratCast, NNRat.cast_natCast, coe_natCast]

@[simp, norm_cast]
theorem nnratCast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℚ≥0) : ℝ≥0∞) = OfNat.ofNat n := by
  simp only [← coe_nnratCast, NNRat.cast_ofNat, coe_ofNat]

@[simp, norm_cast]
theorem nnratCast_sum (s : Finset ι) (f : ι → ℚ≥0) :
    ((∑ i ∈ s, f i : ℚ≥0) : ℝ≥0∞) = ∑ i ∈ s, (f i : ℝ≥0∞) := by
  simp only [← coe_nnratCast, NNRat.cast_sum, ofNNReal_finsetSum]

theorem nnratCast_inv (hq : q ≠ 0) : ((q⁻¹ : ℚ≥0) : ℝ≥0∞) = (q : ℝ≥0∞)⁻¹ := by
  simp only [← coe_nnratCast, NNRat.cast_inv, coe_inv (NNRat.cast_ne_zero.2 hq)]

theorem nnratCast_div (hq : q ≠ 0) : ((p / q : ℚ≥0) : ℝ≥0∞) = p / q := by
  simp only [← coe_nnratCast, NNRat.cast_div, coe_div (NNRat.cast_ne_zero.2 hq)]

@[simp, norm_cast]
theorem nnratCast_inj : (p : ℝ≥0∞) = q ↔ p = q := by
  simp only [← coe_nnratCast, coe_inj, NNRat.cast_inj]

@[simp, norm_cast]
theorem nnratCast_eq_zero : (q : ℝ≥0∞) = 0 ↔ q = 0 := by
  simp only [← coe_nnratCast, coe_eq_zero, NNRat.cast_eq_zero]

@[simp, norm_cast]
theorem nnratCast_lt : (p : ℝ≥0∞) < q ↔ p < q := by
  simp only [← coe_nnratCast, coe_lt_coe, NNRat.cast_lt]

@[simp, norm_cast]
theorem nnratCast_le : (p : ℝ≥0∞) ≤ q ↔ p ≤ q := by
  simp only [← coe_nnratCast, coe_le_coe, NNRat.cast_le]

@[simp]
theorem nnratCast_ne_top : (q : ℝ≥0∞) ≠ ∞ := by
  rw [← coe_nnratCast]; exact coe_ne_top

@[simp]
theorem toReal_nnratCast : (q : ℝ≥0∞).toReal = q := by
  rw [← coe_nnratCast, coe_toReal]; rfl

end ENNReal
