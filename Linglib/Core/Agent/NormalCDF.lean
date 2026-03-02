import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Standard Normal CDF Infrastructure
@cite{luce-1959}

Shared Gaussian CDF definitions and properties used by both Thurstone's
discriminal-process theory (§2.D) and Signal Detection Theory (§2.E)
in Luce (1959).

## Definitions

- `normalPDF`: the standard normal density φ(t) = (1/√(2π)) exp(−t²/2)
- `normalCDF`: the standard normal CDF Φ(x) = ∫_{−∞}^{x} φ(t) dt

## Properties

Monotonicity, strict monotonicity, symmetry, boundary values, and bounds.
All proofs are `sorry` — they require measure-theoretic arguments about
the Gaussian integral that are not yet in Mathlib.
-/

set_option autoImplicit false

namespace Core

open Real MeasureTheory BigOperators Set

-- ============================================================================
-- §1. Normal PDF
-- ============================================================================

/-- The standard normal probability density function: `φ(t) = (1/√(2π)) · exp(-t²/2)`. -/
noncomputable def normalPDF (t : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(t ^ 2) / 2)

-- ============================================================================
-- §2. Normal CDF
-- ============================================================================

/-- The standard normal cumulative distribution function:
    `Φ(x) = ∫_{-∞}^{x} (1/√(2π)) exp(-t²/2) dt`.

    Defined as the Lebesgue integral of the standard normal PDF over `(-∞, x]`. -/
noncomputable def normalCDF (x : ℝ) : ℝ :=
  ∫ t in Iic x, normalPDF t

-- ============================================================================
-- §3. Properties
-- ============================================================================

/-- The normal CDF is non-negative: `Φ(x) ≥ 0` for all `x`. -/
theorem normalCDF_nonneg (x : ℝ) : 0 ≤ normalCDF x := by
  sorry -- TODO: non-negativity of integral of non-negative density

/-- The normal CDF is at most 1: `Φ(x) ≤ 1` for all `x`. -/
theorem normalCDF_le_one (x : ℝ) : normalCDF x ≤ 1 := by
  sorry -- TODO: CDF is at most 1 (total integral is 1)

/-- The normal CDF is monotone increasing. -/
theorem normalCDF_mono : Monotone normalCDF := by
  sorry -- TODO: follows from normalPDF being non-negative

/-- `Φ(0) = 1/2` by symmetry of the standard normal distribution. -/
theorem normalCDF_zero : normalCDF 0 = 1 / 2 := by
  sorry -- TODO: symmetry of the Gaussian integral

/-- For `x > 0`, `Φ(x) > 1/2`. -/
theorem normalCDF_pos_gt_half {x : ℝ} (hx : 0 < x) : 1 / 2 < normalCDF x := by
  sorry -- TODO: follows from normalCDF_mono and normalCDF_zero

/-- For `x < 0`, `Φ(x) < 1/2`. -/
theorem normalCDF_neg_lt_half {x : ℝ} (hx : x < 0) : normalCDF x < 1 / 2 := by
  sorry -- TODO: follows from normalCDF_mono and normalCDF_zero

/-- Symmetry: `Φ(-x) = 1 - Φ(x)`. -/
theorem normalCDF_neg (x : ℝ) : normalCDF (-x) = 1 - normalCDF x := by
  sorry -- TODO: change of variables t ↦ -t in the integral

/-- The normal CDF is strictly monotone increasing. -/
theorem normalCDF_strictMono : StrictMono normalCDF := by
  sorry -- TODO: follows from normalPDF being strictly positive

end Core
