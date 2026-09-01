import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.Real

/-!
# The uniform measure on a finite type

Evaluation of `ProbabilityTheory.uniformOn` on a finset or on `Set.univ` at singletons and
finite sets, in `ℝ≥0∞` and on reals.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {W : Type*} [MeasurableSpace W] [MeasurableSingletonClass W] [Fintype W]

omit [Fintype W] in
/-- The uniform measure on a finset at a singleton: `1 / #A` on `A` and `0` off it. -/
theorem uniformOn_finset_apply_singleton [DecidableEq W] (A : Finset W) (w : W) :
    uniformOn ↑A {w} = if w ∈ A then (A.card : ℝ≥0∞)⁻¹ else 0 := by
  rw [← Finset.coe_singleton, uniformOn_apply_finset]
  by_cases h : w ∈ A <;> simp [Finset.inter_singleton_of_mem, Finset.inter_singleton_of_notMem, h,
    div_eq_mul_inv]

theorem uniformOn_univ_apply_singleton (w : W) :
    uniformOn (Set.univ : Set W) {w} = (Fintype.card W : ℝ≥0∞)⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton, one_div]

theorem uniformOn_univ_singleton_ne_zero (w : W) : uniformOn (Set.univ : Set W) {w} ≠ 0 := by
  rw [uniformOn_univ_apply_singleton]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem uniformOn_univ_singleton_eq (w w' : W) :
    uniformOn (Set.univ : Set W) {w} = uniformOn Set.univ {w'} := by
  rw [uniformOn_univ_apply_singleton, uniformOn_univ_apply_singleton]

theorem uniformOn_univ_real_singleton (w : W) :
    (uniformOn (Set.univ : Set W)).real {w} = (Fintype.card W : ℝ)⁻¹ := by
  rw [measureReal_def, uniformOn_univ, Measure.count_singleton, one_div,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem uniformOn_univ_real_coe_finset (s : Finset W) :
    (uniformOn (Set.univ : Set W)).real ↑s = s.card / Fintype.card W := by
  rw [measureReal_def, uniformOn_univ, Measure.count_apply_finset, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]

end MeasureTheory
