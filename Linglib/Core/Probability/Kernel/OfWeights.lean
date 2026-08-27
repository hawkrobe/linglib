import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Kernels from weight functions

This file defines `ProbabilityTheory.Kernel.ofWeights`, the kernel that normalizes a
nonnegative weight function on a finite target into a probability measure per row, and
evaluates it at singletons. A row of zero or infinite total weight collapses to the zero
measure, so the kernel is always finite; it is Markov exactly on rows with a positive finite
total.

## Main definitions

* `ProbabilityTheory.Kernel.ofWeights` — row `a` is proportional to `w a`.

## Main results

* `ProbabilityTheory.Kernel.ofWeights_apply_singleton` — `w a b / ∑ b', w a b'`.
* `ProbabilityTheory.Kernel.ofWeights_real_singleton_lt_iff` — row preference is weight
  comparison.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [Fintype β] [MeasurableSingletonClass β] in
theorem ofFunOfCountable_apply (f : α → Measure β) (a : α) : ofFunOfCountable f a = f a := rfl

/-- The kernel that normalizes a nonnegative weight function on a finite
target: row `a` is the probability measure proportional to `w a`. A row of
zero (or infinite) total weight collapses to the zero measure. -/
noncomputable def ofWeights (w : α → β → ℝ≥0∞) : Kernel α β :=
  ofFunOfCountable fun a => (∑ b, w a b)⁻¹ • ∑ b, w a b • Measure.dirac b

@[simp] theorem ofWeights_apply_singleton (w : α → β → ℝ≥0∞) (a : α) (b : β) :
    ofWeights w a {b} = w a b / ∑ b', w a b' := by
  have hval : (∑ b', w a b' • Measure.dirac b') {b} = w a b := by
    rw [Measure.finsetSum_apply,
      Finset.sum_eq_single_of_mem b (Finset.mem_univ b) fun b' _ hb' => by
        rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (.singleton b),
          Set.indicator_of_notMem (fun h => hb' (Set.mem_singleton_iff.mp h)), mul_zero],
      Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (.singleton b),
      Set.indicator_of_mem (Set.mem_singleton b), Pi.one_apply, mul_one]
  show ((∑ b', w a b')⁻¹ • ∑ b', w a b' • Measure.dirac b') {b} = _
  rw [Measure.smul_apply, smul_eq_mul, hval, ENNReal.div_eq_inv_mul]

omit [MeasurableSingletonClass β] in
/-- A row with a positive entry and finite entries normalizes to a
probability measure. -/
theorem isMarkovKernel_ofWeights {w : α → β → ℝ≥0∞}
    (h0 : ∀ a, ∃ b, w a b ≠ 0) (htop : ∀ a b, w a b ≠ ∞) :
    IsMarkovKernel (ofWeights w) := by
  refine ⟨fun a => ⟨?_⟩⟩
  have hZ0 : (∑ b, w a b) ≠ 0 := by
    obtain ⟨b, hb⟩ := h0 a
    exact fun h => hb (Finset.sum_eq_zero_iff.mp h b (Finset.mem_univ b))
  have hZtop : (∑ b, w a b) ≠ ∞ := ENNReal.sum_ne_top.mpr fun b _ => htop a b
  show ((∑ b, w a b)⁻¹ • ∑ b, w a b • Measure.dirac b) Set.univ = 1
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel hZ0 hZtop

/-- Row-preference in a weight kernel reduces to weight comparison; the
normalization cancels. -/
theorem ofWeights_real_singleton_lt_iff {w : α → β → ℝ≥0∞} (a : α)
    (h0 : (∑ b, w a b) ≠ 0) (htop : (∑ b, w a b) ≠ ∞) {b₁ b₂ : β} :
    (ofWeights w a).real {b₁} < (ofWeights w a).real {b₂} ↔ w a b₁ < w a b₂ := by
  have hb : ∀ b, w a b ≠ ∞ := fun b => ENNReal.sum_ne_top.mp htop b (Finset.mem_univ b)
  rw [measureReal_def, measureReal_def, ofWeights_apply_singleton,
    ofWeights_apply_singleton,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hb b₁) h0)
      (ENNReal.div_ne_top (hb b₂) h0),
    ENNReal.div_lt_div_iff_left h0 htop]

omit [MeasurableSingletonClass β] in
/-- Weight-kernel rows are subprobabilities: normalization gives mass 1 on
positive finite total weight and 0 otherwise. -/
theorem ofWeights_apply_univ_le_one (w : α → β → ℝ≥0∞) (a : α) :
    ofWeights w a Set.univ ≤ 1 := by
  show ((∑ b, w a b)⁻¹ • ∑ b, w a b • Measure.dirac b) Set.univ ≤ 1
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rcases eq_or_ne (∑ b, w a b) 0 with h0 | h0
  · simp [h0]
  · rcases eq_or_ne (∑ b, w a b) ∞ with htop | htop
    · simp [htop]
    · rw [ENNReal.inv_mul_cancel h0 htop]

instance (w : α → β → ℝ≥0∞) : IsFiniteKernel (ofWeights w) :=
  ⟨⟨1, ENNReal.one_lt_top, ofWeights_apply_univ_le_one w⟩⟩

end ProbabilityTheory.Kernel
