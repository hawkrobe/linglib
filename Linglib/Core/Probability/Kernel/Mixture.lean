import Linglib.Core.Probability.Kernel.OfWeights

/-!
# Mixtures of kernels

`ProbabilityTheory.Kernel.mixture c κ` is the kernel whose row at `a` is the weighted sum
`∑ i, c i • κ i a` of the rows of a finite family of kernels: the family averaged over a latent
index the target does not see. Its rows are finite when the weights are finite and the members
are finite kernels.

## Main definitions

* `ProbabilityTheory.Kernel.mixture` — the weighted sum of a finite family of kernels.

## Main results

* `ProbabilityTheory.Kernel.mixture_apply'`, `ProbabilityTheory.Kernel.mixture_real` — a row at
  an event, in `ℝ≥0∞` and on reals.
* `ProbabilityTheory.Kernel.mixture_apply_ne_zero_iff` — a row has mass on an event exactly
  when some positively weighted member does.
* `ProbabilityTheory.Kernel.isFiniteKernel_mixture` — finiteness under finite weights.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable α]
  [MeasurableSingletonClass α] [Fintype ι]

/-- The mixture of a finite family of kernels by weights `c`: row `a` is `∑ i, c i • κ i a`. -/
noncomputable def mixture (c : ι → ℝ≥0∞) (κ : ι → Kernel α β) : Kernel α β :=
  ofFunOfCountable λ a => ∑ i, c i • κ i a

theorem mixture_apply (c : ι → ℝ≥0∞) (κ : ι → Kernel α β) (a : α) :
    mixture c κ a = ∑ i, c i • κ i a := rfl

/-- A row of a mixture at an event is the weighted sum of the members' masses. -/
theorem mixture_apply' (c : ι → ℝ≥0∞) (κ : ι → Kernel α β) (a : α) (s : Set β) :
    mixture c κ a s = ∑ i, c i * κ i a s := by
  rw [mixture_apply, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- A row of a mixture has mass on an event exactly when some positively weighted member
does. -/
theorem mixture_apply_ne_zero_iff (c : ι → ℝ≥0∞) (κ : ι → Kernel α β) (a : α) (s : Set β) :
    mixture c κ a s ≠ 0 ↔ ∃ i, c i ≠ 0 ∧ κ i a s ≠ 0 := by
  simp only [ne_eq, mixture_apply', Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies,
    mul_eq_zero, not_forall, not_or]

/-- A row of a mixture of finite kernels with finite weights at an event, on reals. -/
theorem mixture_real (c : ι → ℝ≥0∞) (κ : ι → Kernel α β) [∀ i, IsFiniteKernel (κ i)]
    (hc : ∀ i, c i ≠ ∞) (a : α) (s : Set β) :
    (mixture c κ a).real s = ∑ i, (c i).toReal * (κ i a).real s := by
  rw [measureReal_def, mixture_apply',
    ENNReal.toReal_sum λ i _ => ENNReal.mul_ne_top (hc i) (measure_ne_top _ _)]
  simp only [ENNReal.toReal_mul, measureReal_def]

/-- A mixture of finite kernels with finite weights is a finite kernel. -/
theorem isFiniteKernel_mixture (c : ι → ℝ≥0∞) (κ : ι → Kernel α β) [∀ i, IsFiniteKernel (κ i)]
    (hc : ∀ i, c i ≠ ∞) : IsFiniteKernel (mixture c κ) :=
  ⟨⟨∑ i, c i * (κ i).bound,
    ENNReal.sum_lt_top.mpr λ i _ => (ENNReal.mul_ne_top (hc i) (κ i).bound_lt_top.ne).lt_top,
    λ a => by
      rw [mixture_apply']
      exact Finset.sum_le_sum λ i _ => mul_le_mul' le_rfl ((κ i).measure_le_bound a _)⟩⟩

end ProbabilityTheory.Kernel
