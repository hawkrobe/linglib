import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.UniformOn

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

* `ProbabilityTheory.Kernel.ofWeights_apply_singleton` — `w a b / ∑ b', w a b'`;
  `ofWeights_apply_finset`, `ofWeights_real_setOf` for finite events.
* `ProbabilityTheory.Kernel.ofWeights_real_singleton_lt_iff` — row preference is weight
  comparison.
* `ProbabilityTheory.Kernel.ofWeights_uniformOn_mul_uniformOn` — the product of two uniform
  experts is uniform on their agreement set.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {β : Type*} [MeasurableSpace β] [Fintype β] [MeasurableSingletonClass β]

/-- A finite sum of scaled Dirac measures evaluates at a singleton to its weight. -/
theorem sum_smul_dirac_apply_singleton (w : β → ℝ≥0∞) (b : β) :
    (∑ b', w b' • dirac b') {b} = w b := by
  rw [finsetSum_apply,
    Finset.sum_eq_single_of_mem b (Finset.mem_univ b) fun b' _ hb' => by
      rw [smul_apply, smul_eq_mul, dirac_apply' _ (.singleton b),
        Set.indicator_of_notMem (fun h => hb' (Set.mem_singleton_iff.mp h)), mul_zero],
    smul_apply, smul_eq_mul, dirac_apply' _ (.singleton b),
    Set.indicator_of_mem (Set.mem_singleton b), Pi.one_apply, mul_one]

end MeasureTheory.Measure

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
  show ((∑ b', w a b')⁻¹ • ∑ b', w a b' • Measure.dirac b') {b} = _
  rw [Measure.smul_apply, smul_eq_mul, Measure.sum_smul_dirac_apply_singleton,
    ENNReal.div_eq_inv_mul]

/-- The mass of a finite event under a weight-kernel row. -/
theorem ofWeights_apply_finset (w : α → β → ℝ≥0∞) (a : α) (E : Finset β) :
    ofWeights w a ↑E = (∑ b ∈ E, w a b) / ∑ b, w a b := by
  rw [← sum_measure_singleton, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by rw [ofWeights_apply_singleton, div_eq_mul_inv]

/-- The real mass of a finite event under a weight-kernel row with finite weights. -/
theorem ofWeights_real_finset (w : α → β → ℝ≥0∞) (a : α) (hw : ∀ b, w a b ≠ ∞) (E : Finset β) :
    (ofWeights w a).real ↑E = (∑ b ∈ E, (w a b).toReal) / ∑ b, (w a b).toReal := by
  rw [measureReal_def, ofWeights_apply_finset, ENNReal.toReal_div,
    ENNReal.toReal_sum fun b _ => hw b, ENNReal.toReal_sum fun b _ => hw b]

/-- The real mass of a decidable event under a weight-kernel row with finite weights. -/
theorem ofWeights_real_setOf (w : α → β → ℝ≥0∞) (a : α) (hw : ∀ b, w a b ≠ ∞) (p : β → Prop)
    [DecidablePred p] :
    (ofWeights w a).real {b | p b} = (∑ b with p b, (w a b).toReal) / ∑ b, (w a b).toReal := by
  rw [show {b | p b} = (↑(Finset.univ.filter p) : Set β) by ext b; simp,
    ofWeights_real_finset w a hw]

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

omit [Countable α] [MeasurableSingletonClass α] [Fintype β] in
/-- Two uniform experts weight a point by `(#A · #B)⁻¹` on their agreement set and `0` off it. -/
theorem uniformOn_mul_uniformOn_apply_singleton [DecidableEq β] (A B : Finset β) (b : β) :
    uniformOn ↑A {b} * uniformOn ↑B {b} =
      if b ∈ A ∩ B then ((A.card : ℝ≥0∞) * B.card)⁻¹ else 0 := by
  rw [← Finset.coe_singleton, uniformOn_apply_finset, uniformOn_apply_finset]
  by_cases hA : b ∈ A <;> by_cases hB : b ∈ B <;>
    simp [Finset.inter_singleton_of_mem, Finset.inter_singleton_of_notMem, hA, hB,
      ENNReal.mul_inv, div_eq_mul_inv]

/-- Product of Experts of two uniform experts: the row is uniform on their agreement set, and
collapses to the zero measure when they agree nowhere. -/
theorem ofWeights_uniformOn_mul_uniformOn [DecidableEq β] (A B : α → Finset β) (a : α) :
    ofWeights (fun a b => uniformOn ↑(A a) {b} * uniformOn ↑(B a) {b}) a =
      uniformOn (↑(A a ∩ B a) : Set β) := by
  refine Measure.ext_of_singleton fun b => ?_
  rw [ofWeights_apply_singleton]
  simp only [uniformOn_mul_uniformOn_apply_singleton, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.coe_singleton, uniformOn_apply_finset]
  by_cases hb : b ∈ A a ∩ B a
  · have hK : ((A a).card : ℝ≥0∞) * (B a).card ≠ 0 := by
      have := Finset.mem_inter.mp hb
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨b, this.1⟩).ne')
        (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨b, this.2⟩).ne')
    have hK' : ((A a).card : ℝ≥0∞) * (B a).card ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
    rw [if_pos hb, Finset.inter_singleton_of_mem hb, Finset.card_singleton, Nat.cast_one,
      ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr hK))
        (Or.inl (ENNReal.natCast_ne_top _)), inv_inv, mul_assoc,
      ENNReal.mul_inv_cancel hK hK', mul_one, one_div]
  · rw [if_neg hb, Finset.inter_singleton_of_notMem hb, Finset.card_empty, Nat.cast_zero,
      ENNReal.zero_div, ENNReal.zero_div]

end ProbabilityTheory.Kernel
