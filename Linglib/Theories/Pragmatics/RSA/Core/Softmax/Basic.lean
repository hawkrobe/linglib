import Linglib.Core.RationalAction

/-!
# Softmax Function: Basic Properties (Re-export)

This file re-exports softmax definitions and theorems from `Core.RationalAction`,
where they now live as part of the unified rational action theory.

Downstream files that import this module continue to work unchanged.
-/

namespace Softmax

open Core

-- Re-export definitions (abbrev for definitional transparency)
noncomputable abbrev softmax {ι : Type*} [Fintype ι] := @Core.softmax ι
noncomputable abbrev partitionFn {ι : Type*} [Fintype ι] := @Core.partitionFn ι
noncomputable abbrev logSumExp {ι : Type*} [Fintype ι] := @Core.logSumExp ι
noncomputable abbrev logistic := Core.logistic
noncomputable abbrev softmax1 {ι : Type*} [Fintype ι] := @Core.softmax1 ι
noncomputable abbrev softmaxTemp {ι : Type*} [Fintype ι] := @Core.softmaxTemp ι
noncomputable abbrev klFinite {ι : Type*} [Fintype ι] := @Core.klFinite ι

-- Re-export theorems as aliases
variable {ι : Type*} [Fintype ι]

theorem partitionFn_pos [Nonempty ι] (s : ι → ℝ) (α : ℝ) :
    0 < partitionFn s α := Core.partitionFn_pos s α

theorem partitionFn_ne_zero [Nonempty ι] (s : ι → ℝ) (α : ℝ) :
    partitionFn s α ≠ 0 := Core.partitionFn_ne_zero s α

theorem softmax_pos [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    0 < softmax s α i := Core.softmax_pos s α i

theorem softmax_sum_eq_one [Nonempty ι] (s : ι → ℝ) (α : ℝ) :
    ∑ i : ι, softmax s α i = 1 := Core.softmax_sum_eq_one s α

theorem softmax_nonneg [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    0 ≤ softmax s α i := Core.softmax_nonneg s α i

theorem softmax_le_one [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    softmax s α i ≤ 1 := Core.softmax_le_one s α i

theorem softmax_odds [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i j : ι) :
    softmax s α i / softmax s α j = Real.exp (α * (s i - s j)) :=
  Core.softmax_odds s α i j

theorem log_softmax_odds [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i j : ι) :
    Real.log (softmax s α i / softmax s α j) = α * (s i - s j) :=
  Core.log_softmax_odds s α i j

theorem softmax_ratio [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i j : ι) :
    softmax s α i = softmax s α j * Real.exp (α * (s i - s j)) :=
  Core.softmax_ratio s α i j

theorem softmax_binary (s : Fin 2 → ℝ) (α : ℝ) :
    softmax s α 0 = logistic (α * (s 0 - s 1)) :=
  Core.softmax_binary s α

theorem softmax_add_const (s : ι → ℝ) (α c : ℝ) :
    softmax (λ i => s i + c) α = softmax s α :=
  Core.softmax_add_const s α c

theorem softmax_scale (s : ι → ℝ) (α a : ℝ) (ha : a ≠ 0) :
    softmax (λ i => a * s i) (α / a) = softmax s α :=
  Core.softmax_scale s α a ha

theorem softmax_mono [Nonempty ι] (s : ι → ℝ) {α : ℝ} (hα : 0 < α) (i j : ι)
    (hij : s i ≤ s j) :
    softmax s α i ≤ softmax s α j :=
  Core.softmax_mono s hα i j hij

theorem softmax_strict_mono [Nonempty ι] (s : ι → ℝ) {α : ℝ} (hα : 0 < α)
    (i j : ι) (hij : s i < s j) :
    softmax s α i < softmax s α j :=
  Core.softmax_strict_mono s hα i j hij

theorem softmax_zero [Nonempty ι] (s : ι → ℝ) :
    softmax s 0 = λ _ => 1 / (Fintype.card ι : ℝ) :=
  Core.softmax_zero s

theorem softmax_neg_mono [Nonempty ι] (s : ι → ℝ) {α : ℝ} (hα : α < 0) (i j : ι)
    (hij : s i ≤ s j) :
    softmax s α j ≤ softmax s α i :=
  Core.softmax_neg_mono s hα i j hij

theorem log_softmax [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    Real.log (softmax s α i) = α * s i - Real.log (partitionFn s α) :=
  Core.log_softmax s α i

theorem softmax_exponential_family (s : ι → ℝ) (α : ℝ) (i : ι) [Nonempty ι] :
    softmax s α i = Real.exp (α * s i - logSumExp s α) :=
  Core.softmax_exponential_family s α i

theorem kl_nonneg [Nonempty ι] {p q : ι → ℝ}
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    0 ≤ klFinite p q :=
  Core.kl_nonneg' hp_nonneg hq_pos hp_sum hq_sum

theorem gibbs_variational [Nonempty ι] (s : ι → ℝ) (α : ℝ) (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    (∑ i, Real.negMulLog (p i)) + α * ∑ i, p i * s i ≤
    (∑ i, Real.negMulLog (softmax s α i)) + α * ∑ i, softmax s α i * s i :=
  Core.gibbs_variational s α p hp_nonneg hp_sum

theorem bayesian_maximizes_expected_log [Nonempty ι] (w : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum_pos : 0 < ∑ i, w i)
    (L : ι → ℝ) (hL_pos : ∀ i, 0 < L i) (hL_sum : ∑ i, L i = 1) :
    ∑ i, (w i / ∑ j, w j) * Real.log (L i) ≤
    ∑ i, (w i / ∑ j, w j) * Real.log (w i / ∑ j, w j) := by
  have h := Core.bayesian_maximizes w hw_nonneg hw_sum_pos L hL_pos hL_sum
  -- h : ∑ i, w i * log (L i) ≤ ∑ i, w i * log (w i / ∑ j, w j)
  -- Divide both sides by C = ∑ j, w j > 0
  have hC_pos := hw_sum_pos
  have hC_ne : (∑ j, w j) ≠ 0 := ne_of_gt hC_pos
  -- Rewrite: ∑ (w i / C) * f i = (1 / C) * ∑ w i * f i
  have factor : ∀ (f : ι → ℝ),
      ∑ i, (w i / ∑ j, w j) * f i = (∑ i, w i * f i) / ∑ j, w j := by
    intro f
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [div_mul_eq_mul_div]
  rw [factor, factor]
  exact div_le_div_of_nonneg_right h (le_of_lt hC_pos)

end Softmax
