/-
# Softmax Function: Basic Properties

Formalization of the softmax function and its mathematical properties,
following Franke & Degen "The softmax function: Properties, motivation,
and interpretation."

## Definition

The softmax function maps scores s = (s₁, ..., sₙ) to probabilities:

  softmax(s; α)ᵢ = exp(α · sᵢ) / Σⱼ exp(α · sⱼ)

where α is the "rationality" or "inverse temperature" parameter.

## Key Properties

- **Fact 1**: Output is a valid probability distribution
- **Fact 2**: Odds determined by score differences: pᵢ/pⱼ = exp(α(sᵢ - sⱼ))
- **Fact 3**: Binary case reduces to logistic function
- **Fact 6**: Translation invariant: softmax(s + c) = softmax(s)
- **Fact 8**: Scale trading: softmax(a·s, α/a) = softmax(s, α)

## References

- Franke & Degen. The softmax function: Properties, motivation, and interpretation.
- Luce (1959). Individual choice behavior.
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field

namespace Softmax

open Real BigOperators Finset

variable {ι : Type*} [Fintype ι]

-- ============================================================================
-- SECTION 1: Definition
-- ============================================================================

/-- The softmax function maps a score vector to a probability distribution.

Given scores s : ι → ℝ and rationality parameter α : ℝ,

  softmax(s, α)ᵢ = exp(α · sᵢ) / Σⱼ exp(α · sⱼ)
-/
noncomputable def softmax (s : ι → ℝ) (α : ℝ) : ι → ℝ :=
  fun i => exp (α * s i) / ∑ j : ι, exp (α * s j)

/-- The partition function (normalizing constant) Z = Σⱼ exp(α · sⱼ) -/
noncomputable def partitionFn (s : ι → ℝ) (α : ℝ) : ℝ :=
  ∑ j : ι, exp (α * s j)

/-- Log-sum-exp: log of partition function -/
noncomputable def logSumExp (s : ι → ℝ) (α : ℝ) : ℝ :=
  log (∑ j : ι, exp (α * s j))

-- ============================================================================
-- SECTION 2: Basic Properties (Fact 1)
-- ============================================================================

/-- The partition function is always positive. -/
theorem partitionFn_pos [Nonempty ι] (s : ι → ℝ) (α : ℝ) :
    0 < partitionFn s α := by
  apply Finset.sum_pos
  · intro i _
    exact exp_pos _
  · exact Finset.univ_nonempty

theorem partitionFn_ne_zero [Nonempty ι] (s : ι → ℝ) (α : ℝ) :
    partitionFn s α ≠ 0 :=
  ne_of_gt (partitionFn_pos s α)

/-- Each softmax probability is positive. (Fact 1, part 1) -/
theorem softmax_pos [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    0 < softmax s α i := by
  simp only [softmax]
  exact div_pos (exp_pos _) (partitionFn_pos s α)

/-- Softmax probabilities sum to 1. (Fact 1, part 2) -/
theorem softmax_sum_eq_one [Nonempty ι] (s : ι → ℝ) (α : ℝ) :
    ∑ i : ι, softmax s α i = 1 := by
  simp only [softmax]
  have h : ∑ x : ι, exp (α * s x) / ∑ j : ι, exp (α * s j) =
           (∑ x : ι, exp (α * s x)) / ∑ j : ι, exp (α * s j) := by
    rw [Finset.sum_div]
  rw [h]
  exact div_self (partitionFn_ne_zero s α)

/-- Softmax is non-negative. -/
theorem softmax_nonneg [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    0 ≤ softmax s α i :=
  le_of_lt (softmax_pos s α i)

/-- Softmax is at most 1. -/
theorem softmax_le_one [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    softmax s α i ≤ 1 := by
  have h := softmax_sum_eq_one s α
  have hpos : ∀ j, 0 ≤ softmax s α j := fun j => softmax_nonneg s α j
  calc softmax s α i
      ≤ ∑ j : ι, softmax s α j := Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ i)
    _ = 1 := h

-- ============================================================================
-- SECTION 3: Odds from Differences (Fact 2 - THE KEY PROPERTY)
-- ============================================================================

/-- **Fact 2**: Odds are determined by score differences.

  pᵢ/pⱼ = exp(α(sᵢ - sⱼ))

This is the most important property of softmax.
-/
theorem softmax_odds [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i j : ι) :
    softmax s α i / softmax s α j = exp (α * (s i - s j)) := by
  simp only [softmax]
  have hZ : (∑ k : ι, exp (α * s k)) ≠ 0 := partitionFn_ne_zero s α
  have hj : exp (α * s j) ≠ 0 := ne_of_gt (exp_pos _)
  field_simp
  have key : α * s j + α * (s i - s j) = α * s i := by ring
  rw [← exp_add, key]

/-- Log-odds equal scaled score difference. -/
theorem log_softmax_odds [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i j : ι) :
    log (softmax s α i / softmax s α j) = α * (s i - s j) := by
  rw [softmax_odds, log_exp]

/-- Ratio form of Fact 2. -/
theorem softmax_ratio [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i j : ι) :
    softmax s α i = softmax s α j * exp (α * (s i - s j)) := by
  have h := softmax_odds s α i j
  have hne : softmax s α j ≠ 0 := ne_of_gt (softmax_pos s α j)
  field_simp at h ⊢
  linarith [h]

-- ============================================================================
-- SECTION 4: Binary Case = Logistic (Fact 3)
-- ============================================================================

/-- The logistic (sigmoid) function. -/
noncomputable def logistic (x : ℝ) : ℝ := 1 / (1 + exp (-x))

/-- **Fact 3**: For n = 2, softmax reduces to logistic.

  softmax(s, α)₀ = 1 / (1 + exp(-α(s₀ - s₁))) = σ(α(s₀ - s₁))
-/
theorem softmax_binary (s : Fin 2 → ℝ) (α : ℝ) :
    softmax s α 0 = logistic (α * (s 0 - s 1)) := by
  simp only [softmax, logistic, Fin.sum_univ_two]
  have key : α * s 0 + (-(α * (s 0 - s 1))) = α * s 1 := by ring
  have h : exp (α * s 0) + exp (α * s 1) =
           exp (α * s 0) * (1 + exp (-(α * (s 0 - s 1)))) := by
    rw [mul_add, mul_one, ← exp_add, key]
  rw [h, ← div_div, div_self (ne_of_gt (exp_pos _))]

-- ============================================================================
-- SECTION 5: Translation Invariance (Fact 6)
-- ============================================================================

/-- **Fact 6**: Softmax is invariant under translation.

Adding a constant to all scores doesn't change the output.
-/
theorem softmax_add_const (s : ι → ℝ) (α c : ℝ) :
    softmax (fun i => s i + c) α = softmax s α := by
  funext i
  simp only [softmax]
  have hexp : ∀ j, exp (α * (s j + c)) = exp (α * s j) * exp (α * c) := by
    intro j
    rw [← exp_add]
    ring_nf
  simp_rw [hexp, ← Finset.sum_mul]
  rw [mul_div_mul_right _ _ (ne_of_gt (exp_pos _))]

-- ============================================================================
-- SECTION 6: Scale Trading (Fact 8)
-- ============================================================================

/-- **Fact 8**: Multiplicative scaling can be absorbed into α.

  softmax(a·s, α/a) = softmax(s, α)  for a ≠ 0
-/
theorem softmax_scale (s : ι → ℝ) (α a : ℝ) (ha : a ≠ 0) :
    softmax (fun i => a * s i) (α / a) = softmax s α := by
  funext i
  simp only [softmax]
  congr 1
  · congr 1
    field_simp
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    field_simp

-- ============================================================================
-- SECTION 7: Monotonicity Properties
-- ============================================================================

/-- Higher scores get higher probabilities (for α > 0). -/
theorem softmax_mono [Nonempty ι] (s : ι → ℝ) {α : ℝ} (hα : 0 < α) (i j : ι)
    (hij : s i ≤ s j) :
    softmax s α i ≤ softmax s α j := by
  simp only [softmax]
  apply div_le_div_of_nonneg_right _ (le_of_lt (partitionFn_pos s α))
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left hij (le_of_lt hα)

/-- Strict monotonicity. -/
theorem softmax_strict_mono [Nonempty ι] (s : ι → ℝ) {α : ℝ} (hα : 0 < α)
    (i j : ι) (hij : s i < s j) :
    softmax s α i < softmax s α j := by
  simp only [softmax]
  apply div_lt_div_of_pos_right _ (partitionFn_pos s α)
  apply exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_left hij hα

-- ============================================================================
-- SECTION 8: Special Values of α
-- ============================================================================

/-- At α = 0, softmax is uniform. -/
theorem softmax_zero [Nonempty ι] (s : ι → ℝ) :
    softmax s 0 = fun _ => 1 / (Fintype.card ι : ℝ) := by
  funext i
  simp only [softmax, zero_mul, exp_zero, Finset.sum_const, Finset.card_univ,
             nsmul_eq_mul, mul_one]

/-- For α < 0, lower scores get higher probabilities. -/
theorem softmax_neg_mono [Nonempty ι] (s : ι → ℝ) {α : ℝ} (hα : α < 0) (i j : ι)
    (hij : s i ≤ s j) :
    softmax s α j ≤ softmax s α i := by
  simp only [softmax]
  apply div_le_div_of_nonneg_right _ (le_of_lt (partitionFn_pos s α))
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hij (le_of_lt hα)

-- ============================================================================
-- SECTION 9: Convenience Definitions
-- ============================================================================

/-- Softmax with default α = 1. -/
noncomputable def softmax1 (s : ι → ℝ) : ι → ℝ := softmax s 1

/-- Temperature form: τ = 1/α. -/
noncomputable def softmaxTemp (s : ι → ℝ) (τ : ℝ) : ι → ℝ :=
  softmax s (1 / τ)

end Softmax
