/-
# RSA/Core/CombinedUtility.lean

Combined utility models for trading off multiple objectives.

## Overview

Many RSA models involve trading off two (or more) utility components:
- **Sumers et al. (2023)**: truthfulness vs relevance
- **PRIOR-PQ (Hawkins et al. 2025)**: informativity vs action-relevance
- **Yoon et al. (2020)**: informativity vs social utility

This module provides a unified framework for such combined utility models.

## Key Concepts

**Combined Utility**: U_combined = (1-λ)·U_A + λ·U_B - cost

- λ = 0: Pure U_A (e.g., pure truthfulness)
- λ = 1: Pure U_B (e.g., pure relevance)
- λ ∈ (0,1): Weighted combination

## References

- Sumers et al. (2023). Reconciling truthfulness and relevance.
- Hawkins et al. (2025). Relevant answers to polar questions.
- Yoon et al. (2020). Polite speech emerges from competing social goals.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace RSA.CombinedUtility


/-- Combined utility: weighted interpolation of two utility components.

U_combined = (1-λ)·U_A + λ·U_B - cost

This is the standard form used across multiple RSA papers:
- Sumers: U_A = truthfulness, U_B = relevance
- PRIOR-PQ: U_A = informativity, U_B = action-relevance
- Yoon: U_A = informativity, U_B = social utility
-/
def combined (lam : ℚ) (utilA utilB : ℚ) (cost : ℚ := 0) : ℚ :=
  (1 - lam) * utilA + lam * utilB - cost

/-- Alternative parameterization with explicit weights -/
def combinedWeighted (wA wB : ℚ) (utilA utilB : ℚ) (cost : ℚ := 0) : ℚ :=
  wA * utilA + wB * utilB - cost


/-- Combined utility equals U_A when λ = 0 -/
theorem combined_at_zero (utilA utilB : ℚ) :
    combined 0 utilA utilB = utilA := by
  unfold combined
  ring

/-- Combined utility equals U_B when λ = 1 -/
theorem combined_at_one (utilA utilB : ℚ) :
    combined 1 utilA utilB = utilB := by
  unfold combined
  ring

/-- Both endpoints in one theorem -/
theorem combined_endpoints (utilA utilB : ℚ) :
    combined 0 utilA utilB = utilA ∧
    combined 1 utilA utilB = utilB := by
  constructor
  · exact combined_at_zero utilA utilB
  · exact combined_at_one utilA utilB

/-- Cost is additive -/
theorem combined_cost_additive (lam : ℚ) (utilA utilB cost : ℚ) :
    combined lam utilA utilB cost =
    combined lam utilA utilB 0 - cost := by
  unfold combined
  ring


/-- Combined utility increases with U_A when λ < 1 -/
theorem combined_mono_A (lam : ℚ) (hlam : lam < 1) (utilA utilA' utilB : ℚ)
    (h : utilA < utilA') :
    combined lam utilA utilB < combined lam utilA' utilB := by
  unfold combined
  have hw : 0 < 1 - lam := by linarith
  have : (1 - lam) * utilA < (1 - lam) * utilA' := mul_lt_mul_of_pos_left h hw
  linarith

/-- Combined utility increases with U_B when λ > 0 -/
theorem combined_mono_B (lam : ℚ) (hlam : 0 < lam) (utilA utilB utilB' : ℚ)
    (h : utilB < utilB') :
    combined lam utilA utilB < combined lam utilA utilB' := by
  unfold combined
  have : lam * utilB < lam * utilB' := mul_lt_mul_of_pos_left h hlam
  linarith


/-- Combined utility is a convex combination when λ ∈ [0,1] -/
theorem combined_convex (lam : ℚ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (utilA utilB : ℚ) :
    min utilA utilB ≤ combined lam utilA utilB 0 ∧
    combined lam utilA utilB 0 ≤ max utilA utilB := by
  unfold combined; simp only [sub_zero]
  constructor
  · rcases le_total utilA utilB with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  · rcases le_total utilA utilB with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith

/-- Midpoint property -/
theorem combined_midpoint (utilA utilB : ℚ) :
    combined (1/2) utilA utilB = (utilA + utilB) / 2 := by
  unfold combined
  ring


/-- When U_A > U_B, lower λ gives higher combined utility -/
theorem lower_lambda_when_A_dominates (lam1 lam2 : ℚ)
    (h : lam1 < lam2) (utilA utilB : ℚ) (hAB : utilA > utilB) :
    combined lam1 utilA utilB > combined lam2 utilA utilB := by
  unfold combined
  have hdiff : utilA - utilB > 0 := by linarith
  have : lam1 * (utilA - utilB) < lam2 * (utilA - utilB) :=
    mul_lt_mul_of_pos_right h hdiff
  linarith

/-- When U_B > U_A, higher λ gives higher combined utility -/
theorem higher_lambda_when_B_dominates (lam1 lam2 : ℚ)
    (h : lam1 < lam2) (utilA utilB : ℚ) (hBA : utilB > utilA) :
    combined lam1 utilA utilB < combined lam2 utilA utilB := by
  unfold combined
  have hdiff : utilB - utilA > 0 := by linarith
  have : lam1 * (utilB - utilA) < lam2 * (utilB - utilA) :=
    mul_lt_mul_of_pos_right h hdiff
  linarith


/-- Structure for MLE-fitted λ parameters -/
structure MLEFit where
  /-- Fitted λ value -/
  lam : ℚ
  /-- Condition name -/
  condition : String
  /-- Log-likelihood (approximate) -/
  logLikelihood : ℚ := 0

/-- Compare two conditions by their λ values -/
def moreRelevanceOriented (fit1 fit2 : MLEFit) : Bool :=
  fit1.lam > fit2.lam

/-- Compare two conditions by their λ values -/
def moreTruthOriented (fit1 fit2 : MLEFit) : Bool :=
  fit1.lam < fit2.lam


/-- Combined utility with three components (for richer models).

U = w_A · U_A + w_B · U_B + w_C · U_C - cost

Used when there are three competing objectives.
-/
def combined3 (wA wB wC : ℚ) (utilA utilB utilC : ℚ) (cost : ℚ := 0) : ℚ :=
  wA * utilA + wB * utilB + wC * utilC - cost

/-- Normalize weights to sum to 1 -/
def normalizeWeights3 (wA wB wC : ℚ) : ℚ × ℚ × ℚ :=
  let total := wA + wB + wC
  if total == 0 then (0, 0, 0)
  else (wA / total, wB / total, wC / total)

end RSA.CombinedUtility
