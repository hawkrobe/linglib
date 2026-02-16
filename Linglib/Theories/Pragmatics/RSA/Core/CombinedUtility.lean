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
import Mathlib.Tactic.FieldSimp

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

-- ============================================================
-- Goal-Oriented Utility (Barnett et al. 2022, Cummins & Franke 2021)
-- ============================================================

/-- Goal-oriented speaker utility: U_epi + β · U_goal.

This parameterization naturally models argumentative/persuasive speakers:
- Barnett et al. (2022): U_goal = ln P_L0(w*|u), β controls persuasive bias
- Cummins & Franke (2021): U_goal = argStr(u, G), β → ∞ for pure argStr speaker

Equivalent to combinedWeighted(1, β, U_epi, U_goal). The parameter β controls
the cooperativity spectrum (Cummins 2025):
- β = 0: fully cooperative (standard RSA)
- 0 < β < ∞: partially argumentative
- β → ∞: purely argumentative -/
def goalOrientedUtility (uEpi uGoal : ℚ) (β : ℚ) : ℚ :=
  uEpi + β * uGoal

/-- Goal-oriented utility = combinedWeighted(1, β, ...) -/
theorem goalOriented_eq_combinedWeighted (uEpi uGoal β : ℚ) :
    goalOrientedUtility uEpi uGoal β = combinedWeighted 1 β uEpi uGoal := by
  unfold goalOrientedUtility combinedWeighted; ring

/-- At β=0, goal-oriented utility reduces to pure epistemic (cooperative RSA) -/
theorem goalOriented_cooperative (uEpi uGoal : ℚ) :
    goalOrientedUtility uEpi uGoal 0 = uEpi := by
  unfold goalOrientedUtility; ring

/-- Higher β increases utility of goal-supporting utterances (U_goal > 0) -/
theorem goalOriented_mono_beta (uEpi uGoal : ℚ) (β₁ β₂ : ℚ)
    (hβ : β₁ < β₂) (hGoal : 0 < uGoal) :
    goalOrientedUtility uEpi uGoal β₁ < goalOrientedUtility uEpi uGoal β₂ := by
  unfold goalOrientedUtility
  have : β₁ * uGoal < β₂ * uGoal := mul_lt_mul_of_pos_right hβ hGoal
  linarith

/-- Negative U_goal DECREASES utility as β increases — the speaker is
penalized for utterances that argue AGAINST the goal. -/
theorem goalOriented_antimono_beta_neg (uEpi uGoal : ℚ) (β₁ β₂ : ℚ)
    (hβ : β₁ < β₂) (hGoal : uGoal < 0) :
    goalOrientedUtility uEpi uGoal β₂ < goalOrientedUtility uEpi uGoal β₁ := by
  unfold goalOrientedUtility
  have : β₂ * uGoal < β₁ * uGoal := by nlinarith
  linarith


-- ============================================================
-- Reparameterization Bridge: Additive (β) ↔ Convex (λ)
-- ============================================================

/-- Convert additive bias parameter β ∈ [0,∞) to convex weight λ ∈ [0,1).

β/(1+β) maps [0,∞) → [0,1): β=0 ↦ 0, β=1 ↦ 1/2, β→∞ ↦ 1.

This bridges `goalOrientedUtility` (additive: U + β·V) and `combined`
(convex: (1-λ)·U + λ·V). -/
def betaToLam (β : ℚ) : ℚ :=
  β / (1 + β)

/-- Convert convex weight λ ∈ [0,1) back to additive bias parameter β.

λ/(1-λ) maps [0,1) → [0,∞): λ=0 ↦ 0, λ=1/2 ↦ 1. -/
def lamToBeta (lam : ℚ) : ℚ :=
  lam / (1 - lam)

/-- Round-trip: betaToLam (lamToBeta λ) = λ for λ ∈ [0,1). -/
theorem betaToLam_lamToBeta_inv (lam : ℚ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    betaToLam (lamToBeta lam) = lam := by
  unfold betaToLam lamToBeta
  have h1ne : (1 : ℚ) - lam ≠ 0 := by linarith
  field_simp [h1ne]; ring

/-- Round-trip: lamToBeta (betaToLam β) = β for β ≥ 0. -/
theorem lamToBeta_betaToLam_inv (β : ℚ) (hβ : 0 ≤ β) :
    lamToBeta (betaToLam β) = β := by
  unfold lamToBeta betaToLam
  have h1ne : (1 : ℚ) + β ≠ 0 := by linarith
  field_simp [h1ne]; ring

/-- The key bridge: goalOrientedUtility = (1+β) · combined(β/(1+β), ...).

`U_epi + β·U_goal = (1+β) · ((1 - β/(1+β))·U_epi + β/(1+β)·U_goal)`

Scaling by (1+β) > 0 preserves utterance rankings, so the additive and
convex forms are strategically equivalent. -/
theorem goalOriented_eq_scaled_combined (uEpi uGoal β : ℚ) (hβ : 0 ≤ β) :
    goalOrientedUtility uEpi uGoal β =
    (1 + β) * combined (betaToLam β) uEpi uGoal := by
  unfold goalOrientedUtility combined betaToLam
  have h1ne : (1 : ℚ) + β ≠ 0 := by linarith
  field_simp [h1ne]
  ring

/-- Utterance ranking equivalence: for β ≥ 0, goalOrientedUtility and combined
rank any two utility pairs the same way (scaling by (1+β) > 0 preserves
ordering).

If U_epi + β·U_goal > U_epi' + β·U_goal', then
combined(β/(1+β), U_epi, U_goal) > combined(β/(1+β), U_epi', U_goal'). -/
theorem goalOriented_same_ranking (uEpi uGoal uEpi' uGoal' β : ℚ) (hβ : 0 ≤ β)
    (hord : goalOrientedUtility uEpi uGoal β > goalOrientedUtility uEpi' uGoal' β) :
    combined (betaToLam β) uEpi uGoal > combined (betaToLam β) uEpi' uGoal' := by
  rw [goalOriented_eq_scaled_combined uEpi uGoal β hβ,
      goalOriented_eq_scaled_combined uEpi' uGoal' β hβ] at hord
  have h1 : (1 : ℚ) + β > 0 := by linarith
  exact lt_of_mul_lt_mul_left hord (le_of_lt h1)

end RSA.CombinedUtility
