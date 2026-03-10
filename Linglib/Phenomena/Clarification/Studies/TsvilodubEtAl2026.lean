import Linglib.Phenomena.Clarification.Basic
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Tsvilodub, Mulligan, Snider, Hawkins & Franke (2026)
@cite{tsvilodub-etal-2026}

Act or Clarify? Modeling Sensitivity to Uncertainty and Cost in Communication.

## Overview

When should an agent ask a clarification question (CQ) vs. act under
uncertainty? This paper predicts and confirms that the decision depends on
both **uncertainty** (ε) about the interlocutor's goals and the **cost** (δ)
of available actions. The interaction is captured by **expected regret**
(= EVPI, @cite{raiffa-schlaifer-1961}).

## Two-layer model

1. **CQ gate**: `P(CQ) = Logistic(τ · (EVPI − c))`, where EVPI is the
   expected regret of the best available action
2. **Behavioral policy**: `π(r) = SoftMax(α · EU(r))`, a `RationalAction`
   over non-CQ responses — an RSA speaker choosing responses to maximize
   expected utility under goal uncertainty

## Key structural result

For the paper's 2×3 decision problem, EVPI = min(ε, δ). This yields:
- **TL;JustAsk**: high ε + large δ → EVPI = ε → increases with uncertainty
- **NoNeedToAsk**: any ε + small δ → EVPI = δ → independent of uncertainty
- **WorthAsking**: fix ε, increase δ → EVPI increases → more CQs

## Formalization

- §1–7: Decision-theoretic layer (EVPI). ℚ-valued `DecisionProblem` with
  `native_decide` proofs. Captures WHEN to ask a CQ.
- §8: RSA behavioral policy layer. ℝ-valued `RSAConfig` with `rsa_predict`
  proofs. Captures WHAT to say when committing (not asking a CQ).
-/

namespace Phenomena.Clarification.Studies.TsvilodubEtAl2026

open Core.DecisionTheory Phenomena.Clarification BigOperators

-- ============================================================================
-- §1. Types
-- ============================================================================

/-- The questioner's latent goal (e.g., preferred drink category). -/
inductive Goal where | g₁ | g₂
  deriving DecidableEq, Repr

instance : Fintype Goal where
  elems := {.g₁, .g₂}
  complete x := by cases x <;> simp

/-- Available non-CQ responses. -/
inductive Response where
  | ms1  -- mention-some matching g₁
  | ms2  -- mention-some matching g₂
  | exh  -- exhaustive (safe but costly)
  deriving DecidableEq, Repr

instance : Fintype Response where
  elems := {.ms1, .ms2, .exh}
  complete x := by cases x <;> simp

def allResponses : List Response := [.ms1, .ms2, .exh]

-- ============================================================================
-- §2. Parameterized Decision Problem
-- ============================================================================

/-- The bartender scenario DP, parameterized by uncertainty ε ∈ [0, 1/2]
    and exhaustive-action cost δ ∈ [0, 1].

    |      | ms1 | ms2 | exh |
    |------|-----|-----|-----|
    | g₁   |  1  |  0  | 1−δ |
    | g₂   |  0  |  1  | 1−δ |

    Prior: P(g₁) = 1−ε, P(g₂) = ε.

    ms1/ms2 are efficient but risky (utility 0 if goal is wrong).
    exh is safe but costly (utility 1−δ regardless of goal). -/
def mkDP (ε δ : ℚ) : DecisionProblem Goal Response where
  utility g r := match g, r with
    | .g₁, .ms1 => 1
    | .g₁, .ms2 => 0
    | .g₁, .exh => 1 - δ
    | .g₂, .ms1 => 0
    | .g₂, .ms2 => 1
    | .g₂, .exh => 1 - δ
  prior g := match g with
    | .g₁ => 1 - ε
    | .g₂ => ε

-- ============================================================================
-- §3. Concrete Experimental Conditions
-- ============================================================================

-- Fitted parameters (Bayesian posterior means):
-- δ_L = 0.32 (large option space), δ_S = 0.11 (small option space)
-- ε_H = 0.49 (high uncertainty), ε_L = 0.17 (low uncertainty)

def dpLargeLow  := mkDP (17/100) (32/100)
def dpLargeHigh := mkDP (49/100) (32/100)
def dpSmallLow  := mkDP (17/100) (11/100)
def dpSmallHigh := mkDP (49/100) (11/100)

-- ============================================================================
-- §4. EVPI Computations
-- ============================================================================

/-- Large option space, low uncertainty: EVPI = ε = 0.17.
    Since ε < δ (0.17 < 0.32), ms1 dominates exh, so
    EU(ms1) = 0.83 > EU(exh) = 0.68. EVPI = 1 − 0.83 = 0.17. -/
theorem evpi_large_low :
    evpi dpLargeLow allResponses = 17/100 := by native_decide

/-- Large option space, high uncertainty: EVPI = δ = 0.32.
    Since ε > δ (0.49 > 0.32), exh dominates ms1, so
    EU(exh) = 0.68 > EU(ms1) = 0.51. EVPI = 1 − 0.68 = 0.32. -/
theorem evpi_large_high :
    evpi dpLargeHigh allResponses = 32/100 := by native_decide

/-- Small option space, low uncertainty: EVPI = δ = 0.11.
    Since ε > δ (0.17 > 0.11), exh dominates. EVPI = 0.11. -/
theorem evpi_small_low :
    evpi dpSmallLow allResponses = 11/100 := by native_decide

/-- Small option space, high uncertainty: EVPI = δ = 0.11.
    Since ε > δ (0.49 > 0.11), exh dominates. EVPI = 0.11. -/
theorem evpi_small_high :
    evpi dpSmallHigh allResponses = 11/100 := by native_decide

-- ============================================================================
-- §5. Predictions
-- ============================================================================

/-- **TL;JustAsk**: In the large option space, higher uncertainty → higher EVPI.
    More CQs under high uncertainty because the mention-some gamble has
    higher expected regret. Confirmed: β = 1.58 [0.75, 2.48]. -/
theorem justAsk :
    evpi dpLargeHigh allResponses > evpi dpLargeLow allResponses := by
  native_decide

/-- **NoNeedToAsk**: In the small option space, EVPI is identical across
    uncertainty levels. The exhaustive answer is cheap enough (δ = 0.11)
    to dominate regardless of ε, capping regret at δ.
    Confirmed: β = −0.21 [−0.99, 0.58], CrI includes 0. -/
theorem noNeedToAsk :
    evpi dpSmallHigh allResponses = evpi dpSmallLow allResponses := by
  native_decide

/-- **WorthAsking**: At high uncertainty, larger option space (higher δ)
    → higher EVPI → more CQs.
    Confirmed: main effect of option space β = 0.40 [0.13, 0.67]. -/
theorem worthAsking :
    evpi dpLargeHigh allResponses > evpi dpSmallHigh allResponses := by
  native_decide

-- ============================================================================
-- §6. Connection to Van Rooy's Question Utility
-- ============================================================================

/-- Identity partition: each goal is its own cell. -/
def identityQ : Question Goal := [λ g => g == .g₁, λ g => g == .g₂]

/-- EVPI equals `questionUtility` on the identity partition.
    This grounds the expected regret model in @cite{van-rooy-2003}'s
    decision-theoretic question semantics: asking a CQ that fully
    resolves the questioner's goal has utility value = EVPI. -/
theorem evpi_eq_euv_identity :
    evpi dpLargeLow allResponses =
    questionUtility dpLargeLow allResponses identityQ := by
  native_decide

-- ============================================================================
-- §7. General Structure
-- ============================================================================

/-- For the bartender DP with ε ∈ [0, 1/2] and δ ∈ [0, 1]:
    EVPI = min(ε, δ).

    Proof sketch: max_a U(g, a) = 1 for all g (when δ ≤ 1), so
    oracleValue = 1. The optimal action has EU = max(1−ε, 1−δ)
    = 1 − min(ε, δ). Therefore EVPI = min(ε, δ).

    TODO: case-split on ε ≤ δ vs ε > δ and unfold dpValue. -/
theorem evpi_eq_min (ε δ : ℚ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1/2)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    evpi (mkDP ε δ) allResponses = min ε δ := by
  sorry

-- ============================================================================
-- §8. RSA Behavioral Policy (Layer 2)
-- ============================================================================

/-! The paper's two-layer model:
1. **CQ gate** (§4–5 above): decide WHETHER to clarify, via EVPI
2. **Behavioral policy** (this section): decide WHAT to say when committing

The behavioral policy π(r) = SoftMax(α · EU(r)) is an RSA speaker.
We model this as a standard RSA reference game:
- **Utterances** = Responses (ms1, ms2, exh)
- **Worlds** = Goals (g₁, g₂)
- **Meaning**: response r "applies to" goal g iff it (partially) satisfies g

L0 interprets responses as evidence about goals:
- ms1 uniquely identifies g₁ (L0(g₁|ms1) = 1)
- ms2 uniquely identifies g₂ (L0(g₂|ms2) = 1)
- exh is ambiguous (L0(g|exh) = 1/2)

S1 prefers informative responses, paralleling @cite{frank-goodman-2012}'s
size principle: targeted responses (extension 1) beat exhaustive
(extension 2). -/

/-- Boolean applicability: does response r address goal g? -/
def respApplies : Response → Goal → Bool
  | .ms1, .g₁ => true
  | .ms2, .g₂ => true
  | .exh, _   => true
  | _, _      => false

open RSA Real in
/-- Bartender RSA constructor, parameterized by (unnormalized) goal prior.
    Belief-based S1 scoring: S1(r|g) ∝ L0(g|r)^α. -/
noncomputable def mkBartenderRSA (prior_g1 prior_g2 : ℝ)
    (h1 : 0 ≤ prior_g1) (h2 : 0 ≤ prior_g2) : RSAConfig Response Goal where
  meaning _ _ r g := if respApplies r g then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α _ w u :=
    if l0 u w = 0 then 0
    else exp (α * log (l0 u w))
  s1Score_nonneg l0 α _ _ u _ _ := by
    split
    · exact le_refl 0
    · exact le_of_lt (exp_pos _)
  α := 1
  α_pos := by norm_num
  worldPrior g := match g with
    | .g₁ => prior_g1
    | .g₂ => prior_g2
  worldPrior_nonneg g := by cases g <;> assumption
  latentPrior_nonneg _ _ := by norm_num

/-- Uniform-prior bartender: structural S1/L1 predictions. -/
noncomputable def bartenderCfg :=
  mkBartenderRSA 1 1 (by norm_num) (by norm_num)

/-- Low uncertainty (ε = 0.17): P(g₁) ∝ 83, P(g₂) ∝ 17. -/
noncomputable def bartenderCfgLow :=
  mkBartenderRSA 83 17 (by norm_num) (by norm_num)

/-- High uncertainty (ε = 0.49): P(g₁) ∝ 51, P(g₂) ∝ 49. -/
noncomputable def bartenderCfgHigh :=
  mkBartenderRSA 51 49 (by norm_num) (by norm_num)

-- ============================================================================
-- §8a. S1 Predictions (Speaker Behavior)
-- ============================================================================

/-! S1 captures the behavioral policy: how the responder acts when they know
the goal. These predictions are independent of the prior (worldPrior doesn't
enter S1). -/

/-- S1 facing g₁ prefers ms1 (targeted) over exh (exhaustive).
    ms1 has L0(g₁|ms1) = 1 while exh has L0(g₁|exh) = 1/2. -/
theorem S1_g1_prefers_ms1 :
    bartenderCfg.S1 () .g₁ .ms1 > bartenderCfg.S1 () .g₁ .exh := by
  rsa_predict

/-- S1 facing g₁ never produces ms2.
    L0(g₁|ms2) = 0, so S1(ms2|g₁) = 0. -/
theorem S1_g1_avoids_ms2 :
    bartenderCfg.S1 () .g₁ .ms1 > bartenderCfg.S1 () .g₁ .ms2 := by
  rsa_predict

/-- S1 is symmetric: facing g₂ prefers ms2, mirroring S1(ms1|g₁). -/
theorem S1_g2_prefers_ms2 :
    bartenderCfg.S1 () .g₂ .ms2 > bartenderCfg.S1 () .g₂ .exh := by
  rsa_predict

-- ============================================================================
-- §8b. L1 Predictions (Listener Inference)
-- ============================================================================

/-! L1 captures pragmatic inference: what goal does a response reveal?
Targeted responses (ms1, ms2) are fully informative — L1 infers the matching
goal with certainty. The exhaustive response is uninformative — L1 reverts
to the prior. -/

/-- L1 hearing ms1 infers g₁. Since S1(ms1|g₂) = 0 (ms1 never signals g₂),
    L1(g₁|ms1) = 1 regardless of prior. -/
theorem L1_ms1_infers_g1 :
    bartenderCfg.L1 .ms1 .g₁ > bartenderCfg.L1 .ms1 .g₂ := by
  rsa_predict

/-- L1 hearing ms2 infers g₂ (symmetric). -/
theorem L1_ms2_infers_g2 :
    bartenderCfg.L1 .ms2 .g₂ > bartenderCfg.L1 .ms2 .g₁ := by
  rsa_predict

/-- L1 hearing exh cannot distinguish goals: exh is equally likely under
    both goals, so L1 reverts to the prior. With uniform prior,
    L1(g₁|exh) = L1(g₂|exh) — neither is preferred. -/
theorem L1_exh_uninformative :
    ¬(bartenderCfg.L1 .exh .g₁ > bartenderCfg.L1 .exh .g₂) := by
  rsa_predict

-- ============================================================================
-- §8c. Asymmetric Prior Predictions
-- ============================================================================

/-! With asymmetric priors (ε ≠ 1/2), targeted responses are still fully
informative (L1(g₁|ms1) = 1), but exh reveals the prior: L1(g₁|exh) = 1−ε.
This is the RSA analog of the EVPI result: under low uncertainty, the
responder's "safe" response still signals the likely goal. -/

/-- Under low uncertainty, L1 hearing exh leans toward g₁.
    L1(g₁|exh) ∝ 83 · S1(exh|g₁) > L1(g₂|exh) ∝ 17 · S1(exh|g₂).
    Since S1(exh|g₁) = S1(exh|g₂), ratio is 83:17. -/
theorem L1_low_exh_leans_g1 :
    bartenderCfgLow.L1 .exh .g₁ > bartenderCfgLow.L1 .exh .g₂ := by
  rsa_predict

/-- Under high uncertainty, L1 hearing exh barely distinguishes goals.
    Ratio is 51:49 — nearly uninformative. -/
theorem L1_high_exh_leans_g1 :
    bartenderCfgHigh.L1 .exh .g₁ > bartenderCfgHigh.L1 .exh .g₂ := by
  rsa_predict

/-- Targeted responses are fully informative regardless of prior.
    L1(g₁|ms1) = 1 even under high uncertainty. -/
theorem L1_high_ms1_still_certain :
    bartenderCfgHigh.L1 .ms1 .g₁ > bartenderCfgHigh.L1 .ms1 .g₂ := by
  rsa_predict

end Phenomena.Clarification.Studies.TsvilodubEtAl2026
