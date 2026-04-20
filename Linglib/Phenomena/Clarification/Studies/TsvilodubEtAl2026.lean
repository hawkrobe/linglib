import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Basic
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

The paper's model is a direct softmax over expected utility (NOT RSA):

1. **CQ gate**: `P(CQ) = Logistic(τ · (ExpRegret(r*) − c))` — when to clarify
2. **Behavioral policy**: `π(r) = SoftMax(α · EU(r))` — what to say

We reinterpret the behavioral policy through RSA, connecting it to
@cite{hawkins-etal-2025}'s action-utility scoring.

## Connection to @cite{hawkins-etal-2025}

The behavioral policy π corresponds to @cite{hawkins-etal-2025}'s
respondent R₁ at β = 1, w_c = 0: **pure action utility**. R₁ scores
responses by:

    (1 − β) · log L0(w|r) + β · E_D[V(D, r)] − w_c · C(r)

At β = 1, w_c = 0 this reduces to `V(D, r)` — the action value. For the
bartender, V(g, r) = U(g, r) is the paper's utility table: 1 for matching
mention-some, 0 for mismatching, 1−δ for exhaustive.

The L0 gate (`if L0 = 0 then 0`) ensures truth-conditional consistency:
S1 never recommends a response that doesn't apply to the goal. This is
structurally identical to @cite{hawkins-etal-2025}'s `responseTruth` gate.

## Action utility and δ-sensitivity

With action-utility scoring, S1 preferences are **δ-sensitive**: the
exhaustive response's S1 score is `exp(α · (1−δ))`, which decreases
with δ. At high δ (large option space), S1 strongly prefers targeted
responses over exh. At low δ (small option space), exh is nearly as
good as targeted — S1's preference weakens.

This connects to the paper's experimental predictions (Exp 1: TL;JUSTASK,
NONEEDTOASK, JUSTLISTTHEMALL, TOOMANYTOLIST; Exp 2: WORTHASKING, etc.)
through the S1 behavioral policy:
- At high δ, exh is expensive → S1 concentrates on targeted responses
  → commitment under uncertainty is riskier → more to gain from clarifying
- At low δ, exh is cheap → S1 assigns near-equal weight to exh and targeted
  → safe to commit even under uncertainty → less need to clarify
-/

namespace TsvilodubEtAl2026

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

-- ============================================================================
-- §2. Meaning and Action Utility
-- ============================================================================

/-- Boolean applicability: does response r address goal g?
    Parallel to @cite{hawkins-etal-2025}'s `responseTruth`. -/
def respApplies : Response → Goal → Bool
  | .ms1, .g₁ => true
  | .ms2, .g₂ => true
  | .exh, _   => true
  | _, _      => false

-- ============================================================================
-- §3. RSAConfig with Action Utility
-- ============================================================================

open RSA Real in
/-- Bartender RSA with action-utility scoring.

    Parameterized by `exhVal` = 1 − δ (utility of exhaustive response)
    and goal prior weights.

    s1Score(L0, α, g, r) =
      if L0(g|r) = 0 then 0
      else exp(α · U(g, r))

    This is @cite{hawkins-etal-2025}'s `priorPQScore` at β = 1, w_c = 0:
    pure action utility. The L0 gate ensures truth-conditional consistency.

    Note: the paper's α has prior N(5, 1); we use α = 1 here. The
    qualitative predictions (all `>` theorems below) hold for any α > 0. -/
noncomputable def mkBartenderRSA (exhVal prior_g1 prior_g2 : ℝ)
    (hExh : 0 ≤ exhVal) (h1 : 0 ≤ prior_g1) (h2 : 0 ≤ prior_g2) :
    RSAConfig Response Goal where
  meaning _ _ r g := if respApplies r g then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α _ w u :=
    if l0 u w = 0 then 0
    else exp (α * match u, w with
      | .ms1, .g₁ => (1 : ℝ)
      | .ms2, .g₂ => 1
      | .exh, _   => exhVal
      | _, _      => 0)
  s1Score_nonneg l0 α _ _ u _ _ := by
    show 0 ≤ (if l0 u _ = 0 then (0 : ℝ) else exp _)
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

-- ============================================================================
-- §3a. Concrete Configs
-- ============================================================================

-- Fitted parameters (Bayesian posterior means):
-- δ_L = 0.32 → exhVal = 0.68, δ_S = 0.11 → exhVal = 0.89
-- ε_H = 0.49 → prior (51, 49), ε_L = 0.17 → prior (83, 17)

/-- Large option space (δ = 0.32), low uncertainty (ε = 0.17). -/
noncomputable def cfgLargeLow :=
  mkBartenderRSA (68/100) 83 17 (by norm_num) (by norm_num) (by norm_num)

/-- Large option space (δ = 0.32), high uncertainty (ε = 0.49). -/
noncomputable def cfgLargeHigh :=
  mkBartenderRSA (68/100) 51 49 (by norm_num) (by norm_num) (by norm_num)

/-- Small option space (δ = 0.11), low uncertainty (ε = 0.17). -/
noncomputable def cfgSmallLow :=
  mkBartenderRSA (89/100) 83 17 (by norm_num) (by norm_num) (by norm_num)

/-- Small option space (δ = 0.11), high uncertainty (ε = 0.49). -/
noncomputable def cfgSmallHigh :=
  mkBartenderRSA (89/100) 51 49 (by norm_num) (by norm_num) (by norm_num)

-- ============================================================================
-- §4. S1 Predictions (Speaker Behavior)
-- ============================================================================

/-! S1 captures the behavioral policy: how the responder acts when they know
the goal. With action-utility scoring, S1 preferences are δ-sensitive:
the exhaustive response scores `exp(α · (1−δ))`, which drops with δ. -/

/-- S1 facing g₁ prefers ms1 over exh in the large option space.
    U(g₁, ms1) = 1 > U(g₁, exh) = 0.68. -/
theorem S1_large_g1_prefers_ms1 :
    cfgLargeLow.S1 () .g₁ .ms1 > cfgLargeLow.S1 () .g₁ .exh := by
  rsa_predict

/-- S1 facing g₁ prefers ms1 over exh in the small option space too.
    U(g₁, ms1) = 1 > U(g₁, exh) = 0.89. The gap is smaller than large δ. -/
theorem S1_small_g1_prefers_ms1 :
    cfgSmallLow.S1 () .g₁ .ms1 > cfgSmallLow.S1 () .g₁ .exh := by
  rsa_predict

/-- S1 facing g₁ never produces ms2 (mismatching response).
    L0(g₁|ms2) = 0, so the L0 gate zeros the score. -/
theorem S1_g1_avoids_ms2 :
    cfgLargeLow.S1 () .g₁ .ms1 > cfgLargeLow.S1 () .g₁ .ms2 := by
  rsa_predict

-- ============================================================================
-- §4a. Cross-Config S1: δ-Sensitivity
-- ============================================================================

/-! The key RSA prediction: exh is relatively more viable in the small
option space (δ = 0.11) than the large (δ = 0.32). This captures the
EVPI effect through action utility: when the safe response is cheap,
there's less need to clarify. -/

/-- **WorthAsking** at S1 level: exh is more viable in small option space.
    S1(exh|g₁, small) > S1(exh|g₁, large) because exp(0.89α) > exp(0.68α). -/
theorem S1_small_exh_more_viable :
    cfgSmallLow.S1 () .g₁ .exh > cfgLargeLow.S1 () .g₁ .exh := by
  rsa_predict

-- ============================================================================
-- §5. L1 Predictions (Listener Inference)
-- ============================================================================

/-! Targeted responses (ms1, ms2) are fully informative: S1 never produces
ms1 for g₂ (L0 gate), so L1(g₁|ms1) = 1 regardless of prior or δ.

Exhaustive response transmits the prior: S1(exh|g₁) = S1(exh|g₂) (symmetric
utility), so L1(g|exh) ∝ P(g). Under asymmetric prior (ε < 0.5), exh
reveals the listener's prior belief about the goal. -/

/-- L1 hearing ms1 infers g₁ with certainty. -/
theorem L1_ms1_infers_g1 :
    cfgLargeLow.L1 .ms1 .g₁ > cfgLargeLow.L1 .ms1 .g₂ := by
  rsa_predict

/-- L1 hearing ms2 infers g₂ (symmetric). -/
theorem L1_ms2_infers_g2 :
    cfgLargeLow.L1 .ms2 .g₂ > cfgLargeLow.L1 .ms2 .g₁ := by
  rsa_predict

/-- L1 hearing exh leans toward g₁ (prior = 83:17).
    Since S1(exh|g₁) = S1(exh|g₂), L1(g|exh) ∝ P(g) — exh transmits
    the prior rather than being uninformative. -/
theorem L1_exh_transmits_prior :
    cfgLargeLow.L1 .exh .g₁ > cfgLargeLow.L1 .exh .g₂ := by
  rsa_predict

/-- Targeted responses remain fully informative at high uncertainty. -/
theorem L1_high_ms1_still_certain :
    cfgLargeHigh.L1 .ms1 .g₁ > cfgLargeHigh.L1 .ms1 .g₂ := by
  rsa_predict

end TsvilodubEtAl2026
