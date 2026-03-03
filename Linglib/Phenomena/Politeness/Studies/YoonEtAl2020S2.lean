import Linglib.Phenomena.Politeness.Studies.YoonEtAl2020
import Linglib.Theories.Pragmatics.RSA.Core.ConfigData
import Linglib.Core.Interval.RSAVerify

/-!
# @cite{yoon-etal-2020} — Full S2 Model
@cite{yoon-etal-2020}

"Polite Speech Emerges From Competing Social Goals"

## Scope

This file implements the **full S2 model**: L0 → S1 → L1 → S2. The S2
speaker adds *presentational utility* — the desire to appear kind — on top
of informativity and social value. This is what drives the paper's main
finding: under the "both" goal condition, speakers produce more negation
at bad states than under "informative" alone.

## The S2 Model

The S2 speaker's utility has three terms computed w.r.t. L1 marginals
(Supplementary Eq. 4):

    U_S2(u, s; ω, φ̂) = ω_inf · ln P_L1(s|u)
                       + ω_soc · Σ_s' P_L1(s'|u) · V(s')
                       + ω_pres · ln P_L1(φ̂|u)

    P_S2(u|s, ω) ∝ P_prior(u) · exp(α · U_S2)

The three utility components:
- **Informativity** (ω_inf): log probability of the true state under L1
- **Social** (ω_soc): expected subjective value under L1
- **Presentational** (ω_pres): log probability that L1 infers the target
  kindness level φ̂ (speaker wants to *appear* kind)

## Parameter Sources (Supplementary Table 2, full model)

- α = 447/100 ≈ 4.47: shared by S1 and S2 (supplement: "which we assume
  to be the same value")
- c = 264/100 ≈ 2.64: cost of negation (positive utterances cost 1)
- Cost enters via utterance prior, NOT scaled by α:
  P_prior(u) ∝ exp(-1) for positive, exp(-c) for negated.
  In the combinedUtility framework (where α scales the sum), we encode
  this as a constant term -cost(u)/α.
- ω weights and φ̂: from Supplementary Table 2 (posterior means)
- φ grid: 20 values {0, 1/20,..., 19/20}. The paper's WebPPL uses
  40 values at 0.025 spacing; we use a coarser grid for tractability.

## Predictions

The key prediction is that the "both" goal condition produces more
negation at bad states than "informative" alone:

| # | Prediction | State | Theorem |
|---|-----------|-------|---------|
| 1 | Both@h0: S2(notTerrible) > S2(terrible) | h0 | `both_h0_prefers_negation` |
| 2 | Informative@h0: S2(terrible) > S2(notTerrible) | h0 | `informative_h0_prefers_direct` |
| 3 | Kind@h0: S2(notTerrible) > S2(terrible) | h0 | `kind_h0_prefers_negation` |
-/

set_option autoImplicit false

namespace Phenomena.Politeness.Studies.YoonEtAl2020S2

open Phenomena.Politeness.Studies.YoonEtAl2020

-- ============================================================================
-- §1. Latent Grid: Fin 20
-- ============================================================================

/-- Discretized kindness weight φ ∈ [0, 1].
    Grid of 20 values: {0, 1/20, 2/20,..., 19/20}.
    The paper's WebPPL uses 40 values at 0.025 spacing; we use 20 for
    tractability while maintaining sufficient resolution for the MAP
    estimates (φ̂ ≈ 0.35-0.50). -/
abbrev PhiGrid := Fin 20

/-- The rational value of each grid point: k/20 for k ∈ {0,..., 19}. -/
def phiVal (i : PhiGrid) : ℚ := i.val / 20

instance : Fintype HeartState where
  elems := {.h0, .h1, .h2, .h3}
  complete := fun x => by cases x <;> simp

instance : Fintype Utterance where
  elems := {.terrible, .bad, .good, .amazing,
            .notTerrible, .notBad, .notGood, .notAmazing}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §2. S2 Goal Weights
-- ============================================================================

/-- S2 utility weights for a specific goal condition.
    From Supplementary Table 2 (posterior means). -/
structure S2Weights where
  ωInf : ℚ       -- informativity weight
  ωSoc : ℚ       -- social weight
  ωPres : ℚ      -- presentational weight
  phiHat : PhiGrid  -- target kindness level φ̂ (discretized to grid)

-- ============================================================================
-- §2a. Cost Function
-- ============================================================================

/-- Cost term for the S1/S2 utility.
    In the WebPPL, cost enters via the utterance prior:
      P_prior(u) ∝ exp(-cost_yes) for positive, exp(-c) for negated
    where cost_yes = 1 and c = 264/100 (Supplementary Table 2).

    Since our combinedUtility scales everything by α, we divide by α
    so that α · costTerm = -cost(u):
      costTerm(pos) = -1/α = -100/447
      costTerm(neg) = -c/α = -264/447 -/
private def costTerm (u : Utterance) : ℚ :=
  if u.isNegated then -(264 : ℚ) / 447 else -(100 : ℚ) / 447

-- ============================================================================
-- §2b. Goal Condition Weights
-- ============================================================================

/-- Weights for "informative" goal condition.
    High presentational weight (ω_pres = 62%) with neutral φ̂ ≈ 0.49.
    Discretized to 10/20 = 0.50. -/
def informativeWeights : S2Weights where
  ωInf := 36/100
  ωSoc := 2/100
  ωPres := 62/100
  phiHat := ⟨10, by omega⟩  -- 10/20 = 0.50

/-- Weights for "kind" (social) goal condition.
    Highest social weight (ω_soc = 31%) with kind φ̂ ≈ 0.37.
    Discretized to 7/20 = 0.35. -/
def kindWeights : S2Weights where
  ωInf := 25/100
  ωSoc := 31/100
  ωPres := 44/100
  phiHat := ⟨7, by omega⟩   -- 7/20 = 0.35

/-- Weights for "both" goal condition.
    Balanced: ω_inf = 36%, ω_soc = 11%, ω_pres = 54%, φ̂ ≈ 0.36.
    Discretized to 7/20 = 0.35.
    The combination of informativity and presentational pressure drives
    the "both" condition's distinctive negation pattern. -/
def bothWeights : S2Weights where
  ωInf := 36/100
  ωSoc := 11/100
  ωPres := 54/100
  phiHat := ⟨7, by omega⟩   -- 7/20 = 0.35

-- ============================================================================
-- §3. S1 RSAConfigData (base for S2)
-- ============================================================================

/-- Full S2 model config. Parameters from Supplementary Table 2:
    - α = 447/100 ≈ 4.47 (shared by S1 and S2)
    - c = 264/100 ≈ 2.64 (cost of negation; baseline = 1)
    - ω weights per goal condition
    - φ grid: 20 values {0, 0.05,..., 0.95} -/
def s1Config (weights : S2Weights) : RSA.RSAConfigData Utterance HeartState where
  Latent := PhiGrid
  meaning := fun _φ u s => utteranceSemantics u s
  meaning_nonneg := by
    intro _l u w
    cases u <;> cases w <;>
    simp only [utteranceSemantics, adjMeaning, Core.GradedProposition.neg, softSemantics] <;> norm_num
  s1Spec := .combinedUtility
    (terms := [
      .logInformativity (fun (φ : PhiGrid) => phiVal φ),
      .expectedValue (fun (φ : PhiGrid) => 1 - phiVal φ) subjectiveValue,
      .constant (fun _ u => costTerm u)
    ])
    (logActive := fun φ => match φ.val with | 0 => false | _ + 1 => true)
  α := 447/100
  s2Spec := some (.utilityMaximizing (447/100) [
    .logStateMarginal weights.ωInf,
    .expectedValue weights.ωSoc subjectiveValue,
    .logLatentMarginal weights.ωPres weights.phiHat,
    .constant (fun u => costTerm u)
  ])

-- ============================================================================
-- §4. S2 Predictions: "Both" Goal
-- ============================================================================

/-- Under "both" goals at h0, S2 prefers "not terrible" over "terrible".
    This is the paper's main finding: dual goals produce negation. -/
theorem both_h0_prefers_negation :
    RSA.Verify.checkS2ScoreGt (s1Config bothWeights) .h0
      .notTerrible .terrible = true := by
  native_decide

-- ============================================================================
-- §5. S2 Predictions: "Informative" Goal
-- ============================================================================

/-- Under "informative" goals at h0, S2 prefers "terrible" over "not terrible".
    Direct speech dominates when the speaker prioritizes informativity. -/
theorem informative_h0_prefers_direct :
    RSA.Verify.checkS2ScoreGt (s1Config informativeWeights) .h0
      .terrible .notTerrible = true := by
  native_decide

-- ============================================================================
-- §6. S2 Predictions: "Kind" Goal
-- ============================================================================

/-- Under "kind" goals at h0, S2 prefers "not terrible" over "terrible".
    The social and presentational weights favor indirect speech. -/
theorem kind_h0_prefers_negation :
    RSA.Verify.checkS2ScoreGt (s1Config kindWeights) .h0
      .notTerrible .terrible = true := by
  native_decide

end Phenomena.Politeness.Studies.YoonEtAl2020S2
