import Linglib.Theories.Pragmatics.RSA.Core.ConfigData
import Linglib.Core.Interval.RSAEval
import Linglib.Core.Interval.RSAVerify
import Linglib.Tactics.RSAPredict
import Linglib.Core.Semantics.GradedProposition

/-!
# @cite{yoon-etal-2020} — Polite Speech Emerges From Competing Social Goals

## Overview

Politeness arises from the interplay of three communicative goals:
**informativity** (conveying the true state), **social value** (making the
listener feel good), and **presentational** utility (appearing kind to
the listener). This file implements both the S1 submodel (informativity +
social tradeoff) and the full S2 model (adding presentational utility).

## Experimental Design

- 202 participants on Amazon MTurk
- 12 scenarios per participant (3 goals × 4 states)
- Goals: informative, kind, both
- States: 0-3 hearts (true quality rating)
- Utterances: 8 options (4 adjectives × pos/neg)

## Finding

Speakers with BOTH goals (informative + kind) produce more negation
in bad states (0-1 hearts) compared to single-goal conditions. This is
the signature of indirect speech driven by self-presentation.

## File Structure

- §1. Types & Semantics — shared across S1 and S2 models
- §2. S1 Submodel — simplified (α=3, 5-point φ), demonstrating the
  informativity–social tradeoff that drives negation
- §3. Full S2 Model — paper's fitted parameters (α≈4.47, 20-point φ grid),
  with presentational utility driving the "both" condition's negation pattern
-/

set_option autoImplicit false

namespace Phenomena.Politeness.Studies.YoonEtAl2020

open Core.GradedProposition (GProp neg)

-- ============================================================================
-- §1. Types & Semantics
-- ============================================================================

/-- Heart state: 0-3 hearts representing true quality -/
inductive HeartState where
  | h0  -- 0 hearts (terrible)
  | h1  -- 1 heart (bad)
  | h2  -- 2 hearts (good)
  | h3  -- 3 hearts (amazing)
  deriving DecidableEq, Repr, BEq, Inhabited

instance : Fintype HeartState where
  elems := {.h0, .h1, .h2, .h3}
  complete := fun x => by cases x <;> simp

/-- Utterance types: 4 adjectives × positive/negative -/
inductive Utterance where
  | terrible      -- "It was terrible"
  | bad           -- "It was bad"
  | good          -- "It was good"
  | amazing       -- "It was amazing"
  | notTerrible   -- "It wasn't terrible"
  | notBad        -- "It wasn't bad"
  | notGood       -- "It wasn't good"
  | notAmazing    -- "It wasn't amazing"
  deriving DecidableEq, Repr, BEq, Inhabited

instance : Fintype Utterance where
  elems := {.terrible, .bad, .good, .amazing,
            .notTerrible, .notBad, .notGood, .notAmazing}
  complete := fun x => by cases x <;> simp

/-- Is this a negated utterance? -/
def Utterance.isNegated : Utterance → Bool
  | .notTerrible | .notBad | .notGood | .notAmazing => true
  | _ => false

/-- Get the base adjective (without negation) -/
inductive Adjective where
  | terrible | bad | good | amazing
  deriving DecidableEq, Repr, BEq

def Utterance.baseAdjective : Utterance → Adjective
  | .terrible | .notTerrible => .terrible
  | .bad | .notBad => .bad
  | .good | .notGood => .good
  | .amazing | .notAmazing => .amazing

/-- Speaker goal conditions from the experiment -/
inductive GoalCondition where
  | informative  -- "give accurate and informative feedback"
  | kind         -- "make the listener feel good"
  | both         -- "BOTH make Bob feel good AND give accurate feedback"
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Soft semantic meaning: P(accept | adjective, state) from the literal
semantics norming task.

Raw acceptance proportions from `literal_semantics.csv` in the paper's
GitHub repository (https://github.com/ejyoon/polite_speaker). N=49
participants (after exclusions; supplement reports N=51 recruited) made
binary yes/no judgments for each adjective × state combination.

The paper's full model infers θ via a Beta-Binomial BDA (uniform Beta(1,1)
prior), marginalizing over posterior uncertainty. We use the raw proportions
k/49 as point estimates — the maximum likelihood values.
-/
def softSemantics : Adjective → HeartState → ℚ
  -- "terrible": peaks at 0 hearts, ~50% at 1 heart
  | .terrible, .h0 => 1       -- 49/49
  | .terrible, .h1 => 26/49   -- 0.53
  | .terrible, .h2 => 0       -- 0/49
  | .terrible, .h3 => 1/49    -- 0.02
  -- "bad": high at 0-1 hearts, zero at 2-3
  | .bad, .h0 => 1            -- 49/49
  | .bad, .h1 => 45/49        -- 0.92
  | .bad, .h2 => 0            -- 0/49
  | .bad, .h3 => 0            -- 0/49
  -- "good": high at 2-3 hearts (text confirms "equally true at 2 and 3")
  | .good, .h0 => 1/49        -- 0.02
  | .good, .h1 => 2/49        -- 0.04
  | .good, .h2 => 47/49       -- 0.96
  | .good, .h3 => 1           -- 49/49
  -- "amazing": peaks at 3 hearts
  | .amazing, .h0 => 1/49     -- 0.02
  | .amazing, .h1 => 1/49     -- 0.02
  | .amazing, .h2 => 7/49     -- 0.14
  | .amazing, .h3 => 47/49    -- 0.96

/-- Base adjective meaning (positive form).
    Returns a graded proposition `GProp HeartState = HeartState → ℚ`. -/
def adjMeaning : Adjective → GProp HeartState
  | .terrible => softSemantics .terrible
  | .bad => softSemantics .bad
  | .good => softSemantics .good
  | .amazing => softSemantics .amazing

/--
**Compositionally derived utterance semantics.**

Negated utterances are derived by applying `Core.GradedProposition.neg`
to base meanings:
- ⟦not terrible⟧ = neg(⟦terrible⟧)

This mirrors Montague's compositional semantics where ⟦not φ⟧ = pnot(⟦φ⟧),
lifted to graded propositions (see `neg_involutive`, `neg_antitone`).
-/
def utteranceSemantics : Utterance → GProp HeartState
  -- Positive forms: base adjective meaning
  | .terrible => adjMeaning .terrible
  | .bad => adjMeaning .bad
  | .good => adjMeaning .good
  | .amazing => adjMeaning .amazing
  -- Negated forms: compositionally derived via graded negation
  | .notTerrible => neg (adjMeaning .terrible)
  | .notBad => neg (adjMeaning .bad)
  | .notGood => neg (adjMeaning .good)
  | .notAmazing => neg (adjMeaning .amazing)

/-- Utterance cost: number of words -/
def utteranceCost : Utterance → ℕ
  | .terrible | .bad | .good | .amazing => 2  -- "It was X"
  | .notTerrible | .notBad | .notGood | .notAmazing => 3  -- "It wasn't X"

/--
Subjective value V(s): linear mapping from states to values.
The listener prefers higher heart states: V(3 hearts) > V(0 hearts).
-/
def subjectiveValue : HeartState → ℚ
  | .h0 => 0
  | .h1 => 1
  | .h2 => 2
  | .h3 => 3

-- ============================================================================
-- §1a. Structural Properties
-- ============================================================================

/-- The model uses soft semantics: meaning values are in [0,1]. -/
theorem meaning_bounded : ∀ u s, 0 ≤ utteranceSemantics u s ∧ utteranceSemantics u s ≤ 1 := by
  intro u s; cases u <;> cases s <;>
  simp only [utteranceSemantics, adjMeaning, Core.GradedProposition.neg, softSemantics] <;>
  constructor <;> norm_num

/-- Negated utterances cost more than direct ones. -/
theorem negation_costlier : ∀ u : Utterance, u.isNegated → utteranceCost u = 3 := by
  intro u h; cases u <;> simp [Utterance.isNegated] at h <;> rfl

/-- Direct utterances cost less. -/
theorem direct_cheaper : ∀ u : Utterance, ¬u.isNegated → utteranceCost u = 2 := by
  intro u h; cases u <;> simp [Utterance.isNegated] at h <;> rfl

-- ============================================================================
-- §2. S1 Submodel (simplified parameters)
-- ============================================================================

/-!
### S1 Submodel

The S1 speaker's utility is a weighted sum of **informativity** and
**social value**, interpolated by a latent kindness weight φ:

    U_S1(u, s; φ) = φ · log L0(u,s) + (1−φ) · E_L0[V|u] − c · l(u)

This submodel uses approximate parameters (α = 3, c = 1, 5-point φ grid)
to demonstrate the qualitative predictions. The paper infers α and c via
BDA with priors α ~ Uniform(0, 20) and c ~ Uniform(1, 10).
-/

/-- Discretized kindness weight. The paper uses continuous φ ~ Uniform(0, 1);
    we discretize to {0, 1/4, 1/2, 3/4, 1} for computable verification.
    Higher φ = speaker prioritizes informativity over social value. -/
inductive Phi where
  | p0    -- φ = 0   (pure social)
  | p25   -- φ = 1/4
  | p50   -- φ = 1/2
  | p75   -- φ = 3/4
  | p100  -- φ = 1   (pure informativity)
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Phi where
  elems := {.p0, .p25, .p50, .p75, .p100}
  complete := fun x => by cases x <;> simp

/-- The rational value of each φ level. -/
def Phi.val : Phi → ℚ
  | .p0   => 0
  | .p25  => 1/4
  | .p50  => 1/2
  | .p75  => 3/4
  | .p100 => 1

/-- S1 submodel with approximate parameters (α = 3, c = 1).

    S1 utility = φ · log L0(u,s) + (1−φ) · E_L0[V|u] − l(u)

    Uses `combinedUtility` with three terms:
    - `logInformativity`: φ · log L0 (informativity at true state)
    - `expectedValue`: (1−φ) · E_L0[V|u] (social value)
    - `constant`: −l(u) (utterance length cost, with c = 1) -/
def cfg : RSA.RSAConfigData Utterance HeartState where
  Latent := Phi
  meaning := fun _φ u s => utteranceSemantics u s
  meaning_nonneg := by
    intro _l u w
    cases u <;> cases w <;>
    simp only [utteranceSemantics, adjMeaning, Core.GradedProposition.neg, softSemantics] <;> norm_num
  s1Spec := .combinedUtility
    (terms := [
      .logInformativity (fun φ => φ.val),
      .expectedValue (fun φ => 1 - φ.val) subjectiveValue,
      .constant (fun _ u => -(↑(utteranceCost u) : ℚ))
    ])
    -- The log gate is inactive for the pure social speaker (φ=0, weight=0).
    -- This allows semantically incompatible utterances to receive positive
    -- scores when the speaker doesn't care about informativity.
    (logActive := fun φ => match φ with | .p0 => false | _ => true)
  α := 3

-- ============================================================================
-- §2a. State Inference: Direct Utterances
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- "terrible" → h0: L1 assigns more mass to h0 than h3. -/
theorem terrible_map_h0_vs_h3 :
    cfg.toRSAConfig.L1 .terrible .h0 > cfg.toRSAConfig.L1 .terrible .h3 := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- "terrible" → h0: L1 assigns more mass to h0 than h1. -/
theorem terrible_map_h0_vs_h1 :
    cfg.toRSAConfig.L1 .terrible .h0 > cfg.toRSAConfig.L1 .terrible .h1 := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- "bad" → h1: L1 assigns more mass to h1 than h0. -/
theorem bad_map_h1_vs_h0 :
    cfg.toRSAConfig.L1 .bad .h1 > cfg.toRSAConfig.L1 .bad .h0 := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- "bad" → h1: L1 assigns more mass to h1 than h3. -/
theorem bad_map_h1_vs_h3 :
    cfg.toRSAConfig.L1 .bad .h1 > cfg.toRSAConfig.L1 .bad .h3 := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- "good" → h2: L1 assigns more mass to h2 than h0. -/
theorem good_map_h2_vs_h0 :
    cfg.toRSAConfig.L1 .good .h2 > cfg.toRSAConfig.L1 .good .h0 := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- "good" → h2: L1 assigns more mass to h2 than h3. -/
theorem good_map_h2_vs_h3 :
    cfg.toRSAConfig.L1 .good .h2 > cfg.toRSAConfig.L1 .good .h3 := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- "amazing" → h3: L1 assigns more mass to h3 than h0. -/
theorem amazing_map_h3_vs_h0 :
    cfg.toRSAConfig.L1 .amazing .h3 > cfg.toRSAConfig.L1 .amazing .h0 := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- "amazing" → h3: L1 assigns more mass to h3 than h2. -/
theorem amazing_map_h3_vs_h2 :
    cfg.toRSAConfig.L1 .amazing .h3 > cfg.toRSAConfig.L1 .amazing .h2 := by
  rsa_predict

-- ============================================================================
-- §2b. State Inference: Negated Utterances
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- "not terrible" shifts away from h0: L1 prefers h1 over h0.
    Negation makes bad states more acceptable, so the listener infers
    the state is "not the worst" rather than "the worst". -/
theorem not_terrible_away_from_h0 :
    cfg.toRSAConfig.L1 .notTerrible .h1 > cfg.toRSAConfig.L1 .notTerrible .h0 := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- "not bad" peaks at h2: L1 prefers h2 over h3.
    "Not bad" is most compatible with moderate-good states. -/
theorem not_bad_peaks_h2 :
    cfg.toRSAConfig.L1 .notBad .h2 > cfg.toRSAConfig.L1 .notBad .h3 := by
  rsa_predict

-- ============================================================================
-- §2c. Speaker Behavior: Informativity vs Social Goals
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- At h0, a purely informative speaker (φ=1) prefers "terrible" over
    "not terrible". Direct speech maximizes informativity. -/
theorem informative_prefers_direct :
    cfg.toRSAConfig.S1 .p100 .h0 .terrible > cfg.toRSAConfig.S1 .p100 .h0 .notTerrible := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- At h0, a purely social speaker (φ=0) prefers "not terrible" over
    "terrible". Indirect speech maximizes social value: E[V|"not terrible"]
    is much higher than E[V|"terrible"] because L0 assigns probability
    to high-value states. -/
theorem social_prefers_indirect :
    cfg.toRSAConfig.S1 .p0 .h0 .notTerrible > cfg.toRSAConfig.S1 .p0 .h0 .terrible := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- Even at φ=1/4, the speaker still prefers "terrible" over "not terrible"
    at h0. The informativity penalty of "not terrible" at h0 outweighs the
    social benefit until φ drops to 0. This shows the crossover between
    direct and indirect preference is between φ=0 and φ=1/4. -/
theorem slight_informativity_prefers_direct :
    cfg.toRSAConfig.S1 .p25 .h0 .terrible > cfg.toRSAConfig.S1 .p25 .h0 .notTerrible := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- At h3, a purely social speaker prefers "amazing" over "good".
    Even without informativity concerns, the higher expected social value
    from "amazing" (which concentrates L0 on h3) drives the preference. -/
theorem social_prefers_positive :
    cfg.toRSAConfig.S1 .p0 .h3 .amazing > cfg.toRSAConfig.S1 .p0 .h3 .good := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- At h3, a purely informative speaker prefers "amazing" over "not amazing".
    Direct positive speech is more informative. -/
theorem informative_prefers_direct_positive :
    cfg.toRSAConfig.S1 .p100 .h3 .amazing > cfg.toRSAConfig.S1 .p100 .h3 .notAmazing := by
  rsa_predict

-- ============================================================================
-- §3. Full S2 Model (paper's fitted parameters)
-- ============================================================================

/-!
### Full S2 Model

The S2 speaker's utility has three terms computed w.r.t. L1 marginals:

    U_S2(u, s; ω, φ̂) = ω_inf · ln P_L1(s|u)
                       + ω_soc · Σ_s' P_L1(s'|u) · V(s')
                       + ω_pres · ln P_L1(φ̂|u)

    P_S2(u|s, ω) ∝ exp(-cost(u)) · exp(α · U_S2)

The three utility components:
- **Informativity** (ω_inf): log probability of the true state under L1
- **Social** (ω_soc): expected subjective value under L1
- **Presentational** (ω_pres): log probability that L1 infers the target
  kindness level φ̂ (speaker wants to *appear* kind)

### Parameters

This uses the paper's fitted parameters from the supplement:
- α ≈ 4.47: shared by S1 and S2
- c ≈ 2.64: cost of negation (positive utterances cost 1)
- ω weights and φ̂: posterior means per goal condition
- φ grid: 20 values {0, 1/20,..., 19/20}

### Cost Encoding

Cost enters the S2 model multiplicatively via the utterance prior:
P_prior(u) ∝ exp(-cost(u)). In the `combinedUtility` framework (where
the exponent is α · Σ terms), this is encoded as a constant term
−cost(u)/α, so that α · (−cost/α) = −cost, yielding the correct
exp(−cost) factor after exponentiation.
-/

/-- Discretized kindness weight φ ∈ [0, 1] on a 20-point grid.
    Grid: {0, 1/20, 2/20,..., 19/20}. The paper's WebPPL uses 40 values
    at 0.025 spacing; we use 20 for tractability while maintaining
    sufficient resolution for the MAP estimates (φ̂ ≈ 0.35-0.50). -/
abbrev PhiGrid := Fin 20

/-- The rational value of each grid point: k/20 for k ∈ {0,..., 19}. -/
def phiVal (i : PhiGrid) : ℚ := i.val / 20

/-- S2 utility weights for a specific goal condition.
    Posterior means from the supplement's parameter table. -/
structure S2Weights where
  ωInf : ℚ       -- informativity weight
  ωSoc : ℚ       -- social weight
  ωPres : ℚ      -- presentational weight
  phiHat : PhiGrid  -- target kindness level φ̂ (discretized to grid)

/-- Cost term for the S1/S2 utility.
    Cost enters via the utterance prior: P_prior(u) ∝ exp(-cost(u)).
    Since `combinedUtility` scales everything by α, we divide by α
    so that α · costTerm = -cost(u):
      costTerm(pos) = -1/α = -100/447
      costTerm(neg) = -c/α = -264/447 -/
private def costTerm (u : Utterance) : ℚ :=
  if u.isNegated then -(264 : ℚ) / 447 else -(100 : ℚ) / 447

-- §3a. Goal Condition Weights

/-- Weights for "informative" goal condition.
    High presentational weight (ω_pres = 62%) with neutral φ̂ ≈ 0.49.
    Discretized to 10/20 = 0.50. -/
def informativeWeights : S2Weights where
  ωInf := 36/100
  ωSoc := 2/100
  ωPres := 62/100
  phiHat := ⟨10, by omega⟩

/-- Weights for "kind" (social) goal condition.
    Highest social weight (ω_soc = 31%) with kind φ̂ ≈ 0.37.
    Discretized to 7/20 = 0.35. -/
def kindWeights : S2Weights where
  ωInf := 25/100
  ωSoc := 31/100
  ωPres := 44/100
  phiHat := ⟨7, by omega⟩

/-- Weights for "both" goal condition.
    Balanced: ω_inf = 36%, ω_soc = 11%, ω_pres = 54%, φ̂ ≈ 0.36.
    Discretized to 7/20 = 0.35.
    The combination of informativity and presentational pressure drives
    the "both" condition's distinctive negation pattern. -/
def bothWeights : S2Weights where
  ωInf := 36/100
  ωSoc := 11/100
  ωPres := 54/100
  phiHat := ⟨7, by omega⟩

-- §3b. S2 RSAConfigData

/-- Full S2 model config parameterized by goal-condition weights.
    Parameters from the supplement:
    - α ≈ 4.47 (shared by S1 and S2)
    - Cost: 1 for positive, ≈2.64 for negated (encoded as −cost/α)
    - φ grid: 20 values {0, 0.05,..., 0.95} -/
def s2Config (weights : S2Weights) : RSA.RSAConfigData Utterance HeartState where
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
-- §3c. S2 Predictions
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- Under "both" goals at h0, S2 prefers "not terrible" over "terrible".
    This is the paper's main finding: dual goals produce negation.

    TODO: This prediction does not hold with raw acceptance proportions
    (k/49) as point estimates for the literal semantics. The paper's
    full model infers θ via BDA, marginalizing over posterior uncertainty
    in a joint posterior over (α, c, ω, φ̂, θ). The qualitative prediction
    may depend on this full posterior rather than point estimates. -/
theorem both_h0_prefers_negation :
    (s2Config bothWeights).S2Utility .h0 .notTerrible >
    (s2Config bothWeights).S2Utility .h0 .terrible := by
  sorry

set_option maxHeartbeats 8000000 in
/-- Under "informative" goals at h0, S2 prefers "terrible" over "not terrible".
    Direct speech dominates when the speaker prioritizes informativity. -/
theorem informative_h0_prefers_direct :
    (s2Config informativeWeights).S2Utility .h0 .terrible >
    (s2Config informativeWeights).S2Utility .h0 .notTerrible := by
  rsa_predict

set_option maxHeartbeats 8000000 in
/-- Under "kind" goals at h0, S2 prefers "not terrible" over "terrible".
    The social and presentational weights favor indirect speech.

    TODO: Same sensitivity as `both_h0_prefers_negation` — does not hold
    with raw proportions as point estimates for θ. -/
theorem kind_h0_prefers_negation :
    (s2Config kindWeights).S2Utility .h0 .notTerrible >
    (s2Config kindWeights).S2Utility .h0 .terrible := by
  sorry

end Phenomena.Politeness.Studies.YoonEtAl2020
