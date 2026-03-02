import Linglib.Phenomena.Politeness.Studies.YoonEtAl2020
import Linglib.Theories.Pragmatics.RSA.Core.ConfigData
import Linglib.Core.Interval.RSAEval
import Linglib.Core.Interval.RSAVerify

/-!
# Yoon et al. (2020) — RSA Politeness Model
@cite{yoon-etal-2020}

"Polite Speech Emerges From Competing Social Goals"

## The Model

The S1 speaker's utility is a weighted sum of **informativity** and
**social value**, interpolated by a latent kindness weight φ ∈ {0, ¼, ½, ¾, 1}:

    U_S1(u, s; φ) = φ · log L0(u,s) + (1−φ) · E_L0[V|u] − cost(u)

where:
- `log L0(u,s)` = informativity at the true state s
- `E_L0[V|u] = Σ_s' L0(u,s') · V(s')` = expected subjective value under L0
- `V(s) = s` = listener prefers higher states
- `cost(u)` = number of words (2 for direct, 3 for negated)

L1 marginalizes over φ to infer both the true state and the speaker's
kindness weight:

    L1(s, φ | u) ∝ P(s) · P(φ) · S1(u | s, φ)

This uses `combinedUtility` with three terms: `logInformativity` for the
informativity component, `expectedValue` for the social component, and
`constant` for utterance cost.

## Key Insight

Negation emerges as optimal when the speaker prioritizes social goals over
informativity. "Not terrible" is informationally weak (high L0 for many
states) but socially kind (high expected value). A purely social speaker
(φ=0) prefers "not terrible" at bad states; a purely informative speaker
(φ=1) prefers direct "terrible". The crossover is between φ=0 and φ=1/4 —
even a slightly informative speaker prefers directness at h0.

## Predictions

| # | Prediction | Theorem |
|---|-----------|---------|
| 1 | "terrible" → h0 (MAP state) | `terrible_map_h0_vs_h3`, `terrible_map_h0_vs_h1` |
| 2 | "bad" → h1 (MAP state) | `bad_map_h1_vs_h0`, `bad_map_h1_vs_h3` |
| 3 | "good" → h2 (MAP state) | `good_map_h2_vs_h0`, `good_map_h2_vs_h3` |
| 4 | "amazing" → h3 (MAP state) | `amazing_map_h3_vs_h0`, `amazing_map_h3_vs_h2` |
| 5 | "not terrible" → h1 over h0 | `not_terrible_away_from_h0` |
| 6 | "not bad" → h2 peaks | `not_bad_peaks_h2` |
| 7 | φ=1 prefers direct | `informative_prefers_direct` |
| 8 | φ=0 prefers indirect | `social_prefers_indirect` |
| 9 | φ=1/4 still prefers direct | `slight_informativity_prefers_direct` |
| 10 | φ=0 social prefers most positive | `social_prefers_positive` |
-/

set_option autoImplicit false

namespace Phenomena.Politeness.Studies.YoonEtAl2020RSA

open Phenomena.Politeness.Studies.YoonEtAl2020

-- ============================================================================
-- §1. Fintype Instances
-- ============================================================================

instance : Fintype HeartState where
  elems := {.h0, .h1, .h2, .h3}
  complete := fun x => by cases x <;> simp

instance : Fintype Utterance where
  elems := {.terrible, .bad, .good, .amazing,
            .notTerrible, .notBad, .notGood, .notAmazing}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §2. Latent Variable: Kindness Weight φ
-- ============================================================================

/-- Discretized kindness weight φ ∈ {0, 1/4, 1/2, 3/4, 1}.
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

-- ============================================================================
-- §3. RSAConfigData
-- ============================================================================

/-- Yoon et al. (2020) politeness RSA model.

    S1 utility = φ · log L0(u,s) + (1−φ) · E_L0[V|u] − cost(u)

    This uses `combinedUtility` with three terms:
    - `logInformativity`: φ · log L0 (informativity at true state)
    - `expectedValue`: (1−φ) · E_L0[V|u] (social value)
    - `constant`: −cost(u) (utterance cost) -/
def cfg : RSA.RSAConfigData Utterance HeartState where
  Latent := Phi
  meaning := fun _φ u s => utteranceSemantics u s
  meaning_nonneg := by
    intro _l u w
    cases u <;> cases w <;>
    simp only [utteranceSemantics, adjMeaning, softNot, softSemantics] <;> norm_num
  scoreSpec := .combinedUtility [
    .logInformativity (fun φ => φ.val),
    .expectedValue (fun φ => 1 - φ.val) subjectiveValue,
    .constant (fun _ u => -(↑(utteranceCost u) : ℚ))
  ]
  α := 3
  -- uniform priors over states and φ

-- ============================================================================
-- §4. State Inference: Direct Utterances
-- ============================================================================

/-- "terrible" → h0: L1 assigns more mass to h0 than h3. -/
theorem terrible_map_h0_vs_h3 :
    RSA.Verify.checkL1ScoreGt cfg .terrible .h0 .terrible .h3 = true := by
  native_decide

/-- "terrible" → h0: L1 assigns more mass to h0 than h1. -/
theorem terrible_map_h0_vs_h1 :
    RSA.Verify.checkL1ScoreGt cfg .terrible .h0 .terrible .h1 = true := by
  native_decide

/-- "bad" → h1: L1 assigns more mass to h1 than h0. -/
theorem bad_map_h1_vs_h0 :
    RSA.Verify.checkL1ScoreGt cfg .bad .h1 .bad .h0 = true := by
  native_decide

/-- "bad" → h1: L1 assigns more mass to h1 than h3. -/
theorem bad_map_h1_vs_h3 :
    RSA.Verify.checkL1ScoreGt cfg .bad .h1 .bad .h3 = true := by
  native_decide

/-- "good" → h2: L1 assigns more mass to h2 than h0. -/
theorem good_map_h2_vs_h0 :
    RSA.Verify.checkL1ScoreGt cfg .good .h2 .good .h0 = true := by
  native_decide

/-- "good" → h2: L1 assigns more mass to h2 than h3. -/
theorem good_map_h2_vs_h3 :
    RSA.Verify.checkL1ScoreGt cfg .good .h2 .good .h3 = true := by
  native_decide

/-- "amazing" → h3: L1 assigns more mass to h3 than h0. -/
theorem amazing_map_h3_vs_h0 :
    RSA.Verify.checkL1ScoreGt cfg .amazing .h3 .amazing .h0 = true := by
  native_decide

/-- "amazing" → h3: L1 assigns more mass to h3 than h2. -/
theorem amazing_map_h3_vs_h2 :
    RSA.Verify.checkL1ScoreGt cfg .amazing .h3 .amazing .h2 = true := by
  native_decide

-- ============================================================================
-- §5. State Inference: Negated Utterances
-- ============================================================================

/-- "not terrible" shifts away from h0: L1 prefers h1 over h0.
    Negation makes bad states more acceptable, so the listener infers
    the state is "not the worst" rather than "the worst". -/
theorem not_terrible_away_from_h0 :
    RSA.Verify.checkL1ScoreGt cfg .notTerrible .h1 .notTerrible .h0 = true := by
  native_decide

/-- "not bad" peaks at h2: L1 prefers h2 over h3.
    "Not bad" is most compatible with moderate-good states. -/
theorem not_bad_peaks_h2 :
    RSA.Verify.checkL1ScoreGt cfg .notBad .h2 .notBad .h3 = true := by
  native_decide

-- ============================================================================
-- §6. Speaker Behavior: Informativity vs Social Goals
-- ============================================================================

/-- At h0, a purely informative speaker (φ=1) prefers "terrible" over
    "not terrible". Direct speech maximizes informativity. -/
theorem informative_prefers_direct :
    RSA.Verify.checkS1PolicyGt cfg .p100 .h0 .terrible .notTerrible = true := by
  native_decide

/-- At h0, a purely social speaker (φ=0) prefers "not terrible" over
    "terrible". Indirect speech maximizes social value: E[V|"not terrible"]
    is much higher than E[V|"terrible"] because L0 assigns probability
    to high-value states. -/
theorem social_prefers_indirect :
    RSA.Verify.checkS1PolicyGt cfg .p0 .h0 .notTerrible .terrible = true := by
  native_decide

/-- Even at φ=1/4, the speaker still prefers "terrible" over "not terrible"
    at h0. The informativity penalty of "not terrible" at h0 (log L0 ≈ −4.1)
    outweighs the social benefit until φ drops to 0.
    This shows the crossover is between φ=0 and φ=1/4. -/
theorem slight_informativity_prefers_direct :
    RSA.Verify.checkS1PolicyGt cfg .p25 .h0 .terrible .notTerrible = true := by
  native_decide

/-- At h3, a purely social speaker prefers "amazing" over "good".
    Even without informativity concerns, the higher expected social value
    from "amazing" (which concentrates L0 on h3) drives the preference. -/
theorem social_prefers_positive :
    RSA.Verify.checkS1PolicyGt cfg .p0 .h3 .amazing .good = true := by
  native_decide

/-- At h3, a purely informative speaker prefers "amazing" over "not amazing".
    Direct positive speech is more informative. -/
theorem informative_prefers_direct_positive :
    RSA.Verify.checkS1PolicyGt cfg .p100 .h3 .amazing .notAmazing = true := by
  native_decide

-- ============================================================================
-- §7. Structural Properties
-- ============================================================================

/-- The model uses soft semantics: meaning values are in [0,1]. -/
theorem meaning_bounded : ∀ u s, 0 ≤ utteranceSemantics u s ∧ utteranceSemantics u s ≤ 1 := by
  intro u s; cases u <;> cases s <;>
  simp only [utteranceSemantics, adjMeaning, softNot, softSemantics] <;>
  constructor <;> norm_num

/-- Negated utterances cost more than direct ones. -/
theorem negation_costlier' : ∀ u : Utterance, u.isNegated → utteranceCost u = 3 := by
  intro u h; cases u <;> simp [Utterance.isNegated] at h <;> rfl

/-- Direct utterances cost less. -/
theorem direct_cheaper : ∀ u : Utterance, ¬u.isNegated → utteranceCost u = 2 := by
  intro u h; cases u <;> simp [Utterance.isNegated] at h <;> rfl

end Phenomena.Politeness.Studies.YoonEtAl2020RSA
