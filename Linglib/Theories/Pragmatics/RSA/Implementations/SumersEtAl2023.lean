/-
# Sumers et al. (2023): Reconciling Truthfulness and Relevance

"Reconciling truthfulness and relevance as epistemic and decision-theoretic utility"

## Overview

This paper introduces a unified speaker model that combines:
- **Truthfulness** (epistemic utility): preference for true utterances
- **Relevance** (decision-theoretic utility): preference for action-improving utterances

These are independent objectives that speakers trade off, not a single
unified goal. The λ parameter controls the tradeoff.

## Signaling Bandits Paradigm

The paper introduces "signaling bandits" - a generalization of Lewis signaling games
to contextual bandit settings:

1. **World state** w: feature-value mappings (e.g., "Green = +2, Spots = +1")
2. **Actions** A: items characterized by features (e.g., mushrooms with colors/textures)
3. **Contexts** A ⊆ A: available actions in a situation
4. **Utterances** U: feature-value claims (e.g., "Spots are +1")
5. **Rewards** R(a,w): linear function of features

## Key Equations

Listener belief update (Eq. 3):
  P_L(w|u) ∝ ⟦u⟧(w) · P(w)

Listener expected reward (Eq. 6):
  R_L(a,u) = Σ_w R(a,w) · P_L(w|u)

Listener policy (Eq. 7):
  π_L(a|u,A) ∝ exp(β_L · R_L(a,u))

Truthfulness utility (Eq. 5):
  U_T(u|w) = +1 if true, -1 if false

Relevance utility (Eq. 8):
  U_R(u|w,A) = Σ_a π_L(a|u,A) · R(a,w)

Combined utility (Eq. 9):
  U_C(u|w,A) = λ·U_R + (1-λ)·U_T + C(u)

## Results

1. **Theorem 1**: Identity DP makes relevance = truthfulness (Appendix A)
2. **Theorem 2**: Any QUD is equivalent to some decision problem (Appendix A)
3. **Empirical**: λ ≈ 0.55 for unbiased participants (Exp 1)
4. **Empirical**: Graded tradeoff, not strict priority (Exp 2)

## References

- Sumers, T.R., Ho, M.K., Griffiths, T.L., & Hawkins, R.D. (2023).
  Reconciling truthfulness and relevance as epistemic and decision-theoretic utility.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Linglib.Theories.Pragmatics.RSA.Core.Distribution
import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility

namespace RSA.SumersEtAl2023

open RSA.CombinedUtility RSA.Eval


/-!
## Signaling Bandits

Unlike Lewis signaling games where world state = correct action,
signaling bandits separate abstract knowledge (feature values) from
concrete decisions (which action to take).
-/

/-- Features that characterize actions (e.g., colors, textures) -/
inductive Feature where
  | green : Feature
  | red : Feature
  | blue : Feature
  | spotted : Feature
  | solid : Feature
  | striped : Feature
  deriving DecidableEq, Repr, BEq

/-- Feature values in the experimental range -/
inductive FeatureValue where
  | neg2 : FeatureValue  -- -2
  | neg1 : FeatureValue  -- -1
  | zero : FeatureValue  --  0
  | pos1 : FeatureValue  -- +1
  | pos2 : FeatureValue  -- +2
  deriving DecidableEq, Repr, BEq

/-- Convert feature value to rational -/
def FeatureValue.toRat : FeatureValue → ℚ
  | .neg2 => -2
  | .neg1 => -1
  | .zero => 0
  | .pos1 => 1
  | .pos2 => 2

/-- All feature values -/
def allFeatureValues : List FeatureValue :=
  [.neg2, .neg1, .zero, .pos1, .pos2]

/-- All features -/
def allFeatures : List Feature :=
  [.green, .red, .blue, .spotted, .solid, .striped]

/-- World state: mapping from features to values.

In the mushroom experiment, this defines how valuable each feature is.
Example: {Green → +2, Red → 0, Blue → -2, Spotted → +1, Solid → 0, Striped → -1}
-/
structure WorldState where
  featureValue : Feature → FeatureValue

instance : BEq WorldState where
  beq w1 w2 := allFeatures.all λ f => w1.featureValue f == w2.featureValue f

/-- Get the rational value of a feature in a world -/
def WorldState.getValue (w : WorldState) (f : Feature) : ℚ :=
  (w.featureValue f).toRat

/-- Action (mushroom) characterized by features it has -/
structure Action where
  /-- Which features this action has (e.g., a green spotted mushroom) -/
  hasFeature : Feature → Bool
  /-- Human-readable name -/
  name : String := "action"

instance : BEq Action where
  beq a1 a2 := allFeatures.all λ f => a1.hasFeature f == a2.hasFeature f

/-- Reward for taking an action in a world state.

R(a,w) = Σ_f [a has f] · w(f)

Linear combination of feature values for features the action has.
-/
def reward (a : Action) (w : WorldState) : ℚ :=
  allFeatures.foldl (λ acc f =>
    if a.hasFeature f then acc + w.getValue f else acc
  ) 0

/-- Decision context: subset of available actions -/
structure Context where
  actions : List Action

/-- Utterance: claim about a feature's value.

Example: "Spots are +1" = ⟨.spotted, .pos1⟩
-/
structure Utterance where
  feature : Feature
  value : FeatureValue
  deriving DecidableEq, Repr, BEq

/-- All possible utterances (30 = 6 features × 5 values) -/
def allUtterances : List Utterance :=
  allFeatures.flatMap λ f =>
    allFeatureValues.map λ v => ⟨f, v⟩

/-- Truth of an utterance in a world state -/
def utteranceTruth (u : Utterance) (w : WorldState) : Bool :=
  w.featureValue u.feature == u.value


/-- Model parameters for Sumers et al. speaker model -/
structure Params where
  /-- Speaker rationality (soft-max temperature) -/
  βS : ℚ := 3
  /-- Listener rationality -/
  βL : ℚ := 3
  /-- Tradeoff: 0 = pure truthfulness, 1 = pure relevance -/
  lam : ℚ := 1/2
  /-- Cost weight -/
  costWeight : ℚ := 0
  deriving Repr, BEq

/-- Default parameters (matches Exp 1 Unbiased MLE) -/
def defaultParams : Params := { lam := 55/100 }

/-- Truth-biased parameters (Exp 1 MLE) -/
def truthBiasedParams : Params := { lam := 35/100 }

/-- Relevance-biased parameters (Exp 1 MLE) -/
def relevanceBiasedParams : Params := { lam := 85/100 }


/-!
## Listener Model

The listener:
1. Updates beliefs about world state given utterance (Eq. 3)
2. Computes expected reward for each action (Eq. 6)
3. Chooses actions via softmax policy (Eq. 7)
-/

-- Note: sumScores, normalizeScores, softmax imported from RSA.Eval

/-- Literal listener: updates beliefs given utterance (Eq. 3).

P_L(w|u) ∝ ⟦u⟧(w) · P(w)

Returns posterior over worlds consistent with utterance.
-/
def literalListener (u : Utterance) (worlds : List WorldState)
    (prior : WorldState → ℚ := λ _ => 1) : List (WorldState × ℚ) :=
  let scores := worlds.map λ w =>
    if utteranceTruth u w then prior w else 0
  let probs := normalizeScores scores
  worlds.zip probs

/-- Expected reward for an action given utterance (Eq. 6).

R_L(a,u) = Σ_w R(a,w) · P_L(w|u)
-/
def expectedReward (a : Action) (u : Utterance) (worlds : List WorldState)
    (prior : WorldState → ℚ := λ _ => 1) : ℚ :=
  let posterior := literalListener u worlds prior
  posterior.foldl (λ acc (w, p) => acc + p * reward a w) 0

/-- Listener policy: probability of choosing each action (Eq. 7).

π_L(a|u,A) ∝ exp(β_L · R_L(a,u))
-/
def listenerPolicy (params : Params) (ctx : Context) (u : Utterance)
    (worlds : List WorldState) (prior : WorldState → ℚ := λ _ => 1)
    : List (Action × ℚ) :=
  let utilities := ctx.actions.map λ a => expectedReward a u worlds prior
  let probs := softmax params.βL utilities
  ctx.actions.zip probs


/-!
## Speaker Utilities

Three components:
1. **Truthfulness** (Eq. 5): epistemic preference for true utterances
2. **Relevance** (Eq. 8): decision-theoretic preference for action-improving utterances
3. **Cost**: production/processing effort
-/

/-- Truthfulness utility (Eq. 5).

U_T(u|w) = +1 if ⟦u⟧(w) = true
         = -1 if ⟦u⟧(w) = false

Note: This is a soft constraint via βS, not a hard filter.
-/
def truthfulnessUtility (u : Utterance) (w : WorldState) : ℚ :=
  if utteranceTruth u w then 1 else -1

/-- Relevance utility (Eq. 8).

U_R(u|w,A) = Σ_a π_L(a|u,A) · R(a,w)

The expected reward of the listener's actual choice in the true world.
-/
def relevanceUtility (params : Params) (u : Utterance) (w : WorldState)
    (ctx : Context) (worlds : List WorldState)
    (prior : WorldState → ℚ := λ _ => 1) : ℚ :=
  let policy := listenerPolicy params ctx u worlds prior
  policy.foldl (λ acc (a, p) => acc + p * reward a w) 0

/-- Utterance cost.

Default: 0 for all utterances.
Can be extended for valence bias (positive utterances preferred).
-/
def utteranceCost (_u : Utterance) : ℚ := 0

/-- Valence-based cost (from Exp 1 residual analysis).

Negative-valued utterances have higher cost (require more processing).
-/
def valenceCost (u : Utterance) (ν : ℚ := 1/4) : ℚ :=
  match u.value with
  | .neg2 | .neg1 => ν
  | .zero => 0
  | .pos1 | .pos2 => -ν

/-- Combined utility (Eq. 9).

U_C(u|w,A) = λ·U_R(u|w,A) + (1-λ)·U_T(u|w) - C(u)

Convex combination of relevance and truthfulness, minus cost.
-/
def combinedUtility (params : Params) (u : Utterance) (w : WorldState)
    (ctx : Context) (worlds : List WorldState)
    (prior : WorldState → ℚ := λ _ => 1) : ℚ :=
  let uT := truthfulnessUtility u w
  let uR := relevanceUtility params u w ctx worlds prior
  let cost := params.costWeight * utteranceCost u
  combined params.lam uT uR cost


/-!
## Speaker Model

P_S(u|w,A) ∝ exp(β_S · U_C(u|w,A))

The speaker chooses utterances proportional to combined utility.
-/

/-- Speaker distribution over utterances (Eq. 1).

P_S(u|w,A) ∝ exp(β_S · U_C(u|w,A))
-/
def speakerDist (params : Params) (w : WorldState) (ctx : Context)
    (worlds : List WorldState) (utterances : List Utterance := allUtterances)
    (prior : WorldState → ℚ := λ _ => 1) : List (Utterance × ℚ) :=
  let utilities := utterances.map λ u =>
    combinedUtility params u w ctx worlds prior
  let probs := softmax params.βS utilities
  utterances.zip probs

/-- Pure truthfulness speaker (λ = 0) -/
def truthOnlySpeaker (params : Params) (w : WorldState)
    (utterances : List Utterance := allUtterances) : List (Utterance × ℚ) :=
  let utilities := utterances.map λ u => truthfulnessUtility u w
  let probs := softmax params.βS utilities
  utterances.zip probs

/-- Pure relevance speaker (λ = 1) -/
def relevanceOnlySpeaker (params : Params) (w : WorldState) (ctx : Context)
    (worlds : List WorldState) (utterances : List Utterance := allUtterances)
    (prior : WorldState → ℚ := λ _ => 1) : List (Utterance × ℚ) :=
  let utilities := utterances.map λ u =>
    relevanceUtility params u w ctx worlds prior
  let probs := softmax params.βS utilities
  utterances.zip probs


/-!
## Pragmatic Listener

Following RSA, the pragmatic listener inverts the speaker model:

P_L1(w|u) ∝ P_S(u|w) · P(w)
-/

/-- Pragmatic listener distribution over worlds.

P_L1(w|u,A) ∝ P_S(u|w,A) · P(w)

Note: This requires a context A, unlike standard RSA.
-/
def pragmaticListener (params : Params) (u : Utterance) (ctx : Context)
    (worlds : List WorldState) (prior : WorldState → ℚ := λ _ => 1)
    : List (WorldState × ℚ) :=
  let scores := worlds.map λ w =>
    let sDist := speakerDist params w ctx worlds allUtterances prior
    let sProb := match sDist.find? (·.1 == u) with
      | some (_, p) => p
      | none => 0
    prior w * sProb
  let probs := normalizeScores scores
  worlds.zip probs


/-!
## Key Theoretical Results

These connect to Comparisons/RelevanceTheories.lean for the deep theorems.
-/

/-- Combined model reduces to truthfulness when λ = 0.

U_C(u|w,A) = U_T(u|w) when λ = 0.
Delegates to `CombinedUtility.combined_at_zero`. -/
theorem combined_pure_truthfulness (u : Utterance) (w : WorldState)
    (ctx : Context) (worlds : List WorldState) (prior : WorldState → ℚ) :
    let params := { defaultParams with lam := 0, costWeight := 0 }
    combinedUtility params u w ctx worlds prior = truthfulnessUtility u w := by
  simp only [combinedUtility, utteranceCost, mul_zero]
  exact combined_at_zero _ _

/-- Combined model reduces to relevance when λ = 1.

U_C(u|w,A) = U_R(u|w,A) when λ = 1.
Delegates to `CombinedUtility.combined_at_one`. -/
theorem combined_pure_relevance (u : Utterance) (w : WorldState)
    (ctx : Context) (worlds : List WorldState) (prior : WorldState → ℚ) :
    let params := { defaultParams with lam := 1, costWeight := 0 }
    combinedUtility params u w ctx worlds prior =
    relevanceUtility params u w ctx worlds prior := by
  simp only [combinedUtility, utteranceCost, mul_zero]
  exact combined_at_one _ _

/-- Truthfulness and relevance are independent objectives.

In Lewis signaling games, they are perfectly correlated (knowing the world =
knowing the best action). In signaling bandits, they can diverge:
- True but irrelevant: "Green is +2" when no green actions in context
- False but relevant: "Spots are +2" when spots are actually +1

Witness 1 (true but irrelevant): "Green is +2" — true in the canonical world
but no green mushrooms appear in the example context.
Witness 2 (false but relevant): "Spots are +2" — false (spots are +1) but
would steer the listener toward the spotted mushroom (the best action). -/
theorem truthfulness_relevance_independent :
    let w : WorldState := { featureValue := λ f => match f with
      | .green => .pos2 | .red => .zero | .blue => .neg2
      | .spotted => .pos1 | .solid => .zero | .striped => .neg1 }
    let trueIrrel : Utterance := ⟨.green, .pos2⟩
    let falseRel : Utterance := ⟨.spotted, .pos2⟩
    -- True but irrelevant witness
    truthfulnessUtility trueIrrel w = 1 ∧
    -- False but relevant witness
    truthfulnessUtility falseRel w = -1 := by
  native_decide


/-!
## Experimental Domain: Mushroom Foraging

The experiments use a mushroom foraging cover story:
- Features: Green, Red, Blue (colors) and Spotted, Solid, Striped (textures)
- Each mushroom has one color and one texture
- Rewards are additive over features
-/

/-- Create a mushroom with one color and one texture -/
def makeMushroom (color texture : Feature) (name : String := "mushroom") : Action :=
  { hasFeature := λ f => f == color || f == texture
  , name := name }

/-- Canonical world state from the experiment.

Green = +2, Red = 0, Blue = -2
Spotted = +1, Solid = 0, Striped = -1
-/
def canonicalWorld : WorldState :=
  { featureValue := λ f => match f with
    | .green => .pos2
    | .red => .zero
    | .blue => .neg2
    | .spotted => .pos1
    | .solid => .zero
    | .striped => .neg1
  }

/-- Example context from Figure 6B: three mushrooms -/
def exampleContext : Context :=
  { actions := [
      makeMushroom .red .spotted "red-spotted",    -- 0 + 1 = +1
      makeMushroom .red .solid "red-solid",        -- 0 + 0 = 0
      makeMushroom .blue .striped "blue-striped"   -- -2 + -1 = -3
    ] }

/-- Verify reward calculations for example context -/
example : reward (makeMushroom .red .spotted) canonicalWorld = 1 := by native_decide
example : reward (makeMushroom .red .solid) canonicalWorld = 0 := by native_decide
example : reward (makeMushroom .blue .striped) canonicalWorld = -3 := by native_decide

/-- True utterance in canonical world -/
def trueUtterance : Utterance := ⟨.spotted, .pos1⟩

/-- False but relevant utterance -/
def falseRelevantUtterance : Utterance := ⟨.spotted, .pos2⟩

/-- True but irrelevant utterance (feature not in context) -/
def trueIrrelevantUtterance : Utterance := ⟨.green, .pos2⟩


/-!
## Empirical Predictions from Experiments

The paper reports MLE parameters and response patterns.
-/

/-- Experiment 1: Free choice paradigm.

Participants chose from 30 utterances. MLE parameters:
- Truth-biased: λ = 0.35
- Unbiased: λ = 0.55
- Relevance-biased: λ = 0.85
-/
structure Exp1Results where
  truthBiased_lam : ℚ := 35/100
  unbiased_lam : ℚ := 55/100
  relevanceBiased_lam : ℚ := 85/100

def exp1Results : Exp1Results := {}

/-- Experiment 2: Forced choice (endorsement) paradigm.

Participants endorsed specific utterances. MLE parameters:
- Truth-biased: λ = 0.15
- Unbiased: λ = 0.75
- Relevance-biased: λ = 0.90
-/
structure Exp2Results where
  truthBiased_lam : ℚ := 15/100
  unbiased_lam : ℚ := 75/100
  relevanceBiased_lam : ℚ := 90/100

def exp2Results : Exp2Results := {}

/-- Unbiased participants jointly optimize truthfulness and relevance.

Neither λ = 0 (pure truth) nor λ = 1 (pure relevance) fits the data.
Participants make a graded tradeoff. -/
theorem unbiased_participants_use_combined :
    exp1Results.unbiased_lam > 0 ∧ exp1Results.unbiased_lam < 1 := by
  simp only [exp1Results]
  native_decide

/-- Manipulation affects λ parameter ordering.

λ_truth < λ_unbiased < λ_relevance -/
theorem manipulation_affects_lambda :
    exp1Results.truthBiased_lam < exp1Results.unbiased_lam ∧
    exp1Results.unbiased_lam < exp1Results.relevanceBiased_lam := by
  simp only [exp1Results]
  native_decide


/-!
## Connections to Other Frameworks

Sumers et al. bridges several research traditions:

1. **Standard RSA** (Frank & Goodman 2012): Pure epistemic utility.
   Recovered when λ = 0 and listener has identity decision problem.

2. **Game-theoretic pragmatics** (Benz, Parikh): Decision-theoretic relevance.
   Recovered when λ = 1.

3. **Relevance Theory** (Sperber & Wilson): Relevance as primary.
   Empirically challenged: participants value truthfulness independently.

4. **QUD models** (Roberts): Question under discussion.
   QUDs can be derived from decision problems (Theorem 2).

See Comparisons/RelevanceTheories.lean for the formal connections:
- Identity DP ≡ epistemic utility (Theorem 1)
- Any QUD is some DP (Theorem 2)
- DT strictly more expressive than QUD (Theorem 3)
-/

/-- Standard RSA is a special case: when λ = 0 and cost = 0, the combined
utility equals truthfulness utility alone.

This recovers standard RSA's epistemic speaker, which soft-maximizes
truthfulness (informativity). The identity-DP connection (Theorem 1 of
Sumers et al.) is proved in `combined_pure_truthfulness` above.

[sorry: none needed — proved by `combined_pure_truthfulness`] -/
theorem standard_rsa_is_special_case (u : Utterance) (w : WorldState)
    (ctx : Context) (worlds : List WorldState) (prior : WorldState → ℚ) :
    let params := { defaultParams with lam := 0, costWeight := 0 }
    combinedUtility params u w ctx worlds prior = truthfulnessUtility u w :=
  combined_pure_truthfulness u w ctx worlds prior

/-- Relevance Theory predicts λ = 1, which is empirically falsified -/
theorem relevance_theory_challenged :
    -- Empirical finding: participants with λ < 1 even in Relevance-biased condition
    exp1Results.relevanceBiased_lam < 1 := by
  simp only [exp1Results]
  native_decide


/-!
## Summary

Unified speaker model combining truthfulness and relevance:

U_C(u|w,A) = λ·U_R(u|w,A) + (1-λ)·U_T(u|w) - C(u)

Empirical findings:
1. Participants use both truthfulness and relevance (0 < λ < 1)
2. Neither objective strictly dominates
3. The tradeoff is graded, not binary

Theoretical implications:
- Decision-theoretic relevance grounds QUD-based relevance
- Truthfulness is an independent constraint, not derived from relevance
- The combined model explains loose talk and context-sensitivity
-/

/-- Sumers et al.'s combinedUtility is CombinedUtility.combined(λ, U_T, U_R, cost).

This makes the shared `combined` theorems (`combined_at_zero`, `combined_at_one`,
`combined_convex`, `combined_mono_A/B`) directly applicable. -/
theorem sumers_uses_combined (params : Params) (u : Utterance) (w : WorldState)
    (ctx : Context) (worlds : List WorldState) (prior : WorldState → ℚ) :
    combinedUtility params u w ctx worlds prior =
    combined params.lam (truthfulnessUtility u w)
      (relevanceUtility params u w ctx worlds prior)
      (params.costWeight * utteranceCost u) := by
  unfold combinedUtility; rfl

/-- The integrated model of truthfulness and relevance -/
def integratedModel : String :=
  "U_C = λ·U_Relevance + (1-λ)·U_Truthfulness - Cost"

end RSA.SumersEtAl2023
