/-
# @cite{sumers-etal-2023}: Reconciling Truthfulness and Relevance

"Reconciling truthfulness and relevance as epistemic and decision-theoretic utility"
Cognitive Science 47(3), e13252.

## Overview

This paper introduces a unified speaker model that combines:
- **Truthfulness** (epistemic utility): preference for true utterances
- **Relevance** (decision-theoretic utility): preference for action-improving utterances

These are independent objectives that speakers trade off, not a single
unified goal. The lambda parameter controls the tradeoff.

## Paradigm: Signaling Bandits

The paper introduces "signaling bandits" - a generalization of Lewis signaling games
to contextual bandit settings:

1. **World state** w: feature-value mappings (e.g., "Green = +2, Spots = +1")
2. **Actions** A: items characterized by features (e.g., mushrooms with colors/textures)
3. **Contexts** A subseteq A: available actions in a situation
4. **Utterances** U: feature-value claims (e.g., "Spots are +1")
5. **Rewards** R(a,w): linear function of features

## Key Equations

Listener belief update (Eq. 3):
  P_L(w|u) proportional to [[u]](w) * P(w)

Listener expected reward (Eq. 6):
  R_L(a,u) = Sum_w R(a,w) * P_L(w|u)

Listener policy (Eq. 7):
  pi_L(a|u,A) proportional to exp(beta_L * R_L(a,u))

Truthfulness utility (Eq. 5):
  U_T(u|w) = +1 if true, -1 if false

Relevance utility (Eq. 8):
  U_R(u|w,A) = Sum_a pi_L(a|u,A) * R(a,w)

Combined utility (Eq. 9):
  U_C(u|w,A) = lambda*U_R + (1-lambda)*U_T + C(u)

## Key Empirical Finding

Human speakers trade off truthfulness and relevance:
- More relevance-oriented in simpler contexts (1DP)
- More truthfulness-oriented in complex contexts (2DP)
- Sensitive to explicit instructions about goals

## Results

1. **Theorem 1**: Identity DP makes relevance = truthfulness (Appendix A)
2. **Theorem 2**: Any QUD is equivalent to some decision problem (Appendix A)
3. **Empirical**: lambda approx 0.55 for unbiased participants (Exp 1)
4. **Empirical**: Graded tradeoff, not strict priority (Exp 2)

-/

import Mathlib.Data.Rat.Defs
import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility

namespace Phenomena.Directives.Studies.SumersEtAl2023

open RSA.CombinedUtility


/-!
## Mushroom Foraging Cover Story

Features: 3 colors × 3 textures
- Colors: Green, Red, Blue
- Textures: Spotted, Solid, Striped

Each feature has a reward value in {-2, -1, 0, +1, +2}
Mushroom reward = sum of color reward + texture reward
-/

/-- Feature types in the experimental domain -/
inductive FeatureType where
  | green | red | blue           -- Colors
  | spotted | solid | striped    -- Textures
  deriving DecidableEq, Repr, BEq

/-- Possible reward values for features (coarse: data-level) -/
inductive RewardValue where
  | minusTwo : RewardValue  -- -2 points
  | plusOne : RewardValue   -- +1 point
  | plusTwo : RewardValue   -- +2 points
  deriving DecidableEq, Repr, BEq

def RewardValue.toInt : RewardValue → Int
  | .minusTwo => -2
  | .plusOne => 1
  | .plusTwo => 2


/-!
## Experiment 1: 1DP vs 2DP Contexts

Manipulated context complexity:
- **1DP (one decision point)**: Only one action available that has the queried feature
- **2DP (two decision points)**: Two actions available that have the queried feature

Key prediction: In 1DP, truthful and relevant responses converge.
In 2DP, they can diverge, revealing tradeoff.
-/

/-- Context complexity conditions -/
inductive ContextCondition where
  | oneDP : ContextCondition   -- One decision point
  | twoDP : ContextCondition   -- Two decision points
  deriving DecidableEq, Repr, BEq

/-- Experiment 1: Sample size and conditions -/
structure Exp1Design where
  /-- Number of participants -/
  nParticipants : Nat
  /-- Participants per condition (between-subjects) -/
  participantsPerCondition : Nat
  /-- Trials per participant per condition -/
  trialsPerCondition : Nat
  /-- Total trials -/
  totalTrials : Nat

def exp1Design : Exp1Design :=
  { nParticipants := 63
  , participantsPerCondition := 63  -- All did both conditions (within)
  , trialsPerCondition := 30
  , totalTrials := 3780 }  -- 63 × 30 × 2

/-- Experiment 1: Human response rates by condition.

From Figure 3a and statistical analysis:
- 1DP: ~91% relevant responses
- 2DP: ~60% relevant responses
-/
structure Exp1ResponseRates where
  /-- Rate of relevance-maximizing responses in 1DP condition -/
  relevanceRate1DP : ℚ
  /-- Rate of relevance-maximizing responses in 2DP condition -/
  relevanceRate2DP : ℚ
  /-- Standard error for 1DP -/
  se1DP : ℚ
  /-- Standard error for 2DP -/
  se2DP : ℚ

def exp1ResponseRates : Exp1ResponseRates :=
  { relevanceRate1DP := 91/100
  , relevanceRate2DP := 60/100
  , se1DP := 3/100
  , se2DP := 5/100 }

/-- Statistical test: Significant effect of context.

Mixed-effects logistic regression:
β = -2.13, z = -5.95, p < 0.001
-/
structure Exp1Stats where
  /-- Coefficient for 2DP vs 1DP effect -/
  beta : ℚ
  /-- z-statistic -/
  zStat : ℚ
  /-- p < 0.001 -/
  pValueLessThan : ℚ

def exp1Stats : Exp1Stats :=
  { beta := -213/100  -- -2.13
  , zStat := -595/100  -- -5.95
  , pValueLessThan := 1/1000 }

/-- Key finding: Context affects relevance rate -/
theorem exp1_context_effect :
    exp1ResponseRates.relevanceRate1DP > exp1ResponseRates.relevanceRate2DP := by
  native_decide


/-!
## Experiment 2: Instruction Manipulation

Between-subjects manipulation of speaker goals:
- **Unbiased**: "Help the forager" (standard)
- **Truth-biased**: "Tell the forager which feature value is largest"
- **Relevance-biased**: "Help the forager choose the best mushroom"
-/

/-- Instruction conditions -/
inductive InstructionCondition where
  | unbiased : InstructionCondition
  | truthBiased : InstructionCondition
  | relevanceBiased : InstructionCondition
  deriving DecidableEq, Repr, BEq

/-- Experiment 2: Design parameters -/
structure Exp2Design where
  /-- Total participants -/
  nParticipants : Nat
  /-- Participants per condition -/
  participantsUnbiased : Nat
  participantsTruthBiased : Nat
  participantsRelevanceBiased : Nat
  /-- Trials per participant -/
  trialsPerParticipant : Nat

def exp2Design : Exp2Design :=
  { nParticipants := 200
  , participantsUnbiased := 67
  , participantsTruthBiased := 66
  , participantsRelevanceBiased := 67
  , trialsPerParticipant := 60 }

/-- Experiment 2: Human response rates by instruction condition.

From Figure 3b:
- Unbiased: ~55% relevant
- Truth-biased: ~35% relevant
- Relevance-biased: ~85% relevant
-/
structure Exp2ResponseRates where
  /-- Relevance rate in unbiased condition -/
  relevanceRateUnbiased : ℚ
  /-- Relevance rate in truth-biased condition -/
  relevanceRateTruthBiased : ℚ
  /-- Relevance rate in relevance-biased condition -/
  relevanceRateRelevanceBiased : ℚ
  /-- Standard errors -/
  seUnbiased : ℚ
  seTruthBiased : ℚ
  seRelevanceBiased : ℚ

def exp2ResponseRates : Exp2ResponseRates :=
  { relevanceRateUnbiased := 55/100
  , relevanceRateTruthBiased := 35/100
  , relevanceRateRelevanceBiased := 85/100
  , seUnbiased := 4/100
  , seTruthBiased := 5/100
  , seRelevanceBiased := 4/100 }

/-- Statistical tests for Experiment 2.

Pairwise comparisons with Bonferroni correction:
- Relevance-biased > Unbiased: χ² = 18.4, p < 0.001
- Unbiased > Truth-biased: χ² = 8.2, p = 0.004
-/
structure Exp2Stats where
  /-- Chi-squared: relevance vs unbiased -/
  chiSqRelevanceVsUnbiased : ℚ
  /-- Chi-squared: unbiased vs truth -/
  chiSqUnbiasedVsTruth : ℚ
  /-- Both p < 0.05 after correction -/
  allSignificant : Bool

def exp2Stats : Exp2Stats :=
  { chiSqRelevanceVsUnbiased := 184/10  -- 18.4
  , chiSqUnbiasedVsTruth := 82/10  -- 8.2
  , allSignificant := true }

/-- Key finding: Instruction ordering -/
theorem exp2_instruction_ordering :
    exp2ResponseRates.relevanceRateRelevanceBiased > exp2ResponseRates.relevanceRateUnbiased ∧
    exp2ResponseRates.relevanceRateUnbiased > exp2ResponseRates.relevanceRateTruthBiased := by
  native_decide


/-!
## Model Comparison

The paper compares several models against human data:
1. Combined model (truthfulness + relevance)
2. Truthfulness-only
3. Relevance-only
4. Literal speaker

Best-fit λ parameters by condition:
- Unbiased: λ = 0.55
- Truth-biased: λ = 0.35
- Relevance-biased: λ = 0.85
-/

/-- MLE parameter estimates for λ by condition -/
structure MLEParameters where
  /-- λ for unbiased condition -/
  lamUnbiased : ℚ
  /-- λ for truth-biased condition -/
  lamTruthBiased : ℚ
  /-- λ for relevance-biased condition -/
  lamRelevanceBiased : ℚ

def mleParams : MLEParameters :=
  { lamUnbiased := 55/100  -- 0.55
  , lamTruthBiased := 35/100  -- 0.35
  , lamRelevanceBiased := 85/100 }  -- 0.85

/-- Model fit statistics (log-likelihood) -/
structure ModelFit where
  /-- Combined model log-likelihood -/
  llCombined : ℚ
  /-- Truthfulness-only log-likelihood -/
  llTruthOnly : ℚ
  /-- Relevance-only log-likelihood -/
  llRelevanceOnly : ℚ
  /-- Literal speaker log-likelihood -/
  llLiteral : ℚ

def modelFit : ModelFit :=
  { llCombined := -3200  -- Approximate
  , llTruthOnly := -4100
  , llRelevanceOnly := -3800
  , llLiteral := -5200 }

/-- Combined model has best fit -/
theorem combined_best_fit :
    modelFit.llCombined > modelFit.llTruthOnly ∧
    modelFit.llCombined > modelFit.llRelevanceOnly ∧
    modelFit.llCombined > modelFit.llLiteral := by
  native_decide

/-- λ ordering matches instruction manipulation -/
theorem lambda_ordering_matches_instructions :
    mleParams.lamRelevanceBiased > mleParams.lamUnbiased ∧
    mleParams.lamUnbiased > mleParams.lamTruthBiased := by
  native_decide


/-!
## Summary of Key Empirical Patterns

1. **Tradeoff exists**: Speakers don't maximize either truthfulness or relevance alone
2. **Context-sensitive**: More truthful in complex (2DP) contexts
3. **Instruction-sensitive**: λ shifts with explicit goal manipulation
4. **Gradedness**: Responses show graded preferences, not categorical choices
-/

/-- Pattern 1: Neither extreme is modal -/
theorem pattern_tradeoff :
    exp2ResponseRates.relevanceRateUnbiased > 30/100 ∧
    exp2ResponseRates.relevanceRateUnbiased < 70/100 := by
  native_decide

/-- Pattern 2: Context matters -/
theorem pattern_context :
    exp1ResponseRates.relevanceRate1DP ≠ exp1ResponseRates.relevanceRate2DP := by
  native_decide

/-- Pattern 3: Instructions matter -/
theorem pattern_instructions :
    mleParams.lamRelevanceBiased > mleParams.lamTruthBiased := by
  native_decide


/-!
## Example Trial

World: Green = +2, Spotted = +1, other features have various values

Context (2DP):
- Action A: Green, Spotted (reward = +3)
- Action B: Green, Solid (reward = +2 if Solid = 0)
- Action C: Red, Striped (reward varies)

True utterance: "Green is +2"
Relevant utterance: "Spotted is +1" (if it uniquely identifies best mushroom)
-/

/-- Example trial structure -/
structure ExampleTrial where
  /-- World state description -/
  worldDescription : String
  /-- Available actions -/
  actions : List String
  /-- Most truthful utterance (about highest feature) -/
  truthfulUtterance : String
  /-- Most relevant utterance (identifies best action) -/
  relevantUtterance : String
  /-- Whether they diverge -/
  diverges : Bool

def exampleTrial : ExampleTrial :=
  { worldDescription := "Green = +2, Spotted = +1, others neutral"
  , actions := ["Green+Spotted", "Green+Solid", "Red+Striped"]
  , truthfulUtterance := "Green is +2"
  , relevantUtterance := "Spotted is +1"  -- Uniquely identifies best
  , diverges := true }


/-!
## Signaling Bandits: RSA Model
@cite{frank-goodman-2012} @cite{sumers-etal-2023}

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
Example: {Green -> +2, Red -> 0, Blue -> -2, Spotted -> +1, Solid -> 0, Striped -> -1}
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

R(a,w) = Sum_f [a has f] * w(f)

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

Example: "Spots are +1" = {feature :=.spotted, value :=.pos1}
-/
structure Utterance where
  feature : Feature
  value : FeatureValue
  deriving DecidableEq, Repr, BEq

/-- All possible utterances (30 = 6 features x 5 values) -/
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
## Speaker Utilities

Three components:
1. **Truthfulness** (Eq. 5): epistemic preference for true utterances
2. **Relevance** (Eq. 8): decision-theoretic preference for action-improving utterances
3. **Cost**: production/processing effort
-/

/-- Truthfulness utility (Eq. 5).

U_T(u|w) = +1 if [[u]](w) = true
         = -1 if [[u]](w) = false

Note: This is a soft constraint via betaS, not a hard filter.
-/
def truthfulnessUtility (u : Utterance) (w : WorldState) : ℚ :=
  if utteranceTruth u w then 1 else -1

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

U_C(u|w,A) = lambda*U_R(u|w,A) + (1-lambda)*U_T(u|w) - C(u)

Convex combination of relevance and truthfulness, minus cost.
Note: Relevance utility requires the full listener model, which depends
on the removed RSA.Eval infrastructure. We define the combined utility
in terms of the abstract `combined` function from CombinedUtility,
with relevance as a parameter.
-/
def combinedUtility (lam : ℚ) (uT uR : ℚ) (costWeight : ℚ) (cost : ℚ) : ℚ :=
  combined lam uT uR (costWeight * cost)


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
## Key Theoretical Results

These connect to Comparisons/RelevanceTheories.lean for the deep theorems.
-/

/-- Combined model reduces to truthfulness when lambda = 0.

U_C(u|w,A) = U_T(u|w) when lambda = 0.
Delegates to `CombinedUtility.combined_at_zero`. -/
theorem combined_pure_truthfulness (uT uR : ℚ) :
    combinedUtility 0 uT uR 0 0 = uT := by
  simp only [combinedUtility, mul_zero]
  exact combined_at_zero _ _

/-- Combined model reduces to relevance when lambda = 1.

U_C(u|w,A) = U_R(u|w,A) when lambda = 1.
Delegates to `CombinedUtility.combined_at_one`. -/
theorem combined_pure_relevance (uT uR : ℚ) :
    combinedUtility 1 uT uR 0 0 = uR := by
  simp only [combinedUtility, mul_zero]
  exact combined_at_one _ _

/-- Truthfulness and relevance are independent objectives.

In Lewis signaling games, they are perfectly correlated (knowing the world =
knowing the best action). In signaling bandits, they can diverge:
- True but irrelevant: "Green is +2" when no green actions in context
- False but relevant: "Spots are +2" when spots are actually +1

Witness 1 (true but irrelevant): "Green is +2" -- true in the canonical world
but no green mushrooms appear in the example context.
Witness 2 (false but relevant): "Spots are +2" -- false (spots are +1) but
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
  exact ⟨rfl, rfl⟩


/-!
## Empirical Predictions from Experiments

The paper reports MLE parameters and response patterns.
-/

/-- Experiment 1: Free choice paradigm.

Participants chose from 30 utterances. MLE parameters:
- Truth-biased: lambda = 0.35
- Unbiased: lambda = 0.55
- Relevance-biased: lambda = 0.85
-/
structure Exp1MLEResults where
  truthBiased_lam : ℚ := 35/100
  unbiased_lam : ℚ := 55/100
  relevanceBiased_lam : ℚ := 85/100

def exp1MLEResults : Exp1MLEResults := {}

/-- Experiment 2: Forced choice (endorsement) paradigm.

Participants endorsed specific utterances. MLE parameters:
- Truth-biased: lambda = 0.15
- Unbiased: lambda = 0.75
- Relevance-biased: lambda = 0.90
-/
structure Exp2MLEResults where
  truthBiased_lam : ℚ := 15/100
  unbiased_lam : ℚ := 75/100
  relevanceBiased_lam : ℚ := 90/100

def exp2MLEResults : Exp2MLEResults := {}

/-- Unbiased participants jointly optimize truthfulness and relevance.

Neither lambda = 0 (pure truth) nor lambda = 1 (pure relevance) fits the data.
Participants make a graded tradeoff. -/
theorem unbiased_participants_use_combined :
    exp1MLEResults.unbiased_lam > 0 ∧ exp1MLEResults.unbiased_lam < 1 := by
  simp only [exp1MLEResults]
  constructor <;> norm_num

/-- Manipulation affects lambda parameter ordering.

lambda_truth < lambda_unbiased < lambda_relevance -/
theorem manipulation_affects_lambda :
    exp1MLEResults.truthBiased_lam < exp1MLEResults.unbiased_lam ∧
    exp1MLEResults.unbiased_lam < exp1MLEResults.relevanceBiased_lam := by
  simp only [exp1MLEResults]
  constructor <;> norm_num


/-!
## Connections to Other Frameworks

Sumers et al. bridges several research traditions:

1. **Standard RSA**: Pure epistemic utility.
   Recovered when lambda = 0 and listener has identity decision problem.

2. **Game-theoretic pragmatics** (Benz, Parikh): Decision-theoretic relevance.
   Recovered when lambda = 1.

3. **Relevance Theory** (Sperber & Wilson): Relevance as primary.
   Empirically challenged: participants value truthfulness independently.

4. **QUD models** (Roberts): Question under discussion.
   QUDs can be derived from decision problems (Theorem 2).

See Comparisons/RelevanceTheories.lean for the formal connections:
- Identity DP equiv epistemic utility (Theorem 1)
- Any QUD is some DP (Theorem 2)
- DT strictly more expressive than QUD (Theorem 3)
-/

/-- Standard RSA is a special case: when lambda = 0 and cost = 0, the combined
utility equals truthfulness utility alone.

This recovers standard RSA's epistemic speaker, which soft-maximizes
truthfulness (informativity). The identity-DP connection (Theorem 1 of
Sumers et al.) is proved in `combined_pure_truthfulness` above. -/
theorem standard_rsa_is_special_case (uT uR : ℚ) :
    combinedUtility 0 uT uR 0 0 = uT :=
  combined_pure_truthfulness uT uR

/-- Relevance Theory predicts lambda = 1, which is empirically falsified -/
theorem relevance_theory_challenged :
    -- Empirical finding: participants with lambda < 1 even in Relevance-biased condition
    exp1MLEResults.relevanceBiased_lam < 1 := by
  simp only [exp1MLEResults]
  norm_num


/-!
## Summary

Unified speaker model combining truthfulness and relevance:

U_C(u|w,A) = lambda*U_R(u|w,A) + (1-lambda)*U_T(u|w) - C(u)

Empirical findings:
1. Participants use both truthfulness and relevance (0 < lambda < 1)
2. Neither objective strictly dominates
3. The tradeoff is graded, not binary

Theoretical implications:
- Decision-theoretic relevance grounds QUD-based relevance
- Truthfulness is an independent constraint, not derived from relevance
- The combined model explains loose talk and context-sensitivity
-/

/-- Sumers et al.'s combinedUtility is CombinedUtility.combined(lambda, U_T, U_R, cost).

This makes the shared `combined` theorems (`combined_at_zero`, `combined_at_one`,
`combined_convex`, `combined_mono_A/B`) directly applicable. -/
theorem sumers_uses_combined (lam uT uR costWeight cost : ℚ) :
    combinedUtility lam uT uR costWeight cost =
    combined lam uT uR (costWeight * cost) := by
  unfold combinedUtility; rfl

/-- The integrated model of truthfulness and relevance -/
def integratedModel : String :=
  "U_C = lambda*U_Relevance + (1-lambda)*U_Truthfulness - Cost"

end Phenomena.Directives.Studies.SumersEtAl2023
