import Linglib.Core.Agent.BToM

/-!
# Emotion as Post-Inference Appraisal @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}

Houlihan, Kleiman-Weiner, Hewitt, Tenenbaum & Saxe (2023) show that emotions
are not primitive mental states — they are **computed** from more basic cognitive
variables via a three-layer architecture:

1. **Inverse Planning** (= BToM): observe action → infer beliefs, desires, percepts
2. **Computed Appraisals**: from inferred mental states, compute appraisal variables
   across multiple utility domains (monetary, affiliation, social equity)
3. **Emotion Concepts**: each emotion is a specific qualitative pattern (β weights)
   over the shared appraisal space — a linear readout with logistic transform

The key architectural claims:

- Appraisals are **post-inference**: computed FROM existing BToM posteriors
  without adding new latent variables to the generative model.
- The **same** appraisal variables are computed for all emotions; different emotions
  are different readout patterns (β vectors) over the shared appraisal space.
- All 20 emotion concepts are **retrospective**: they presuppose an observed
  outcome. Prospective emotions (hope, fear, dread) require different
  computations over uncertain future outcomes.

## Appraisal Dimensions

The paper computes appraisals along four types × two perspectives:

| Type | Definition | BToM Component |
|------|------------|----------------|
| AU   | U(outcome \| preferences) | Desire marginal |
| PE   | outcome − E[outcome \| beliefs] | Belief expectation |
| CFa  | U(agent's alternative) − U(actual) | Planning model |
| CFo  | U(opponent's alternative) − U(actual) | Planning model |

| Perspective | Meaning |
|-------------|---------|
| Base | Direct outcomes: monetary + social utility |
| Reputational | How the agent's choices appear to others |

The paper's full model decomposes base utility into three domains
(monetary, affiliation, social equity), yielding an 18-dimensional
appraisal space. Our qualitative profiles collapse these base domains
into a single "base" perspective (4 types × 2 perspectives = 8 dimensions),
which suffices to uniquely characterize all 20 emotion concepts.

## References

- Houlihan, S. D., Kleiman-Weiner, M., Hewitt, L. B., Tenenbaum, J. B., &
  Saxe, R. (2023). Emotion prediction as computation over a generative model
  of the world. Phil. Trans. R. Soc. A 381: 20220047.
-/

namespace Core.Agent.Emotion

-- ════════════════════════════════════════════════════════════════
-- § 1. Core Types
-- ════════════════════════════════════════════════════════════════

/-- The four appraisal computation types from Houlihan et al. (2023).

Each type is a different way of evaluating an outcome relative
to the agent's inferred mental states:

- **AU**: value of actual outcome given preferences
- **PE**: actual outcome minus expected outcome given beliefs
- **CFa**: utility of agent's alternative action minus actual
- **CFo**: utility of opponent's alternative action minus actual -/
inductive AppraisalType where
  | achievedUtility        -- AU: U(outcome | preferences)
  | predictionError        -- PE: outcome − E[outcome | beliefs]
  | counterfactualAgent    -- CFa: U(agent alt) − U(actual)
  | counterfactualOpponent -- CFo: U(opponent alt) − U(actual)
  deriving DecidableEq, BEq, Repr

/-- Perspective for appraisal computation.

The paper's full model has three base utility domains (monetary, affiliation,
social equity) plus reputational utility. We collapse the three base domains
into a single "base" perspective, capturing the key structural distinction:
base appraisals evaluate direct outcomes, reputational appraisals evaluate
how the agent's choices appear to others. -/
inductive AppraisalPerspective where
  | base          -- Direct outcomes (monetary + social)
  | reputational  -- Social perception
  deriving DecidableEq, BEq, Repr

/-- Qualitative sign of an appraisal dimension in an emotion profile.

Rather than modeling continuous β weights, we capture the qualitative
structure: whether high values of a given appraisal dimension increase
the emotion (+), decrease it (−), or are irrelevant (·). Abstracted
from the learned transformation in Houlihan et al.'s Fig. 4. -/
inductive AppraisalSign where
  | positive    -- High values increase the emotion (β > 0)
  | negative    -- High values decrease the emotion (β < 0)
  | irrelevant  -- Does not contribute (β ≈ 0)
  deriving DecidableEq, BEq, Repr

/-- Temporal orientation of an emotion.

Retrospective emotions presuppose an observed outcome and evaluate it
against the agent's inferred mental states. Prospective emotions (hope,
fear, dread) concern uncertain future outcomes and require expected
utility computations — a fundamentally different appraisal architecture
not covered by the current model.

All 20 emotion concepts in Houlihan et al. are retrospective. -/
inductive TemporalOrientation where
  | retrospective  -- After outcome: evaluation of what happened
  | prospective    -- Before outcome: anticipation under uncertainty
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2. Appraisal Computation from BToM Marginals
-- ════════════════════════════════════════════════════════════════

section AppraisalComputation
open Core.BToM

variable {F : Type*} [CommSemiring F]
variable {A P B D S M W : Type*}
  [Fintype P] [Fintype B] [Fintype D] [Fintype S] [Fintype M] [Fintype W]

/-- Achieved Utility from BToM desire marginals.

    AU(a, w) = Σ_d P(d | a) · U(w, d)

The desire marginal P(d | a) is the observer's posterior over what the
agent wanted, given the observed action. Weighting by utility U(w, d)
yields the expected value of the actual outcome under the inferred desires.

This is the core post-inference property: AU is a function of the BToM
posterior, not a primitive input to the model. -/
def achievedUtility (model : BToMModel F A P B D S M W)
    (utility : W → D → F) (action : A) (world : W) : F :=
  ∑ d : D, model.desireMarginal action d * utility world d

/-- Prediction Error from BToM belief expectation.

    PE(a, w) = outcome(w) − E_B[prediction(b) | a]

The belief expectation is the observer's posterior-weighted average of
what the agent believed would happen. The difference from the actual
outcome measures surprise. -/
def predictionError [AddCommGroup F] (model : BToMModel F A P B D S M W)
    (outcome : W → F) (beliefPrediction : B → F) (action : A) (world : W) : F :=
  outcome world - model.beliefExpectation beliefPrediction action

/-- Counterfactual Appraisal: utility difference from alternative action.

    CF(a_actual, a_alt, w) = U(w, a_alt) − U(w, a_actual)

Serves as both CFa (agent counterfactual) and CFo (opponent counterfactual)
depending on which agent's action space is being varied:
- CFa: `altAction` ranges over the focal agent's alternative actions
- CFo: `altAction` ranges over the opponent's alternative actions

Positive values mean the alternative would have been better. -/
def counterfactualAppraisal (utility : W → A → F) [AddCommGroup F]
    (actualAction altAction : A) (world : W) : F :=
  utility world altAction - utility world actualAction

/-- AU is a desire-marginal weighted sum — structurally post-inference. -/
theorem au_from_btom_marginals (model : BToMModel F A P B D S M W)
    (utility : W → D → F) (action : A) (world : W) :
    achievedUtility model utility action world =
    ∑ d : D, model.desireMarginal action d * utility world d := rfl

/-- PE uses beliefExpectation — structurally post-inference. -/
theorem pe_uses_belief_expectation [AddCommGroup F] (model : BToMModel F A P B D S M W)
    (outcome : W → F) (beliefPrediction : B → F) (action : A) (world : W) :
    predictionError model outcome beliefPrediction action world =
    outcome world - model.beliefExpectation beliefPrediction action := rfl

end AppraisalComputation

-- ════════════════════════════════════════════════════════════════
-- § 3. Emotion Profiles
-- ════════════════════════════════════════════════════════════════

/-- Appraisal weights for a single appraisal type, split by perspective. -/
structure PerspectiveWeights where
  base : AppraisalSign
  reputational : AppraisalSign
  deriving DecidableEq, BEq, Repr

/-- The 4 × 2 qualitative appraisal weight matrix for an emotion concept.

Each of the four appraisal types has a base and reputational weight,
yielding 8 qualitative dimensions. This is our abstraction of the
paper's full 18-dimensional learned β weight matrix (Fig. 4),
collapsing monetary + affiliation + social equity into "base." -/
structure AppraisalWeights where
  au  : PerspectiveWeights  -- Achieved utility
  pe  : PerspectiveWeights  -- Prediction error
  cfa : PerspectiveWeights  -- Counterfactual (agent)
  cfo : PerspectiveWeights  -- Counterfactual (opponent)
  deriving DecidableEq, BEq, Repr

/-- An emotion concept as a qualitative pattern over the appraisal space.

The paper's central claim: each emotion is a specific readout pattern
(β weight vector) over the shared set of computed appraisals. Different
emotions = different patterns over the SAME underlying variables.
The readout is applied identically for all emotions (eq. 8.2):

    P(e | ψ) ∝ exp(β_e · ψ + b_e) -/
structure EmotionProfile where
  name : String
  weights : AppraisalWeights
  orientation : TemporalOrientation
  deriving DecidableEq, BEq, Repr

/-- Look up the qualitative sign for a specific appraisal type and perspective. -/
def AppraisalWeights.getSign (w : AppraisalWeights)
    (t : AppraisalType) (p : AppraisalPerspective) : AppraisalSign :=
  match t, p with
  | .achievedUtility, .base => w.au.base
  | .achievedUtility, .reputational => w.au.reputational
  | .predictionError, .base => w.pe.base
  | .predictionError, .reputational => w.pe.reputational
  | .counterfactualAgent, .base => w.cfa.base
  | .counterfactualAgent, .reputational => w.cfa.reputational
  | .counterfactualOpponent, .base => w.cfo.base
  | .counterfactualOpponent, .reputational => w.cfo.reputational

/-- All base (non-reputational) dimensions are irrelevant. -/
def EmotionProfile.isPurelyReputational (e : EmotionProfile) : Bool :=
  e.weights.au.base == .irrelevant && e.weights.pe.base == .irrelevant &&
  e.weights.cfa.base == .irrelevant && e.weights.cfo.base == .irrelevant

-- ════════════════════════════════════════════════════════════════
-- § 4. The 20 Emotion Concepts
-- ════════════════════════════════════════════════════════════════

/-! Qualitative profiles abstracted from the learned β weights in
Houlihan et al.'s Fig. 4. Convention: `.positive` = β > 0 (high appraisal
values increase emotion), `.negative` = β < 0, `.irrelevant` = β ≈ 0.

Each definition specifies: `⟨name, ⟨au, pe, cfa, cfo⟩, orientation⟩`
where each of `au, pe, cfa, cfo` is `⟨base, reputational⟩`.

| Emotion        | AU_b | AU_r | PE_b | PE_r | CFa_b | CFa_r | CFo_b | CFo_r |
|----------------|------|------|------|------|-------|-------|-------|-------|
| joy            |  +   |  ·   |  +   |  ·   |   ·   |   ·   |   ·   |   ·   |
| surprise       |  ·   |  ·   |  +   |  ·   |   ·   |   ·   |   ·   |   ·   |
| pride          |  +   |  +   |  ·   |  ·   |   +   |   ·   |   ·   |   ·   |
| gratitude      |  +   |  ·   |  +   |  ·   |   ·   |   ·   |   −   |   ·   |
| relief         |  +   |  ·   |  +   |  ·   |   −   |   ·   |   ·   |   ·   |
| amusement      |  +   |  ·   |  +   |  ·   |   ·   |   ·   |   +   |   ·   |
| disappointment |  −   |  ·   |  −   |  ·   |   +   |   ·   |   ·   |   ·   |
| annoyance      |  −   |  ·   |  −   |  ·   |   ·   |   ·   |   ·   |   ·   |
| fury           |  −   |  −   |  −   |  ·   |   ·   |   ·   |   ·   |   ·   |
| embarrassment  |  ·   |  −   |  ·   |  −   |   ·   |   −   |   ·   |   ·   |
| regret         |  −   |  ·   |  ·   |  ·   |   −   |   ·   |   ·   |   ·   |
| guilt          |  ·   |  −   |  ·   |  ·   |   ·   |   −   |   ·   |   ·   |
| disgust        |  −   |  −   |  ·   |  ·   |   ·   |   ·   |   ·   |   ·   |
| devastation    |  −   |  ·   |  −   |  ·   |   ·   |   ·   |   −   |   ·   |
| contempt       |  ·   |  −   |  ·   |  ·   |   ·   |   ·   |   ·   |   ·   |
| respect        |  ·   |  +   |  ·   |  ·   |   ·   |   ·   |   ·   |   ·   |
| envy           |  −   |  ·   |  ·   |  ·   |   ·   |   ·   |   +   |   ·   |
| sympathy       |  ·   |  ·   |  ·   |  −   |   ·   |   ·   |   ·   |   −   |
| confusion      |  ·   |  ·   |  +   |  +   |   ·   |   ·   |   ·   |   ·   |
| excitement     |  +   |  ·   |  +   |  +   |   ·   |   ·   |   ·   |   ·   |
-/

private abbrev O : PerspectiveWeights := ⟨.irrelevant, .irrelevant⟩

def joy : EmotionProfile :=
  ⟨"joy", ⟨⟨.positive, .irrelevant⟩, ⟨.positive, .irrelevant⟩, O, O⟩, .retrospective⟩

def surprise : EmotionProfile :=
  ⟨"surprise", ⟨O, ⟨.positive, .irrelevant⟩, O, O⟩, .retrospective⟩

def pride : EmotionProfile :=
  ⟨"pride", ⟨⟨.positive, .positive⟩, O, ⟨.positive, .irrelevant⟩, O⟩, .retrospective⟩

def gratitude : EmotionProfile :=
  ⟨"gratitude", ⟨⟨.positive, .irrelevant⟩, ⟨.positive, .irrelevant⟩, O,
    ⟨.negative, .irrelevant⟩⟩, .retrospective⟩

def relief : EmotionProfile :=
  ⟨"relief", ⟨⟨.positive, .irrelevant⟩, ⟨.positive, .irrelevant⟩,
    ⟨.negative, .irrelevant⟩, O⟩, .retrospective⟩

def amusement : EmotionProfile :=
  ⟨"amusement", ⟨⟨.positive, .irrelevant⟩, ⟨.positive, .irrelevant⟩, O,
    ⟨.positive, .irrelevant⟩⟩, .retrospective⟩

def disappointment : EmotionProfile :=
  ⟨"disappointment", ⟨⟨.negative, .irrelevant⟩, ⟨.negative, .irrelevant⟩,
    ⟨.positive, .irrelevant⟩, O⟩, .retrospective⟩

def annoyance : EmotionProfile :=
  ⟨"annoyance", ⟨⟨.negative, .irrelevant⟩, ⟨.negative, .irrelevant⟩, O, O⟩, .retrospective⟩

def fury : EmotionProfile :=
  ⟨"fury", ⟨⟨.negative, .negative⟩, ⟨.negative, .irrelevant⟩, O, O⟩, .retrospective⟩

def embarrassment : EmotionProfile :=
  ⟨"embarrassment", ⟨⟨.irrelevant, .negative⟩, ⟨.irrelevant, .negative⟩,
    ⟨.irrelevant, .negative⟩, O⟩, .retrospective⟩

def regret : EmotionProfile :=
  ⟨"regret", ⟨⟨.negative, .irrelevant⟩, O, ⟨.negative, .irrelevant⟩, O⟩, .retrospective⟩

def guilt : EmotionProfile :=
  ⟨"guilt", ⟨⟨.irrelevant, .negative⟩, O, ⟨.irrelevant, .negative⟩, O⟩, .retrospective⟩

def disgust : EmotionProfile :=
  ⟨"disgust", ⟨⟨.negative, .negative⟩, O, O, O⟩, .retrospective⟩

def devastation : EmotionProfile :=
  ⟨"devastation", ⟨⟨.negative, .irrelevant⟩, ⟨.negative, .irrelevant⟩, O,
    ⟨.negative, .irrelevant⟩⟩, .retrospective⟩

def contempt : EmotionProfile :=
  ⟨"contempt", ⟨⟨.irrelevant, .negative⟩, O, O, O⟩, .retrospective⟩

def respect : EmotionProfile :=
  ⟨"respect", ⟨⟨.irrelevant, .positive⟩, O, O, O⟩, .retrospective⟩

def envy : EmotionProfile :=
  ⟨"envy", ⟨⟨.negative, .irrelevant⟩, O, O, ⟨.positive, .irrelevant⟩⟩, .retrospective⟩

def sympathy : EmotionProfile :=
  ⟨"sympathy", ⟨O, ⟨.irrelevant, .negative⟩, O, ⟨.irrelevant, .negative⟩⟩, .retrospective⟩

def confusion : EmotionProfile :=
  ⟨"confusion", ⟨O, ⟨.positive, .positive⟩, O, O⟩, .retrospective⟩

def excitement : EmotionProfile :=
  ⟨"excitement", ⟨⟨.positive, .irrelevant⟩, ⟨.positive, .positive⟩, O, O⟩, .retrospective⟩

/-- All 20 emotion concepts from Houlihan et al. (2023). -/
def allEmotions : List EmotionProfile :=
  [joy, surprise, pride, gratitude, relief, amusement,
   disappointment, annoyance, fury, embarrassment,
   regret, guilt, disgust, devastation,
   contempt, respect, envy, sympathy, confusion, excitement]

-- ════════════════════════════════════════════════════════════════
-- § 5. Structural Theorems
-- ════════════════════════════════════════════════════════════════

theorem twenty_emotions : allEmotions.length = 20 := by native_decide

/-- All 20 emotions have distinct appraisal weight patterns.
    This is the paper's central empirical finding (Fig. 4):
    "the learned appraisal structure is unique for each emotion." -/
theorem appraisal_patterns_distinguishable :
    (allEmotions.map (·.weights)).Pairwise (· ≠ ·) := by native_decide

/-- All 20 emotions in the model are retrospective (post-outcome).
    The paper explicitly excludes prospective emotions: "we target
    retrospective emotions... and did not include prospective emotions
    that concern uncertain future events (e.g. hope, fear)" (p. 22). -/
theorem all_retrospective :
    (allEmotions.all (·.orientation == .retrospective)) = true := by native_decide

/-- Embarrassment is purely reputational: all base dimensions are irrelevant. -/
theorem embarrassment_purely_reputational :
    embarrassment.isPurelyReputational = true := by native_decide

end Core.Agent.Emotion
