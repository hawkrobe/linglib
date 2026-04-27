import Linglib.Core.Agent.BToM

/-!
# Emotion as Post-Inference Appraisal @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}

Houlihan, Kleiman-Weiner, @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023} show that emotions
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
(monetary, affiliation, social equity), yielding a 19-dimensional
appraisal space (4 types × 3 base domains × 2 perspectives, minus
some all-zero columns, plus |PE_{π_{a₂}}| for belief prediction error).
Our qualitative profiles collapse these base domains into a single
"base" perspective (4 types × 2 perspectives = 8 dimensions), which
suffices to uniquely characterize all 20 emotion concepts.

For domain-refined profiles that distinguish monetary/AIA/DIA effects,
see `RefinedAppraisalWeights` (§6) and the full instantiation in
`HoulihanEtAl2023`.

-/

namespace Core

-- ════════════════════════════════════════════════════════════════
-- § 1. Core Types
-- ════════════════════════════════════════════════════════════════

/-- The four appraisal computation types from @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}.

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
  deriving DecidableEq, Repr

/-- Perspective for appraisal computation.

The paper's full model has three base utility domains (monetary, affiliation,
social equity) plus reputational utility. We collapse the three base domains
into a single "base" perspective, capturing the key structural distinction:
base appraisals evaluate direct outcomes, reputational appraisals evaluate
how the agent's choices appear to others. -/
inductive AppraisalPerspective where
  | base          -- Direct outcomes (monetary + social)
  | reputational  -- Social perception
  deriving DecidableEq, Repr

/-- Qualitative sign of an appraisal dimension in an emotion profile.

Rather than modeling continuous β weights, we capture the qualitative
structure: whether high values of a given appraisal dimension increase
the emotion (+), decrease it (−), or are irrelevant (·). Abstracted
from the learned transformation in Houlihan et al.'s Fig. 4. -/
inductive AppraisalSign where
  | positive    -- High values increase the emotion (β > 0)
  | negative    -- High values decrease the emotion (β < 0)
  | irrelevant  -- Does not contribute (β ≈ 0)
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2. Utility Domains (Refined Decomposition)
-- ════════════════════════════════════════════════════════════════

/-- The three base utility domains from @cite{fehr-schmidt-1999} as used in
@cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}.

The qualitative `AppraisalPerspective.base` collapses these three domains
into one. For domain-refined analysis, each base appraisal has a sign for
each domain. The domain matters: *envy* loads specifically on `socialEquity`
(DIA), not on `monetary` or `affiliation`; *guilt* loads on reputational
dimensions of `affiliation` (AIA), not `monetary`. -/
inductive UtilityDomain where
  | monetary      -- Material payoff (Money)
  | affiliation   -- AIA: aversion to advantageous inequality
  | socialEquity  -- DIA: aversion to disadvantageous inequality
  deriving DecidableEq, Repr

instance : Fintype UtilityDomain where
  elems := {.monetary, .affiliation, .socialEquity}
  complete := λ x => by cases x <;> simp

/-- Qualitative appraisal sign for each utility domain.

This refines `PerspectiveWeights.base : AppraisalSign` into three
domain-specific signs, capturing the paper's 19-dimensional structure. -/
structure DomainWeights where
  monetary     : AppraisalSign
  affiliation  : AppraisalSign
  socialEquity : AppraisalSign
  deriving DecidableEq, Repr

/-- Refined perspective weights: three base domains + one reputational. -/
structure RefinedPerspectiveWeights where
  base : DomainWeights
  reputational : AppraisalSign
  deriving DecidableEq, Repr

/-- The full domain-refined appraisal weight matrix for an emotion concept.

4 appraisal types × (3 base domains + 1 reputational) = 16 qualitative
dimensions. This is the structure underlying the paper's Fig. 4. -/
structure RefinedAppraisalWeights where
  au  : RefinedPerspectiveWeights
  pe  : RefinedPerspectiveWeights
  cfa : RefinedPerspectiveWeights
  cfo : RefinedPerspectiveWeights
  deriving DecidableEq, Repr

-- Collapse/projection functions are in §9 (after PerspectiveWeights
-- and EmotionProfile are defined in §6).

-- ════════════════════════════════════════════════════════════════
-- § 3. Appraisal Computation from BToM Marginals
-- ════════════════════════════════════════════════════════════════

section AppraisalComputation
open Core

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
-- § 4. Weighted Counterfactual Appraisal
-- ════════════════════════════════════════════════════════════════

section WeightedCounterfactual
open Core

variable {F : Type*} [Ring F]
variable {A P B D S M W : Type*}
  [Fintype P] [Fintype B] [Fintype D] [Fintype S] [Fintype M] [Fintype W]

/-- Weighted counterfactual appraisal: the counterfactual utility difference
weighted by the probability the agent would have chosen the alternative.

    WCF(a, a', w) = P(a' | ω, a₂) · [U(w, a') − U(w, a)]

@cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023} weight CFa₁ by
the probability the player would have chosen differently, given the
inferred preferences and updated beliefs. This connects counterfactual
*appraisal* (utility comparison) to counterfactual *reasoning* (how
likely was the alternative?) — bridging `counterfactualAppraisal` here
with the counterfactual conditional semantics in
`Theories.Semantics.Conditionals.Counterfactual`. -/
def weightedCounterfactualAppraisal (utility : W → A → F)
    (altProb : F) (actualAction altAction : A) (world : W) : F :=
  altProb * (utility world altAction - utility world actualAction)

end WeightedCounterfactual

-- ════════════════════════════════════════════════════════════════
-- § 5. Reputational Appraisal from BToM Desire Marginals
-- ════════════════════════════════════════════════════════════════

section ReputationalAppraisal
open Core

variable {F : Type*} [CommSemiring F]
variable {A P B D S M W : Type*}
  [Fintype P] [Fintype B] [Fintype D] [Fintype S] [Fintype M] [Fintype W]

/-- Reputational appraisal: what an observer would infer about the
agent's preferences from the observed action.

    E[f(d) | a] = Σ_d P(d | a) · f(d)

This is the second-order computation in @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}:
the agent anticipates what observers will infer about their desires
from their action. For the agent, this IS the `desireMarginal` — the
BToM architecture already computes exactly this. The reputational
appraisal is just the desire-marginal expectation of a preference
projection function (e.g., extracting the AIA weight from the desire). -/
def reputationalExpectation (model : BToMModel F A P B D S M W)
    (desireProjection : D → F) (action : A) : F :=
  ∑ d : D, model.desireMarginal action d * desireProjection d

end ReputationalAppraisal

-- ════════════════════════════════════════════════════════════════
-- § 6. Emotion Profiles
-- ════════════════════════════════════════════════════════════════

/-- Appraisal weights for a single appraisal type, split by perspective. -/
structure PerspectiveWeights where
  base : AppraisalSign
  reputational : AppraisalSign
  deriving DecidableEq, Repr

/-- The 4 × 2 qualitative appraisal weight matrix for an emotion concept.

Each of the four appraisal types has a base and reputational weight,
yielding 8 qualitative dimensions. This is our abstraction of the
paper's full 19-dimensional learned β weight matrix (Fig. 4),
collapsing monetary + affiliation + social equity into "base." -/
structure AppraisalWeights where
  au  : PerspectiveWeights  -- Achieved utility
  pe  : PerspectiveWeights  -- Prediction error
  cfa : PerspectiveWeights  -- Counterfactual (agent)
  cfo : PerspectiveWeights  -- Counterfactual (opponent)
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
-- § 7. The 20 Emotion Concepts
-- ════════════════════════════════════════════════════════════════

/-! Qualitative profiles abstracted from the learned β weights in
Houlihan et al.'s Fig. 4. Convention: `.positive` = β > 0 (high appraisal
values increase emotion), `.negative` = β < 0, `.irrelevant` = β ≈ 0.

Each definition specifies: `⟨name, ⟨au, pe, cfa, cfo⟩, orientation⟩`
where each of `au, pe, cfa, cfo` is `⟨base, reputational⟩`.

| Emotion        | AU_b | AU_r | PE_b | PE_r | CFa_b | CFa_r | CFo_b | CFo_r |
|----------------|------|------|------|------|-------|-------|-------|-------|
| joy            |  +   |  ·   |  +   |  ·   |   ·   |   ·   |   ·   |   ·   |
| surprise       |  ·   |  ·   |  ·   |  +   |   ·   |   ·   |   ·   |   ·   |
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

/-- Surprise: loads on |PEπ_{a₂}| — how unexpected the opponent's action was.
This is a distinct appraisal dimension in the paper (the 19th), not a standard
base PE (monetary/AIA/DIA prediction error). We place it in PE.reputational
as the best available slot, since it concerns the social dimension (opponent's
choice) rather than direct material outcomes. -/
def surprise : EmotionProfile :=
  ⟨"surprise", ⟨O, ⟨.irrelevant, .positive⟩, O, O⟩, .retrospective⟩

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

/-- All 20 emotion concepts from @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}. -/
def allEmotions : List EmotionProfile :=
  [joy, surprise, pride, gratitude, relief, amusement,
   disappointment, annoyance, fury, embarrassment,
   regret, guilt, disgust, devastation,
   contempt, respect, envy, sympathy, confusion, excitement]

-- ════════════════════════════════════════════════════════════════
-- § 8. Structural Theorems
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

-- ════════════════════════════════════════════════════════════════
-- § 9. Refined ↔ Qualitative Projections
-- ════════════════════════════════════════════════════════════════

/-- Collapse domain-refined weights back to the qualitative abstraction.

Uses "any positive → positive, any negative → negative, else irrelevant"
policy. This ensures the qualitative profiles remain compatible. -/
def DomainWeights.collapse (d : DomainWeights) : AppraisalSign :=
  if d.monetary == .positive || d.affiliation == .positive || d.socialEquity == .positive
  then .positive
  else if d.monetary == .negative || d.affiliation == .negative || d.socialEquity == .negative
  then .negative
  else .irrelevant

/-- Collapse refined perspective weights to the qualitative abstraction. -/
def RefinedPerspectiveWeights.toPerspectiveWeights
    (r : RefinedPerspectiveWeights) : PerspectiveWeights :=
  ⟨r.base.collapse, r.reputational⟩

/-- Collapse a full refined weight matrix to the qualitative abstraction. -/
def RefinedAppraisalWeights.toAppraisalWeights
    (r : RefinedAppraisalWeights) : AppraisalWeights :=
  ⟨r.au.toPerspectiveWeights, r.pe.toPerspectiveWeights,
   r.cfa.toPerspectiveWeights, r.cfo.toPerspectiveWeights⟩

/-- An emotion concept with domain-refined appraisal weights. -/
structure RefinedEmotionProfile where
  name : String
  weights : RefinedAppraisalWeights
  orientation : TemporalOrientation
  deriving DecidableEq, Repr

/-- Every refined profile projects to a qualitative profile. -/
def RefinedEmotionProfile.toEmotionProfile
    (r : RefinedEmotionProfile) : EmotionProfile :=
  ⟨r.name, r.weights.toAppraisalWeights, r.orientation⟩

-- ════════════════════════════════════════════════════════════════
-- § 10. Prospective Emotions: BToM Bridge to Emotive Doxastics
-- @cite{anand-hacquard-2013} @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}
-- ════════════════════════════════════════════════════════════════

/-!
## Prospective Emotions

The 20 emotions in §7 are all **retrospective**: they are computed from
an *observed outcome* (the agent saw what happened, and we appraise the
result). But emotional attitude verbs like `hope` and `fear` are
**prospective**: the outcome is *uncertain*, and the emotional state
concerns how the uncertainty might be resolved.

@cite{anand-hacquard-2013} formalize exactly this: emotive doxastics
(hope, fear) combine:
1. A **doxastic** component (belief that φ is possible but uncertain)
2. A **preference** component (preference for φ-verifying resolutions)

This maps directly onto the BToM architecture:
- The doxastic component = **belief marginal**: Pr(b | a) determines the
  agent's epistemic state (what they think is possible)
- The preference component = **desire marginal**: Pr(d | a) determines
  what the agent wants
- The uncertainty condition = non-extreme credence: the agent's beliefs
  don't settle the question

### From Retrospective to Prospective

| Retrospective (Houlihan) | Prospective (A&H emotive doxastic) |
|---|---|
| Outcome observed | Outcome uncertain |
| AU = U(actual \| desires) | Preference = desire ordering over DOX partition |
| PE = actual − E[actual \| beliefs] | N/A (no outcome to compare to) |
| CF = U(alternative) − U(actual) | N/A (no actual outcome) |
| Post-outcome: all 4 appraisal types | Pre-outcome: only AU analog available |

The key structural insight: **prospective AU reduces to the preference
ordering over verifiers vs. falsifiers.** When the outcome is uncertain,
the achieved utility is not a single number but a *comparison* between
the utility of φ-worlds and ¬φ-worlds, weighted by the agent's beliefs
about which is actual. This is precisely the preference component of
emotive doxastics.

### Mathematical Foundation

For a BToM model with belief states B and desire states D:

**Prospective achieved utility** (expected utility conditional on φ):

    EU(a, φ) = Σ_d Pr(d | a) · [Σ_w Pr(w | a, φ) · U(w, d)]

**Prospective preference** (φ preferred to ¬φ):

    φ >_DES ¬φ  ⟺  EU(a, φ) > EU(a, ¬φ)

**Uncertainty** (non-extreme credence):

    uncertain(a, φ) ⟺ 0 < Pr(φ | a) < 1
      where Pr(φ | a) = Σ_b Pr(b | a) · ⟦φ⟧_b

The prospective AU is a *conditional* expectation — conditioned on φ or
¬φ being the resolution — rather than a *marginal* utility of the actual
outcome. This is the formal content of "preference over how the uncertainty
gets resolved" from @cite{anand-hacquard-2013} §4.1.
-/

/-- Prospective appraisal: computed over uncertain future outcomes
rather than observed past outcomes.

The BToM components needed are:
- `beliefCredence`: Pr(φ | a) from the belief marginal (how likely the
  agent thinks φ is)
- `conditionalUtility`: EU(a, φ) and EU(a, ¬φ) — expected utility of
  the φ-worlds and ¬φ-worlds, weighted by desires
-/
structure ProspectiveAppraisal (F : Type*) where
  /-- Agent's credence in φ: Pr(φ | a) from BToM belief marginal.
      This is `Σ_b Pr(b | a) · ⟦φ⟧_b` — the probabilistic analog of
      "∃w' ∈ DOX: φ(w')" in the classical framework. -/
  beliefCredence : F
  /-- Expected utility conditional on φ: EU(a, φ).
      The prospective analog of achieved utility. -/
  utilityIfTrue : F
  /-- Expected utility conditional on ¬φ: EU(a, ¬φ). -/
  utilityIfFalse : F

/-- The agent is uncertain about φ: credence is strictly between 0 and 1.
This is the probabilistic analog of the A&H uncertainty condition:
∃w' ∈ DOX: φ(w') ∧ ∃w' ∈ DOX: ¬φ(w'). -/
def ProspectiveAppraisal.isUncertain {F : Type*} [LinearOrder F] [Zero F] [One F]
    (a : ProspectiveAppraisal F) : Bool :=
  decide (a.beliefCredence > 0) && decide (a.beliefCredence < 1)

/-- Hope: uncertain about φ and prefers φ-resolution.
@cite{anand-hacquard-2013}: emotive doxastic with positive valence. -/
def ProspectiveAppraisal.isHope {F : Type*} [LinearOrder F] [Zero F] [One F]
    (a : ProspectiveAppraisal F) : Bool :=
  a.isUncertain && decide (a.utilityIfTrue > a.utilityIfFalse)

/-- Fear: uncertain about φ and disprefers φ-resolution.
@cite{anand-hacquard-2013}: emotive doxastic with negative valence. -/
def ProspectiveAppraisal.isFear {F : Type*} [LinearOrder F] [Zero F] [One F]
    (a : ProspectiveAppraisal F) : Bool :=
  a.isUncertain && decide (a.utilityIfFalse > a.utilityIfTrue)

/-- A prospective emotion profile: extends the retrospective 8-dimensional
profile with the pre-outcome appraisal structure.

Prospective emotions use only the AU analog (preference over resolutions).
PE, CFa, CFo are undefined pre-outcome — there is no actual outcome to
compute prediction error or counterfactuals against. -/
structure ProspectiveEmotionProfile where
  /-- Name of the prospective emotion -/
  name : String
  /-- Valence: does the agent prefer φ (positive) or ¬φ (negative)? -/
  valence : AppraisalSign
  /-- Orientation: always prospective -/
  orientation : TemporalOrientation := .prospective

/-- Prospective hope: positive prospective AU (prefers φ-resolution). -/
def prospectiveHope : ProspectiveEmotionProfile :=
  { name := "hope", valence := .positive }

/-- Prospective fear: negative prospective AU (disprefers φ-resolution). -/
def prospectiveFear : ProspectiveEmotionProfile :=
  { name := "fear", valence := .negative }

/-- Prospective dread: strong negative prospective AU. Structurally
identical to fear but with higher intensity (lower threshold). -/
def prospectiveDread : ProspectiveEmotionProfile :=
  { name := "dread", valence := .negative }

-- ════════════════════════════════════════════════════════════════
-- § 11. BToM Computation of Prospective Appraisals
-- ════════════════════════════════════════════════════════════════

section ProspectiveBToM
open Core

variable {F : Type*} [CommSemiring F] [LinearOrder F]
variable {A P B D S M W : Type*}
  [Fintype P] [Fintype B] [Fintype D] [Fintype S] [Fintype M] [Fintype W]

/-- Compute agent credence in φ from BToM belief marginals.

    Pr(φ | a) = Σ_b Pr(b | a) · ⟦φ⟧_b

where ⟦φ⟧_b is 1 if belief state b is compatible with φ, 0 otherwise.
This is exactly `beliefExpectation` instantiated with the characteristic
function of φ. -/
def agentCredence (model : BToMModel F A P B D S M W)
    (phiInBelief : B → F) (action : A) : F :=
  model.beliefExpectation phiInBelief action

/-- Compute prospective utility: expected utility of φ-worlds under
inferred desires.

    EU(a, φ) = Σ_d Pr(d | a) · U_φ(d)

where U_φ(d) is the utility the agent would get from desire d being
satisfied in a φ-world. This is `achievedUtility` with a φ-conditional
utility function. -/
def prospectiveUtility (model : BToMModel F A P B D S M W)
    (conditionalUtility : D → F) (action : A) : F :=
  ∑ d : D, model.desireMarginal action d * conditionalUtility d

/-- Build a prospective appraisal from a BToM model.

Combines the belief marginal (for credence) and desire marginal (for
conditional utilities) to construct the pre-outcome appraisal that
emotive doxastic attitudes operate over. -/
def buildProspectiveAppraisal (model : BToMModel F A P B D S M W)
    (phiInBelief : B → F)
    (utilIfTrue utilIfFalse : D → F)
    (action : A) : ProspectiveAppraisal F :=
  { beliefCredence := agentCredence model phiInBelief action
  , utilityIfTrue := prospectiveUtility model utilIfTrue action
  , utilityIfFalse := prospectiveUtility model utilIfFalse action }

/-- Agent credence is structurally a BToM belief expectation. -/
theorem agentCredence_eq_beliefExpectation
    (model : BToMModel F A P B D S M W)
    (phiInBelief : B → F) (action : A) :
    agentCredence model phiInBelief action =
    model.beliefExpectation phiInBelief action := rfl

/-- Prospective utility is structurally a desire-marginal weighted sum —
the same computation as retrospective achieved utility, but with a
conditional utility function instead of an actual-outcome utility. -/
theorem prospectiveUtility_eq_desire_weighted_sum
    (model : BToMModel F A P B D S M W)
    (conditionalUtility : D → F) (action : A) :
    prospectiveUtility model conditionalUtility action =
    ∑ d : D, model.desireMarginal action d * conditionalUtility d := rfl

end ProspectiveBToM

end Core
