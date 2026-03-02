/-
# Hawkins, Tsvilodub, Bergey, Goodman & Franke (2025): PRIOR-PQ

Empirical data from "Relevant answers to polar questions"
Phil. Trans. R. Soc. B 380: 20230505.

## Innovation

PRIOR-PQ (Pragmatic Reasoning In Overinformative Responses to Polar Questions)
models how people use theory of mind to produce and interpret relevantly
overinformative answers to yes-no questions.

## Core Insight

The choice of question signals information about the questioner's goals.
A respondent can infer likely decision problems from the question asked.
-/

import Mathlib.Data.Rat.Defs

namespace Phenomena.Questions.Studies.HawkinsEtAl2025


/-!
## Model Components

### Decision Problem
A decision problem D = ⟨W, A, U, π_Q^W⟩ consists of:
- W: world states
- A: actions
- U: W × A → ℝ utility function
- π_Q^W: questioner's prior beliefs over worlds

### Base-level Respondent R0
Selects true AND safe responses uniformly:
  R0(r | w, q) ∝ 1 if r is true in w & safe for q, else 0

### Questioner Q
Chooses question by soft-maximizing expected value after responses:
  Q(q | D) = SM_α(E_w[E_r~R0[V(D|r,q) - w_c·C(r)]])

### Pragmatic Respondent R1
Updates beliefs about decision problem via Bayesian ToM:
  π_R1^D|q(D) ∝ Q(q|D) π_R1^D(D)

Chooses response by soft-maximizing:
  (1-β)·(-KL) + β·V(D|r,q) - w_c·C(r)
-/

/-- Response types in the experiments -/
inductive ResponseType where
  | taciturn       -- Just "yes" or "no"
  | competitor     -- Mention most useful alternative
  | sameCategory   -- Mention similar but less useful option
  | otherCategory  -- Mention unrelated option
  | exhaustive     -- List all available options
  deriving DecidableEq, Repr


/-!
## Case Study 1: Credit Cards

Replication/extension of @cite{clark-1979}, N = 25 participants.

### Conditions
- (3) "Do you accept American Express?" → "Yes, we accept AE and [exhaustive list]"
- (4) "Do you accept American Express?" → "No, we accept [exhaustive list]"
- (5) "Do you accept credit cards?" → "Yes, we accept [exhaustive list]"

### Finding
Probability of exhaustive-list answers: (4) ≥ (5) > (3)
-/

/-- Proportion of exhaustive responses by condition (Case Study 1) -/
def cs1_exhaustive_rate : Fin 3 → ℚ
  | 0 => 12/100   -- Condition (3): specific item available
  | 1 => 75/100   -- Condition (4): specific item unavailable
  | 2 => 66/100   -- Condition (5): general question

/-- Model predictions for exhaustive responses -/
def cs1_model_prediction : Fin 3 → ℚ
  | 0 => 12/100   -- Condition (3)
  | 1 => 75/100   -- Condition (4)
  | 2 => 66/100   -- Condition (5)

/-- Key prediction: unavailable (4) ≥ general (5) > available (3) -/
theorem cs1_ordering :
    cs1_exhaustive_rate 1 ≥ cs1_exhaustive_rate 2 ∧
    cs1_exhaustive_rate 2 > cs1_exhaustive_rate 0 := by
  native_decide


/-!
## Case Study 2: Iced Tea

N = 162 participants, 30 vignettes.

Example: "You are a bartender. The bar serves soda, iced coffee and Chardonnay.
A woman asks: 'Do you have iced tea?'"

### Options
- Competitor: iced coffee (most useful alternative)
- Same-category: soda (similar but less useful)
- Other-category: Chardonnay (unrelated)

### Finding
Response preference ordering: competitor > taciturn ≥ same-category > exhaustive
-/

/-- Human response rates in Case Study 2 -/
structure CS2ResponseRates where
  competitor : ℚ
  taciturn : ℚ
  sameCategory : ℚ
  exhaustive : ℚ
  otherCategory : ℚ
  deriving Repr

/-- Human response rates averaged across 30 vignettes (from MCMC fitting data). -/
def cs2_human_rates : CS2ResponseRates :=
  { competitor := 512/1000
  , taciturn := 206/1000
  , sameCategory := 168/1000
  , exhaustive := 101/1000
  , otherCategory := 14/1000
  }

def cs2_model_rates : CS2ResponseRates :=
  { competitor := 62/100
  , taciturn := 22/100
  , sameCategory := 14/100
  , exhaustive := 1/100
  , otherCategory := 1/100
  }

/-- Model captures the qualitative ordering -/
theorem cs2_competitor_highest :
    cs2_model_rates.competitor > cs2_model_rates.taciturn ∧
    cs2_model_rates.taciturn > cs2_model_rates.sameCategory ∧
    cs2_model_rates.sameCategory > cs2_model_rates.exhaustive := by
  native_decide


/-!
## Case Study 3: Context-Sensitivity

12 paired vignettes testing whether the SAME question with the SAME alternatives
elicits different responses in different contexts.

Example:
- Context 1 (sleepover): "Do you have a blanket?" → sleeping bag preferred
- Context 2 (transportation): "Do you have a blanket?" → bubble wrap preferred

### Finding
Participants mentioned context-congruent competitor significantly more often.
- Context 1 competitor in context 1 vs 2: β = -2.14 [-2.60, -1.71]
- Context 2 competitor in context 2 vs 1: β = 1.34 [0.92, 1.77]
-/

/-- Effect sizes for context-sensitivity (log odds) -/
def cs3_context1_competitor_effect : ℚ := -214/100  -- More in context 1
def cs3_context2_competitor_effect : ℚ := 134/100   -- More in context 2

/-- Credible intervals exclude zero → significant context effects -/
theorem cs3_context_sensitivity :
    cs3_context1_competitor_effect < 0 ∧
    cs3_context2_competitor_effect > 0 := by
  native_decide


/-!
## LLM Performance

Tested: GPT-3.5, GPT-4, Llama-3-70b-Instruct, Mixtral-Instruct

### Finding
LLMs have strong bias toward exhaustive responses in zero-shot condition.
Psychologically-informed chain-of-thought (CoT) prompting improves performance.

### Jensen-Shannon Divergence from Human Data (Case Study 2)
- PRIOR-PQ: 0.120
- Zero-shot Llama: 0.236
- CoT Llama: 0.124
-/

/-- Jensen-Shannon divergence from human data -/
def cs2_jsd_prior_pq : ℚ := 120/1000
def cs2_jsd_llama_zero_shot : ℚ := 236/1000
def cs2_jsd_llama_cot : ℚ := 124/1000

/-- PRIOR-PQ outperforms zero-shot LLM -/
theorem prior_pq_beats_zero_shot :
    cs2_jsd_prior_pq < cs2_jsd_llama_zero_shot := by
  native_decide


/-- Best-fitting model parameters from Table S2 of electronic supplementary material.

    Fit by MCMC (100 burn-in, 5000 samples) to minimize error between
    model and human answer distributions. Parameters vary by case study. -/
structure ModelParams where
  α_respondent : ℚ  -- R₁ softmax temperature
  α_questioner : ℚ  -- Q softmax temperature
  α_policy : ℚ      -- Action policy softmax temperature
  β : ℚ             -- Action-relevance weight (0 = pure epistemic, 1 = pure action)
  w_c : ℚ           -- Response cost weight
  U_fail : Option ℚ -- Utility of failure (receiving nothing); none for CS1
  deriving Repr

/-- CS2 fitted parameters (Table S2). β ≈ 1 means almost pure action-relevance. -/
def cs2Params : ModelParams :=
  { α_respondent := 887/100
  , α_questioner := 373/100
  , α_policy := 4
  , β := 96/100
  , w_c := 96/100
  , U_fail := some (34/10)
  }

/-- CS1 fitted parameters (Table S2). -/
def cs1Params : ModelParams :=
  { α_respondent := 5
  , α_questioner := 3/2
  , α_policy := 5/2
  , β := 9/10
  , w_c := 3/10
  , U_fail := none
  }

/-- CS3 fitted parameters (Table S2). β ≈ 0.29 means mostly epistemic. -/
def cs3Params : ModelParams :=
  { α_respondent := 294/100
  , α_questioner := 589/100
  , α_policy := 854/100
  , β := 29/100
  , w_c := 234/100
  , U_fail := some (-594/100)
  }

/-- Empirically elicited utility values (Table S1, 0-100 slider scale).
    Each row is a decision problem (what the questioner wants);
    each column is an item type. Mean values across N=162 participants. -/
structure CS2Utilities where
  target_for_target : ℚ       -- wanting target → getting target
  competitor_for_target : ℚ   -- wanting target → getting competitor
  sameCat_for_target : ℚ      -- wanting target → getting same-category
  otherCat_for_target : ℚ     -- wanting target → getting other-category
  deriving Repr

/-- Mean utility values from Table S1 (on 0-100 scale). -/
def cs2_utilities : CS2Utilities :=
  { target_for_target := 9618/100     -- 96.18
  , competitor_for_target := 5693/100  -- 56.93
  , sameCat_for_target := 3611/100     -- 36.11
  , otherCat_for_target := 2369/100    -- 23.69
  }


/-- Key qualitative predictions from PRIOR-PQ -/
inductive KeyPrediction where
  | questionSignalsGoal      -- Question choice provides info about goals
  | responseReflectsDP       -- Response tailored to inferred decision problem
  | contextSensitivity       -- Same question, same options → different responses
  | competitorPreferred      -- Useful alternatives mentioned over exhaustive lists
  | tomResolvesCircularity   -- ToM breaks questioner-respondent reasoning loop
  deriving DecidableEq, Repr

def keyPredictions : List KeyPrediction :=
  [ .questionSignalsGoal
  , .responseReflectsDP
  , .contextSensitivity
  , .competitorPreferred
  , .tomResolvesCircularity
  ]

end Phenomena.Questions.Studies.HawkinsEtAl2025
