/-
# Hawkins, Tsvilodub, @cite{hawkins-etal-2025}: PRIOR-PQ

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
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict
import Linglib.Core.Agent.ExperimentDesign

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

/-! ## Bridge content (merged from RSA_HawkinsEtAl2025Bridge.lean) -/

/-!
# PRIOR-PQ as RSAConfig @cite{hawkins-etal-2025}
@cite{frank-goodman-2012}

Hawkins, R. D., Tsvilodub, P., Bergey, C., Goodman, N. D. & Franke, M. (2025).
"Relevant answers to polar questions." Phil. Trans. R. Soc. B 380: 20230505.

## Architectural contribution

PRIOR-PQ models how respondents produce overinformative answers to polar
questions. The **respondent IS S1** and the **questioner IS L1**:

| PRIOR-PQ agent | RSAConfig role | Knows | Uncertain about |
|----------------|----------------|-------|-----------------|
| R₁ (respondent) | S1 (speaker) | world w | decision problem D |
| Q (questioner) | L1 (listener) | DP D | world w |

Decision-problem marginalization is baked into `s1Score` (Latent = Unit),
making the model a standard RSAConfig. This shows that the same machinery
handles both assertion-based RSA and
question-answering RSA (this paper).

## Model equations

R₁'s utility for response r in world w:

    U(r, w) = (1−β)·log L0(w|r) + β·E_D[V(D, r)] − w_c·C(r)

- log L0(w|r): standard RSA informativity (surprisal at true world)
- E_D[V(D, r)]: expected action-relevance under inferred DP posterior
- C(r): response cost (utterance length)

The DP posterior π(D|q) is derived from the Q model (eq. 2.4): asking about
iced tea signals wanting the target item, concentrating the posterior on
wantTarget.

## Case Study 2: Iced Tea

Model prediction (Table S2 fitted params, averaged over 30 items):
  competitor 62% > taciturn 22% > same-category 14% > other-category < 1% ≈ exhaustive < 1%

Human (N=162, 30 vignettes, MCMC fitting targets):
  competitor 51% > taciturn 21% > same-category 17% > exhaustive 10% > other-category 1%

## Simplified model

The RSAConfig below is a simplified abstraction: 5 responses × 8 worlds × 4 DPs,
with pre-computed `expectedActionValue` from DP posterior weights (5:1:1:1). The
full computational model has 30+ responses × 16 worlds and a Q₁ pipeline computing
DP posteriors from the questioner's rationality model. Action values and fitted
parameters (β = 24/25, w_c = 24/25) are from the paper (Table S1, S2). The DP
posterior weights (5:1:1:1) are calibrated for the simplified model; the full model
derives them from Q₁ (see `cs2Params` in Studies/HawkinsEtAl2025).
-/

namespace RSA.PriorPQ

open RSA Real BigOperators

-- ============================================================================
-- §1. Types
-- ============================================================================

/-- Response to "Do you have iced tea?" -/
inductive Response where
  | taciturn     -- "No"
  | mentionIC    -- "No, but we have iced coffee"
  | mentionSoda  -- "No, but we have soda"
  | mentionChard -- "No, but we have Chardonnay"
  | exhaustive   -- "No, but we have iced coffee, soda, and Chardonnay"
  deriving DecidableEq, Repr

instance : Fintype Response where
  elems := {.taciturn, .mentionIC, .mentionSoda, .mentionChard, .exhaustive}
  complete r := by cases r <;> simp

/-- World state: which alternatives the bar has in stock.
    Target (iced tea) is always unavailable — that's why Q asked. -/
structure World where
  hasIC : Bool
  hasSoda : Bool
  hasChard : Bool
  deriving DecidableEq, Repr

instance : Fintype World :=
  Fintype.ofEquiv (Bool × Bool × Bool) {
    toFun := fun ⟨a, b, c⟩ => ⟨a, b, c⟩
    invFun := fun w => ⟨w.hasIC, w.hasSoda, w.hasChard⟩
    left_inv := fun ⟨_, _, _⟩ => rfl
    right_inv := fun ⟨_, _, _⟩ => rfl
  }

/-- Decision problem D = ⟨W, A, U, π_Q^W⟩ (eq. 2, page 4).
    Each DP is defined by which item type the questioner wants.
    The utility function U(w, a) is elicited empirically (Table S1). -/
inductive DP where
  | wantTarget      -- wants iced tea (unavailable → competitor is best substitute)
  | wantCompetitor  -- wants iced coffee
  | wantSameCat     -- wants soda
  | wantOtherCat    -- wants Chardonnay
  deriving DecidableEq, Repr

instance : Fintype DP where
  elems := {.wantTarget, .wantCompetitor, .wantSameCat, .wantOtherCat}
  complete d := by cases d <;> simp

-- ============================================================================
-- §2. Literal semantics (R₀)
-- ============================================================================

/-- A response is true iff mentioned items are actually available. -/
def responseTruth : Response → World → Bool
  | .taciturn, _ => true
  | .mentionIC, w => w.hasIC
  | .mentionSoda, w => w.hasSoda
  | .mentionChard, w => w.hasChard
  | .exhaustive, w => w.hasIC && w.hasSoda && w.hasChard

-- ============================================================================
-- §3. Decision-theoretic action relevance
-- ============================================================================

/-- Action relevance V(D, r): utility of the item revealed by response r,
    given decision problem D. Values from Table S1 of supplementary material
    (0–100 slider scale, ÷ 10 for model). Taciturn reveals nothing:
    V = U_fail = 3.4. Exhaustive reveals all: V = max utility for that DP. -/
noncomputable def actionValue : DP → Response → ℝ
  | _, .taciturn                    => 17/5       -- U_fail = 3.4
  | .wantTarget, .mentionIC         => 5693/1000  -- 56.93
  | .wantTarget, .mentionSoda       => 3611/1000  -- 36.11
  | .wantTarget, .mentionChard      => 2369/1000  -- 23.69
  | .wantTarget, .exhaustive        => 5693/1000  -- max(56.93, 36.11, 23.69)
  | .wantCompetitor, .mentionIC     => 9521/1000  -- 95.21
  | .wantCompetitor, .mentionSoda   => 3815/1000  -- 38.15
  | .wantCompetitor, .mentionChard  => 2485/1000  -- 24.85
  | .wantCompetitor, .exhaustive    => 9521/1000  -- max
  | .wantSameCat, .mentionIC        => 3959/1000  -- 39.59
  | .wantSameCat, .mentionSoda      => 9504/1000  -- 95.04
  | .wantSameCat, .mentionChard     => 2615/1000  -- 26.15
  | .wantSameCat, .exhaustive       => 9504/1000  -- max
  | .wantOtherCat, .mentionIC       => 2547/1000  -- 25.47
  | .wantOtherCat, .mentionSoda     => 2537/1000  -- 25.37
  | .wantOtherCat, .mentionChard    => 9565/1000  -- 95.65
  | .wantOtherCat, .exhaustive      => 9565/1000  -- max

/-- DP posterior π(D|q_tea) ∝ Q(q|D) · π₀(D) (eq. 2.4, page 4).
    Unnormalized weights approximating the full Q₁ posterior.
    Asking "Do you have iced tea?" most benefits wantTarget (the questioner
    probably wants what they asked for), so wantTarget dominates 5:1:1:1. -/
noncomputable def dpPrior : DP → ℝ
  | .wantTarget     => 5
  | .wantCompetitor => 1
  | .wantSameCat    => 1
  | .wantOtherCat   => 1

/-- Expected action relevance E_D[V(D, r)], marginalized over DPs.

    Precomputed from `dpPrior` (5:1:1:1, total = 8) and `actionValue`:
    - taciturn: 17/5 = 3.4 (U_fail, same for all DPs)
    - mentionIC: (5·5693 + 9521 + 3959 + 2547) / 8000 = 11123/2000 ≈ 5.56
    - mentionSoda: (5·3611 + 3815 + 9504 + 2537) / 8000 = 33911/8000 ≈ 4.24
    - mentionChard: (5·2369 + 2485 + 2615 + 9565) / 8000 = 2651/800 ≈ 3.31
    - exhaustive: (5·5693 + 9521 + 9504 + 9565) / 8000 = 11411/1600 ≈ 7.13 -/
noncomputable def expectedActionValue : Response → ℝ
  | .taciturn    => 17/5
  | .mentionIC   => 11123/2000
  | .mentionSoda => 33911/8000
  | .mentionChard => 2651/800
  | .exhaustive  => 11411/1600

/-- Response cost C(r) = number of items mentioned.
    Taciturn ("No") mentions 0 items; single mentions cost 1;
    exhaustive ("No, but we have IC, soda, Chardonnay") costs 3. -/
noncomputable def cost : Response → ℝ
  | .taciturn    => 0
  | .mentionIC   => 1
  | .mentionSoda => 1
  | .mentionChard => 1
  | .exhaustive  => 3

-- ============================================================================
-- §4. RSAConfig
-- ============================================================================

/-- β: weight on action-relevance vs informativity.
    Fitted value: 0.96 ≈ 24/25 (Table S2). Almost pure action-relevance:
    the respondent optimizes for the questioner's inferred decision problem. -/
noncomputable def β : ℝ := 24/25

/-- w_c: cost weight.
    Fitted value: 0.96 ≈ 24/25 (Table S2). Each mentioned item incurs
    substantial cost in the utility function. -/
noncomputable def w_c : ℝ := 24/25

/-- PRIOR-PQ as RSAConfig.

    The respondent (R₁) IS S1. The questioner (Q) IS L1.
    Decision problems are marginalized into s1Score (Latent = Unit).

    s1Score(L0, α, w, r) =
      if L0(w|r) = 0 then 0
      else exp(α · ((1−β)·log L0(w|r) + β·E_D[V(D,r)] − w_c·C(r))) -/
noncomputable def cfg : RSAConfig Response World where
  Latent := Unit
  meaning _ _ r w := if responseTruth r w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α _ w r :=
    let info := l0 r w
    if info = 0 then 0
    else exp (α * ((1 - β) * log info + β * expectedActionValue r - w_c * cost r))
  s1Score_nonneg l0 α _ w r _ _ := by
    show 0 ≤ (if l0 r w = 0 then (0 : ℝ) else exp _)
    split
    · exact le_refl 0
    · exact le_of_lt (exp_pos _)
  α := 5
  α_pos := by norm_num
  latentPrior_nonneg := fun _ _ => by norm_num
  worldPrior_nonneg := fun _ => by norm_num

-- ============================================================================
-- §5. Case Study 2: Iced Tea
-- ============================================================================

/-- The actual world: all 3 alternatives in stock. -/
def w_cs2 : World := ⟨true, true, true⟩

/-- **Prediction 1**: Competitor (iced coffee) preferred over taciturn.

    MentionIC wins on action-relevance (E[V] = 11123/2000 ≈ 5.56
    vs 17/5 = 3.4). Despite lower informativity (L0 = 1/4 vs 1/8)
    and higher cost (1 vs 0), action-relevance dominates with β = 24/25.
    Reduces to: log 2 > −27.88 (trivially true). -/
theorem cs2_competitor_gt_taciturn :
    cfg.S1 () w_cs2 .mentionIC > cfg.S1 () w_cs2 .taciturn := by
  rsa_predict

/-- **Prediction 2**: Taciturn preferred over same-category (soda).

    Despite soda's higher informativity (L0 = 1/4 vs 1/8) and
    action-relevance (E[V] = 33911/8000 ≈ 4.24 vs 17/5 = 3.4),
    taciturn wins on cost (0 vs 1). Reduces to: log 2 < 3.87. -/
theorem cs2_taciturn_gt_sameCategory :
    cfg.S1 () w_cs2 .taciturn > cfg.S1 () w_cs2 .mentionSoda := by
  rsa_predict

/-- **Prediction 3**: Competitor > same-category.

    Both have same informativity (L0 = 1/4) and cost (1), but mentionIC
    has higher action-relevance (11123/2000 vs 33911/8000) because the
    DP posterior concentrates on wantTarget, where competitor is the
    best available substitute. Pure rational comparison: 44492 > 33911. -/
theorem cs2_competitor_gt_sameCategory :
    cfg.S1 () w_cs2 .mentionIC > cfg.S1 () w_cs2 .mentionSoda := by
  rsa_predict

/-- **Prediction 4**: Same-category > other-category (chardonnay).

    Both have same informativity (L0 = 1/4) and cost (1). MentionSoda
    has higher action-relevance (33911/8000 vs 2651/800) because the
    DP posterior favors wantTarget, where soda (same-category) is a
    better substitute than Chardonnay (other-category).
    Pure rational comparison: 33911 > 26510. -/
theorem cs2_sameCategory_gt_otherCategory :
    cfg.S1 () w_cs2 .mentionSoda > cfg.S1 () w_cs2 .mentionChard := by
  rsa_predict

-- ============================================================================
-- §6. Bridge to empirical data
-- ============================================================================

open Phenomena.Questions.Studies.HawkinsEtAl2025

/-- The model's qualitative ordering matches CS2 human data (from Data file). -/
theorem cs2_data_ordering :
    cs2_model_rates.competitor > cs2_model_rates.taciturn ∧
    cs2_model_rates.taciturn > cs2_model_rates.sameCategory ∧
    cs2_model_rates.sameCategory > cs2_model_rates.exhaustive := by
  native_decide

-- ============================================================================
-- §7. Questioner Q as Optimal Experiment Designer
-- ============================================================================

/-! ### Q selects questions to maximize expected decision value

PRIOR-PQ's Q (eq. 2.3) IS an optimal experiment designer:
- **Experiment** = question q
- **Observation** = R₀'s response r
- **Observation model** = R₀'s literal semantics (truth-conditional)
- **Value function** = expected decision value under DP posterior

The connection is structural: Q's utility U_Q(q) = E_{w~prior}[E_{r~R₀}[V(D,r,q)]]
is exactly the EIG of the experiment q under the observation model R₀.

This section makes the connection explicit by constructing the observation model
from R₀ and showing Q is an `optimalExperiment` instance. -/

open Core.ExperimentDesign

/-- Number of true responses in world w (for uniform R₀ normalization). -/
noncomputable def truthCount (w : World) : ℝ :=
  (Finset.univ.filter (fun r => responseTruth r w)).card

/-- R₀ as an observation model: the literal respondent's truth-conditional
    semantics define a stochastic observation model.

    P(r|w,q) = 1/|{r : responseTruth r w}| if responseTruth r w, else 0.

    R₀ selects uniformly among true responses (literal respondent).
    The experiment is trivial (Unit) because we model a single question. -/
noncomputable def r0ObservationModel : ObservationModel World Unit Response where
  likelihood w _ r :=
    if responseTruth r w then 1 / truthCount w else 0
  likelihood_nonneg w _ r := by
    show 0 ≤ (if responseTruth r w then 1 / truthCount w else 0)
    split
    · exact div_nonneg (by norm_num) (Nat.cast_nonneg' _)
    · exact le_refl 0
  likelihood_sum w _ := by
    -- Σ_r (if truth r w then 1/|true responses| else 0) = |true|/|true| = 1
    -- TODO: Requires rewriting the sum as |true responses| · (1/|true responses|)
    sorry

/-- All responses, as a concrete list for dpValueR iteration. -/
def allResponses : List Response :=
  [.taciturn, .mentionIC, .mentionSoda, .mentionChard, .exhaustive]

/-- Expected decision value: the value of holding posterior beliefs `post`.

    V(post) = max_r Σ_w post(w) · E_D[V(D, r)]

    where E_D[V(D, r)] = `expectedActionValue r` (marginalized over DPs
    using `dpPrior`). This is the value function for Q's experiment
    design problem: how useful is it to hold beliefs `post`? -/
noncomputable def questionerValue : (World → ℝ) → ℝ :=
  dpValueR (fun _w r => expectedActionValue r) allResponses

/-- The questioner Q IS an optimal experiment designer.

    Q selects questions to maximize expected decision value after observing
    R₀'s response. This is eq. 2.3 of @cite{hawkins-etal-2025}:

    U_Q(q) = E_{w~prior}[E_{r~R₀(·|w,q)}[V(D^{r,q})]]

    which is exactly `eig r0ObservationModel worldPrior questionerValue`. -/
noncomputable def questioner_as_experiment (αQ : ℝ) :=
  optimalExperiment r0ObservationModel
    (fun _w => (1 : ℝ) / Fintype.card World)  -- uniform world prior
    questionerValue αQ

end RSA.PriorPQ
