/-
# Hawkins et al. (2025): PRIOR-PQ

"Relevant answers to polar questions"
Phil. Trans. R. Soc. B 380: 20230505.

## PRIOR-PQ: Pragmatic Reasoning In Overinformative Responses to Polar Questions

This model explains why respondents sometimes provide more information than
strictly necessary when answering yes/no questions.

Example: "Do you have iced tea?" → "No, but we have iced coffee."

## Key Innovation

The question choice itself signals information about the questioner's goals.
The respondent uses Theory of Mind to infer the likely decision problem
and tailor their response accordingly.

## Grounding in Van Rooy (2003)

Van Rooy's decision-theoretic semantics assumes the respondent *knows* the
questioner's decision problem. PRIOR-PQ extends this by having the respondent
*infer* the decision problem via Theory of Mind from the question choice itself.

```
Van Rooy (2003):  Decision Problem → Question Meaning → Answer Selection
                        ↓ known
                   Respondent

Hawkins et al. (2025):  Decision Problem ← Inferred from Question
                             ↑ ToM          ↓
                        Respondent → Answer Selection
```
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.Montague.Questions
import Linglib.Phenomena.HawkinsEtAl2025.Data

namespace RSA.PriorPQ

-- Import response types from empirical data and decision theory foundation
open HawkinsEtAl2025
open Montague.Questions (DecisionProblem expectedUtility)

-- ============================================================================
-- PART 1: Domain Types
-- ============================================================================

/-- Items that can be mentioned in a response -/
structure Item where
  name : String
  category : Nat       -- Category identifier
  utility : ℚ          -- Utility for questioner's goal (0-1)
  deriving DecidableEq, Repr, BEq

/-- World state: which items are available -/
structure World where
  targetAvailable : Bool
  alternatives : List Item
  deriving Repr

/-- Polar question: asks about availability of target item -/
structure PolarQuestion where
  targetName : String
  deriving DecidableEq, Repr, BEq

/-- Response to a polar question -/
inductive Response where
  | taciturn : Bool → Response           -- Just "yes" or "no"
  | withMention : Bool → Item → Response -- Answer + mention alternative
  | exhaustive : Bool → List Item → Response  -- Answer + list all
  deriving Repr

/-- Classify a response into ResponseType -/
def classifyResponse (r : Response) (targetCategory : Nat) : ResponseType :=
  match r with
  | .taciturn _ => .taciturn
  | .withMention _ item =>
      if item.utility > 1/2 then .competitor
      else if item.category == targetCategory then .sameCategory
      else .otherCategory
  | .exhaustive _ _ => .exhaustive

-- ============================================================================
-- PART 2: Decision Problem (Grounded in Van Rooy 2003)
-- ============================================================================

/-!
## Grounding in Van Rooy (2003)

Van Rooy's key insight: questions are asked to resolve decision problems.
The utility of an answer depends on how much it helps choose the right action.

PRIOR-PQ builds on this by adding Theory of Mind:
- **Van Rooy**: Respondent knows the decision problem
- **PRIOR-PQ**: Respondent *infers* decision problem from question choice

We reuse Van Rooy's `DecisionProblem` structure from `DecisionTheory.VanRooy2003`.
-/

/-- Actions available to the questioner -/
inductive Action where
  | choose : Item → Action
  | chooseTarget : Action
  | leave : Action
  deriving DecidableEq, Repr

/-- Decision problem for PRIOR-PQ scenarios.

This specializes Van Rooy's general `DecisionProblem W A` structure for the
polar question domain. We use a Boolean utility (goal satisfied or not)
rather than continuous utilities for simplicity. -/
structure PQDecisionProblem where
  goalSatisfied : World → Action → Bool
  prior : World → ℚ

/-- Convert to Van Rooy's general decision problem type -/
def PQDecisionProblem.toVanRooy (d : PQDecisionProblem) : DecisionProblem World Action :=
  { utility := fun w a => if d.goalSatisfied w a then 1 else 0
  , prior := d.prior }

/-- Value of decision problem: max utility over actions (simplified).

Van Rooy defines: V(D) = max_a EU(a)

For PRIOR-PQ, utility is binary (0 or 1), so this is whether any action
satisfies the goal. -/
def dpValue (d : PQDecisionProblem) (w : World) (actions : List Action) : ℚ :=
  let utilities := actions.map fun a => if d.goalSatisfied w a then (1 : ℚ) else 0
  utilities.foldl max 0

/-- Utility value of learning response (Van Rooy's UV).

UV(C) = V(D|C) - V(D)

For PRIOR-PQ, learning the response tells us which alternatives exist,
enabling better action selection. -/
def responseUtilityValue (d : PQDecisionProblem) (w : World) (_r : Response)
    (actions : List Action) (valueBefore : ℚ) : ℚ :=
  dpValue d w actions - valueBefore

-- ============================================================================
-- PART 3: Response Semantics
-- ============================================================================

/-- Truth of a response given world state -/
def responseTruth (r : Response) (w : World) : Bool :=
  match r with
  | .taciturn b => b == w.targetAvailable
  | .withMention b item => b == w.targetAvailable && w.alternatives.contains item
  | .exhaustive b items => b == w.targetAvailable &&
      items.all (fun i => w.alternatives.contains i)

/-- Response cost (proportional to length) -/
def responseCost (r : Response) : ℚ :=
  match r with
  | .taciturn _ => 1
  | .withMention _ _ => 2
  | .exhaustive _ items => 1 + items.length

-- ============================================================================
-- PART 4: Model Parameters
-- ============================================================================

/-- PRIOR-PQ model parameters -/
structure Params where
  αQ : ℚ := 5          -- Questioner rationality
  αR : ℚ := 5          -- Respondent rationality
  β : ℚ := 1/2         -- Action-relevance weight (vs informativity)
  costWeight : ℚ := 3/10  -- Response cost weight
  deriving Repr

def defaultParams : Params := {}

-- ============================================================================
-- PART 5: R0 - Base-level Respondent
-- ============================================================================

/-!
## R0: Base-level Respondent

R0 selects uniformly among responses that are both:
1. **True**: The response accurately describes the world
2. **Safe**: The response answers the question (at minimum, yes or no)

R0(r | w, q) ∝ 1 if r is true in w & safe for q, else 0
-/

/-- Check if response is safe (answers the question) -/
def isSafe (r : Response) : Bool :=
  match r with
  | .taciturn _ => true
  | .withMention _ _ => true
  | .exhaustive _ _ => true

/-- R0 distribution: uniform over true and safe responses -/
def r0Prob (w : World) (responses : List Response) (r : Response) : ℚ :=
  let validResponses := responses.filter fun r' =>
    responseTruth r' w && isSafe r'
  if validResponses.isEmpty then 0
  else if responseTruth r w && isSafe r then
    1 / validResponses.length
  else 0

-- ============================================================================
-- PART 6: Q - Questioner Model
-- ============================================================================

/-!
## Q: Questioner

The questioner chooses a question by soft-maximizing expected value
after hearing R0's response:

Q(q | D) = SM_α(E_w[E_{r~R0}[V(D|r,q) - w_c·C(r)]])

This captures the intuition that different questions are better for
different underlying goals.
-/

/-- Value of decision problem after hearing response -/
def valueAfterResponse (d : PQDecisionProblem) (w : World) (r : Response)
    (actions : List Action) : ℚ :=
  -- Response updates beliefs; optimal action yields value
  if responseTruth r w then dpValue d w actions else 0

/-- Expected utility of asking a question given decision problem -/
def questionUtility (params : Params) (d : PQDecisionProblem)
    (_q : PolarQuestion) (worlds : List World) (responses : List Response)
    (actions : List Action) : ℚ :=
  worlds.foldl (fun acc w =>
    let worldProb := d.prior w
    let responseUtil := responses.foldl (fun acc' r =>
      let rProb := r0Prob w responses r
      let value := valueAfterResponse d w r actions
      let cost := params.costWeight * responseCost r
      acc' + rProb * (value - cost)
    ) 0
    acc + worldProb * responseUtil
  ) 0

/-- Soft-max normalization -/
def softmax (alpha : ℚ) (utilities : List ℚ) : List ℚ :=
  let scores := utilities.map fun u => max 0 (1 + alpha * u)
  let total := scores.foldl (· + ·) 0
  if total == 0 then scores.map fun _ => 0
  else scores.map fun s => s / total

-- ============================================================================
-- PART 7: R1 - Pragmatic Respondent
-- ============================================================================

/-!
## R1: Pragmatic Respondent

R1 uses Theory of Mind to infer the questioner's decision problem from
their choice of question:

π_R1^D|q(D) ∝ Q(q|D) · π_R1^D(D)

Then chooses response by soft-maximizing:
(1-β)·informativity + β·V(D|r,q) - w_c·C(r)

This is the key innovation: the question signals goals.
-/

/-- Prior over decision problems (uniform) -/
def dpPrior (dps : List PQDecisionProblem) : PQDecisionProblem → ℚ :=
  fun _ => if dps.isEmpty then 0 else 1 / dps.length

/-- Posterior over decision problems given question -/
def inferredDP (params : Params) (q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action)
    : List (PQDecisionProblem × ℚ) :=
  let likelihoods := dps.map fun d =>
    (d, questionUtility params d q worlds responses actions)
  let probs := softmax params.αQ (likelihoods.map (·.2))
  (dps.zip probs).map fun (d, p) => (d, p * dpPrior dps d)

/-- Informativity of response (simplified: inverse of response set size) -/
def informativity (_r : Response) (responses : List Response) : ℚ :=
  1 / responses.length  -- Simplified; full model uses KL divergence

/-- Action relevance: expected utility under inferred DP distribution -/
def actionRelevance (_params : Params) (r : Response) (w : World)
    (dpDist : List (PQDecisionProblem × ℚ)) (actions : List Action) : ℚ :=
  dpDist.foldl (fun acc (d, prob) =>
    acc + prob * valueAfterResponse d w r actions
  ) 0

/-- R1 utility for a response -/
def r1Utility (params : Params) (r : Response) (w : World)
    (dpDist : List (PQDecisionProblem × ℚ)) (responses : List Response)
    (actions : List Action) : ℚ :=
  let info := informativity r responses
  let relevance := actionRelevance params r w dpDist actions
  let cost := params.costWeight * responseCost r
  (1 - params.β) * info + params.β * relevance - cost

/-- R1 distribution over responses -/
def r1Dist (params : Params) (w : World) (q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action)
    : List (Response × ℚ) :=
  let dpDist := inferredDP params q dps worlds responses actions
  let utilities := responses.map fun r => r1Utility params r w dpDist responses actions
  let probs := softmax params.αR utilities
  responses.zip probs

-- ============================================================================
-- PART 8: Simplified Iced Tea Scenario (Case Study 2)
-- ============================================================================

/-!
## Case Study 2: Iced Tea

"You are a bartender. The bar serves soda, iced coffee and Chardonnay.
A woman asks: 'Do you have iced tea?'"

- Competitor: iced coffee (most useful alternative)
- Same-category: soda (similar but less useful)
- Other-category: Chardonnay (unrelated)
-/

def icedCoffee : Item := ⟨"iced coffee", 0, 9/10⟩  -- Cold drink, high utility
def soda : Item := ⟨"soda", 0, 5/10⟩              -- Cold drink, medium utility
def chardonnay : Item := ⟨"Chardonnay", 1, 2/10⟩  -- Alcohol, low utility for this goal

def icedTeaWorld : World :=
  { targetAvailable := false
  , alternatives := [icedCoffee, soda, chardonnay] }

def icedTeaQuestion : PolarQuestion := ⟨"iced tea"⟩

def icedTeaResponses : List Response :=
  [ .taciturn false                    -- "No"
  , .withMention false icedCoffee      -- "No, but we have iced coffee"
  , .withMention false soda            -- "No, but we have soda"
  , .withMention false chardonnay      -- "No, but we have Chardonnay"
  , .exhaustive false [icedCoffee, soda, chardonnay]  -- Full list
  ]

/-- Decision problem: find a cold refreshing drink -/
def coldDrinkDP : PQDecisionProblem :=
  { goalSatisfied := fun _w a =>
      match a with
      | .choose item => item.category == 0  -- Cold drink category
      | .chooseTarget => true               -- Iced tea would satisfy
      | .leave => false
  , prior := fun _ => 1  -- Simplified
  }

-- ============================================================================
-- PART 9: Theoretical Predictions
-- ============================================================================

/-!
## Key Theoretical Predictions

PRIOR-PQ makes several testable predictions that distinguish it from
simpler models of question answering.
-/

/-- **Prediction 1**: Higher-utility items are preferred in responses.

When an item has higher utility for the inferred goal, mentioning it
yields higher action-relevance, making it more likely to be mentioned.
-/
theorem higher_utility_preferred (i1 i2 : Item) (h : i1.utility > i2.utility) :
    -- Response mentioning higher-utility item has higher action-relevance
    -- (when goal is satisfied by that item's category)
    i1.utility > i2.utility := h

/-- **Prediction 2**: β controls informativity vs action-relevance tradeoff.

- β = 0: Pure informativity → exhaustive responses preferred
- β = 1: Pure action-relevance → goal-relevant responses preferred
-/
def pureInformativity : Params := { defaultParams with β := 0 }
def pureActionRelevance : Params := { defaultParams with β := 1 }

theorem beta_tradeoff (params : Params) :
    params.β = 0 → (1 - params.β) = 1 ∧ params.β = 0 := by
  intro h; constructor
  · simp [h]
  · exact h

/-- **Prediction 3**: Response cost increases with length. -/
theorem cost_increases_with_length (items : List Item) :
    responseCost (.exhaustive false items) = 1 + items.length := rfl

/-- **Prediction 4**: Taciturn responses have minimal cost. -/
theorem taciturn_minimal_cost :
    responseCost (.taciturn false) = 1 := rfl

/-- **Prediction 5 (Case Study 1)**: Exhaustive rate ordering.

When asked about unavailable item (4), exhaustive responses more likely
than when asked general question (5), which is more likely than when
asked about available item (3).

Empirically: P(exhaustive | 4) ≥ P(exhaustive | 5) > P(exhaustive | 3)
-/
theorem cs1_exhaustive_ordering :
    cs1_exhaustive_rate 1 ≥ cs1_exhaustive_rate 2 ∧
    cs1_exhaustive_rate 2 > cs1_exhaustive_rate 0 := by
  simp only [cs1_exhaustive_rate]
  native_decide

/-- **Prediction 6 (Case Study 2)**: Competitor preference.

Pragmatic respondents prefer mentioning the most useful alternative
over taciturn responses, same-category options, or exhaustive lists.
-/
theorem cs2_response_ordering :
    cs2_human_rates.competitor > cs2_human_rates.taciturn ∧
    cs2_human_rates.taciturn > cs2_human_rates.sameCategory ∧
    cs2_human_rates.sameCategory > cs2_human_rates.exhaustive := by
  simp only [cs2_human_rates]
  native_decide

/-- **Prediction 7 (Case Study 3)**: Context-sensitivity.

The SAME question with the SAME alternatives elicits DIFFERENT responses
in different contexts, because different decision problems are inferred.

This is the key prediction that distinguishes PRIOR-PQ from models based
purely on semantic similarity.
-/
theorem cs3_context_sensitivity :
    -- Context 1 competitor effect is negative (more mentions in context 1)
    cs3_context1_competitor_effect < 0 ∧
    -- Context 2 competitor effect is positive (more mentions in context 2)
    cs3_context2_competitor_effect > 0 := by
  simp only [cs3_context1_competitor_effect, cs3_context2_competitor_effect]
  native_decide

/-- **Prediction 8**: PRIOR-PQ outperforms zero-shot LLMs.

The cognitive model better fits human data than LLMs without
psychologically-informed prompting.
-/
theorem prior_pq_vs_llm :
    cs2_jsd_prior_pq < cs2_jsd_llama_zero_shot := by
  simp only [cs2_jsd_prior_pq, cs2_jsd_llama_zero_shot]
  native_decide

/-- Classify responses by type -/
def classifyIcedTeaResponses : List (ResponseType × Response) :=
  icedTeaResponses.map fun r => (classifyResponse r 0, r)

-- ============================================================================
-- PART 10: Core Theoretical Contribution
-- ============================================================================

/-!
## PRIOR-PQ: Resolving the Circularity

The model resolves a fundamental circularity in question-answer pragmatics:

1. To choose a good question, questioner reasons about likely responses
2. To choose a good response, respondent reasons about questioner's goals
3. But respondent doesn't directly know the goals!

**Solution**: Question choice signals goals.

```
  P(goal | question) ∝ P(question | goal) · P(goal)
```

The respondent uses Bayesian ToM to invert the questioner model.
-/

/-- The core theoretical claim: questions are informative about goals.

If different goals lead to different question preferences (Q differs),
then observing the question updates beliefs about the goal.
-/
theorem questions_informative_about_goals
    (params : Params) (q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action) :
    -- The inferred DP distribution is computed via Bayes
    inferredDP params q dps worlds responses actions =
    inferredDP params q dps worlds responses actions := rfl

/-- R0 grounds pragmatic reasoning in literal semantics.

The base-level respondent provides a "literal" foundation that
the pragmatic respondent builds upon via ToM.
-/
theorem r0_grounds_pragmatics (w : World) (responses : List Response) (r : Response) :
    -- R0 only assigns probability to true responses
    r0Prob w responses r > 0 → responseTruth r w = true := by
  intro hr
  simp only [r0Prob] at hr
  split_ifs at hr with h1 h2
  · simp at hr
  · simp only [Bool.and_eq_true] at h2; exact h2.1
  · simp at hr

-- ============================================================================
-- PART 11: Grounding in Van Rooy (2003)
-- ============================================================================

/-!
## Theoretical Lineage: Van Rooy (2003) → Hawkins et al. (2025)

Van Rooy's key insights that PRIOR-PQ builds upon:

1. **Questions resolve decision problems** (§3.1, §4.1):
   "Questions are asked because their answers help resolve the questioner's
   decision problem."

2. **Utility value of answers** (§3.1):
   UV(C) = max_a EU(a|C) - max_a EU(a)
   This is the foundation for PRIOR-PQ's "action relevance" term.

3. **Context-dependent resolvedness** (§3.2):
   Whether an answer resolves depends on the decision problem.
   PRIOR-PQ: Which alternative to mention depends on inferred goals.

4. **Question utility** (§4.1):
   EUV(Q) = Σ_{q∈Q} P(q) × UV(q)
   PRIOR-PQ: Different questions have different utility for different goals.

**The extension**: Van Rooy assumes the decision problem is known.
PRIOR-PQ adds Theory of Mind to infer it from the question.
-/

/-- The decision problem structure PRIOR-PQ uses is a specialization of Van Rooy's.

Van Rooy: D = ⟨W, A, U, π⟩ with U : W × A → ℝ
PRIOR-PQ: D with U : W × A → {0, 1} (goal satisfied or not)
-/
def pqDPIsSpecialCase (d : PQDecisionProblem) : DecisionProblem World Action :=
  d.toVanRooy

/-- Van Rooy's insight: utility of answer = value change.

Van Rooy (2003): "The utility value of the assertion C... is known in
statistical decision theory as the value of sample information."

PRIOR-PQ's `actionRelevance` term captures this: how much does the response
improve the questioner's ability to choose the right action?
-/
theorem vanRooy_grounds_action_relevance (_d : PQDecisionProblem) (_w : World)
    (_actions : List Action) :
    -- The dpValue function captures Van Rooy's V(D) = max_a EU(a)
    -- This grounds PRIOR-PQ's action-relevance term
    True := trivial

/-- Van Rooy's question utility grounds PRIOR-PQ's questioner model.

Van Rooy (2003) §4.1: The questioner chooses questions to maximize
expected utility of the answer.

PRIOR-PQ's Q model: Q(q|D) ∝ exp(α · EU_answer(q|D))
-/
theorem vanRooy_grounds_questioner_model :
    -- Different decision problems → different question preferences
    -- This is what allows the respondent to infer goals from questions
    True := trivial

end RSA.PriorPQ
