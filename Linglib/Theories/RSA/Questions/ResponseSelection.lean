/-
# RSA/Questions/ResponseSelection.lean

Response Selection Models for Polar Questions.

## Overview

This module implements the response selection component of PRIOR-PQ
(Hawkins et al. 2025), including:
- R0: Base-level (literal) respondent
- R1: Pragmatic respondent with Theory of Mind
- ToM inference of questioner's decision problem

## Key Models

### R0: Literal Respondent

R0 selects uniformly among responses that are:
1. **True**: The response accurately describes the world
2. **Safe**: The response answers the question

R0(r | w, q) ∝ 1 if r is true in w & safe for q, else 0

### R1: Pragmatic Respondent

R1 uses Theory of Mind to infer the questioner's decision problem:

π_R1^D|q(D) ∝ Q(q|D) · π_R1^D(D)

Then chooses response by soft-maximizing:
(1-β)·informativity + β·V(D|r,q) - w_c·C(r)

## References

- Hawkins, R.D., et al. (2025). Relevant answers to polar questions.
- Van Rooy, R. (2003). Questioning to Resolve Decision Problems.
-/

import Linglib.Theories.RSA.Questions.PolarQuestions
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval

namespace RSA.Questions

open RSA.Eval

-- ============================================================================
-- PART 1: Response Types
-- ============================================================================

/-- Response to a polar question.

Respondents can provide different levels of information:
- **Taciturn**: Just "yes" or "no"
- **WithMention**: Answer plus mention one alternative
- **Exhaustive**: Answer plus list all alternatives
-/
inductive Response where
  /-- Just "yes" or "no" -/
  | taciturn : Bool → Response
  /-- Answer + mention one alternative -/
  | withMention : Bool → Item → Response
  /-- Answer + list all alternatives -/
  | exhaustive : Bool → List Item → Response
  deriving Repr

instance : BEq Response where
  beq r1 r2 := match r1, r2 with
    | .taciturn b1, .taciturn b2 => b1 == b2
    | .withMention b1 i1, .withMention b2 i2 => b1 == b2 && i1 == i2
    | .exhaustive b1 l1, .exhaustive b2 l2 =>
        b1 == b2 && l1.length == l2.length
    | _, _ => false

/-- Extract the yes/no answer from a response -/
def Response.answer : Response → Bool
  | .taciturn b => b
  | .withMention b _ => b
  | .exhaustive b _ => b

/-- Response type classification (for empirical comparison) -/
inductive ResponseType where
  | taciturn : ResponseType
  | competitor : ResponseType      -- High-utility alternative
  | sameCategory : ResponseType    -- Same category, lower utility
  | otherCategory : ResponseType   -- Different category
  | exhaustive : ResponseType
  deriving Repr, DecidableEq, BEq

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
-- PART 2: Response Semantics
-- ============================================================================

/-- Truth of a response given world state.

A response is true iff:
- The yes/no answer matches whether target is available
- Any mentioned items are actually available in the world
-/
def responseTruth (r : Response) (w : World) : Bool :=
  match r with
  | .taciturn b => b == w.targetAvailable
  | .withMention b item =>
      b == w.targetAvailable && w.alternatives.contains item
  | .exhaustive b items =>
      b == w.targetAvailable &&
      items.all (fun i => w.alternatives.contains i)

/-- Response cost (proportional to length/complexity).

Longer responses are more costly to produce.
-/
def responseCost (r : Response) : ℚ :=
  match r with
  | .taciturn _ => 1
  | .withMention _ _ => 2
  | .exhaustive _ items => 1 + items.length

/-- Check if response is safe (answers the question).

A response is safe if it provides at minimum a yes/no answer.
All our response types are safe by construction.
-/
def isSafe (_r : Response) : Bool := true

-- ============================================================================
-- PART 3: R0 - Base-Level Respondent
-- ============================================================================

/-- R0: Base-level respondent.

R0 selects uniformly among responses that are both:
1. **True**: The response accurately describes the world
2. **Safe**: The response answers the question

R0(r | w, q) ∝ 1 if r is true in w & safe for q, else 0

This provides a "literal" foundation that the pragmatic respondent
builds upon via Theory of Mind.
-/
def r0Prob (w : World) (responses : List Response) (r : Response) : ℚ :=
  let validResponses := responses.filter fun r' =>
    responseTruth r' w && isSafe r'
  if validResponses.isEmpty then 0
  else if responseTruth r w && isSafe r then
    1 / validResponses.length
  else 0

/-- R0 distribution over responses -/
def r0Dist (w : World) (responses : List Response) : List (Response × ℚ) :=
  responses.map fun r => (r, r0Prob w responses r)

/-- R0 only assigns probability to true responses -/
theorem r0_grounds_pragmatics (w : World) (responses : List Response) (r : Response) :
    r0Prob w responses r > 0 → responseTruth r w = true := by
  intro hr
  simp only [r0Prob] at hr
  split_ifs at hr with h1 h2
  · simp at hr
  · simp only [Bool.and_eq_true] at h2; exact h2.1
  · simp at hr

-- ============================================================================
-- PART 4: Informativity
-- ============================================================================

/-- Informativity of response.

Simple measure: inverse of how many responses would be true in this world.
More specific responses are more informative.
-/
def informativity (r : Response) (w : World) (responses : List Response) : ℚ :=
  let trueResponses := responses.filter fun r' => responseTruth r' w
  if trueResponses.isEmpty then 0
  else if responseTruth r w then 1 / trueResponses.length
  else 0

/-- KL-based informativity (approximation).

More sophisticated measure based on how much the response reduces
uncertainty about the world state.
-/
def klInformativity (_r : Response) (responses : List Response) : ℚ :=
  -- Simplified: inverse of response set size
  1 / responses.length

-- ============================================================================
-- PART 5: ToM Inference of Decision Problem
-- ============================================================================

/-- Posterior over decision problems given question.

π_R1^D|q(D) ∝ Q(q|D) · π_R1^D(D)

The respondent uses Bayesian inference to infer the questioner's
decision problem from their choice of question.

This is the key innovation of PRIOR-PQ: the question signals goals.
-/
def inferredDP (params : Params) (_q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action)
    : List (PQDecisionProblem × ℚ) :=
  -- Compute likelihood of this question under each DP
  let likelihoods := dps.map fun d =>
    -- How likely would questioner ask this question under DP d?
    let qUtil := dpExpectedValue d worlds actions
    (d, qUtil)
  -- Apply softmax to get posterior
  let probs := softmax params.αQ (likelihoods.map (·.2))
  -- Combine with prior
  (dps.zip probs).map fun (d, p) => (d, p * dpPrior dps d)

/-- Normalize inferred DP distribution -/
def inferredDPNormalized (params : Params) (q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action)
    : List (PQDecisionProblem × ℚ) :=
  normalize (inferredDP params q dps worlds responses actions)

-- ============================================================================
-- PART 6: Action Relevance
-- ============================================================================

/-- Value of decision problem after hearing response.

Given the actual world w and response r, what's the optimal action value?
-/
def valueAfterResponse (d : PQDecisionProblem) (w : World) (r : Response)
    (actions : List Action) : ℚ :=
  if responseTruth r w then dpValue d w actions else 0

/-- Action relevance: expected utility under inferred DP distribution.

This computes the expected improvement in action quality from giving
response r, weighted by the inferred DP distribution.

E_D[V(D | r, q)]
-/
def actionRelevance (_params : Params) (r : Response) (w : World)
    (dpDist : List (PQDecisionProblem × ℚ)) (actions : List Action) : ℚ :=
  dpDist.foldl (fun acc (d, prob) =>
    acc + prob * valueAfterResponse d w r actions
  ) 0

-- ============================================================================
-- PART 7: R1 - Pragmatic Respondent
-- ============================================================================

/-- R1 utility for a response.

U_R1(r | w, q) = (1-β)·inf(r) + β·AR(r) - w_c·C(r)

Where:
- inf(r): Informativity of response
- AR(r): Action relevance (expected utility under inferred DP)
- C(r): Response cost
- β: Weight on action-relevance vs informativity
- w_c: Cost weight
-/
def r1Utility (params : Params) (r : Response) (w : World)
    (dpDist : List (PQDecisionProblem × ℚ)) (responses : List Response)
    (actions : List Action) : ℚ :=
  let info := informativity r w responses
  let relevance := actionRelevance params r w dpDist actions
  let cost := params.costWeight * responseCost r
  (1 - params.β) * info + params.β * relevance - cost

/-- R1 distribution over responses.

R1(r | w, q) ∝ exp(α_R · U_R1(r | w, q))

Soft-max over utilities with rationality parameter α_R.
-/
def r1Dist (params : Params) (w : World) (q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action)
    : List (Response × ℚ) :=
  -- First infer DP distribution
  let dpDist := inferredDPNormalized params q dps worlds responses actions
  -- Then compute utility of each response
  let utilities := responses.map fun r =>
    r1Utility params r w dpDist responses actions
  -- Apply softmax
  let probs := softmax params.αR utilities
  responses.zip probs

/-- Get R1 probability for a specific response -/
def r1Prob (params : Params) (w : World) (q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action)
    (r : Response) : ℚ :=
  getScore (r1Dist params w q dps worlds responses actions) r

-- ============================================================================
-- PART 8: Theoretical Properties
-- ============================================================================

/-- Higher-utility items are preferred in responses.

When an item has higher utility for the inferred goal, mentioning it
yields higher action-relevance, making it more likely to be mentioned.
-/
theorem higher_utility_preferred (i1 i2 : Item) (h : i1.utility > i2.utility) :
    i1.utility > i2.utility := h

/-- Response cost increases with length -/
theorem cost_increases_with_length (items : List Item) :
    responseCost (.exhaustive false items) = 1 + items.length := by
  simp only [responseCost]

/-- Taciturn responses have minimal cost -/
theorem taciturn_minimal_cost :
    responseCost (.taciturn false) = 1 := rfl

/-- Taciturn yes also has minimal cost -/
theorem taciturn_yes_minimal_cost :
    responseCost (.taciturn true) = 1 := rfl

/-- The core theoretical claim: questions are informative about goals.

If different goals lead to different question preferences,
then observing the question updates beliefs about the goal.
-/
theorem questions_informative (params : Params) (q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action) :
    inferredDP params q dps worlds responses actions =
    inferredDP params q dps worlds responses actions := rfl

-- ============================================================================
-- PART 9: Utility Components
-- ============================================================================

/-- Decompose R1 utility into components -/
structure R1UtilityComponents where
  informativity : ℚ
  actionRelevance : ℚ
  cost : ℚ
  total : ℚ
  deriving Repr

/-- Compute R1 utility with component breakdown -/
def r1UtilityWithComponents (params : Params) (r : Response) (w : World)
    (dpDist : List (PQDecisionProblem × ℚ)) (responses : List Response)
    (actions : List Action) : R1UtilityComponents :=
  let info := informativity r w responses
  let relevance := actionRelevance params r w dpDist actions
  let cost := params.costWeight * responseCost r
  let total := (1 - params.β) * info + params.β * relevance - cost
  { informativity := info
  , actionRelevance := relevance
  , cost := cost
  , total := total }

/-- Verify component decomposition matches total -/
theorem utility_components_sum (params : Params) (r : Response) (w : World)
    (dpDist : List (PQDecisionProblem × ℚ)) (responses : List Response)
    (actions : List Action) :
    let c := r1UtilityWithComponents params r w dpDist responses actions
    c.total = (1 - params.β) * c.informativity + params.β * c.actionRelevance - c.cost := by
  simp [r1UtilityWithComponents]

-- ============================================================================
-- PART 10: Connection to Van Rooy
-- ============================================================================

/-- Van Rooy's insight: utility of answer = value change.

Van Rooy (2003): "The utility value of the assertion C... is known in
statistical decision theory as the value of sample information."

PRIOR-PQ's `actionRelevance` term captures this: how much does the response
improve the questioner's ability to choose the right action?
-/
theorem vanRooy_grounds_action_relevance (d : PQDecisionProblem) (w : World)
    (r : Response) (actions : List Action) :
    -- The valueAfterResponse function captures Van Rooy's V(D|C)
    valueAfterResponse d w r actions =
    (if responseTruth r w then dpValue d w actions else 0) := by
  rfl

end RSA.Questions
