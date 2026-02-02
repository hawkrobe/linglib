/-
# RSA/Questions/PolarQuestions.lean

Decision Problems for Polar Questions.

## Overview

This module provides the decision-theoretic foundation for polar question
models, building on Van Rooy (2003) and extending to PRIOR-PQ (Hawkins et al. 2025).

## Key Concepts

- **PQDecisionProblem**: Decision problem specialized for polar questions
- **dpValue**: Value of a decision problem (max EU over actions)
- **questionUtility**: Expected utility of asking a question

## Grounding in Van Rooy (2003)

Van Rooy's key insight: questions are asked to resolve decision problems.
The utility of an answer depends on how much it helps choose the right action.

PRIOR-PQ builds on this by adding Theory of Mind:
- **Van Rooy**: Respondent knows the decision problem
- **PRIOR-PQ**: Respondent *infers* decision problem from question choice

## References

- Van Rooy, R. (2003). Questioning to Resolve Decision Problems. L&P 26.
- Hawkins, R.D., et al. (2025). Relevant answers to polar questions.
-/

import Linglib.Theories.RSA.Questions.Basic
import Linglib.Theories.Montague.Question.DecisionTheory

namespace RSA.Questions

open Montague.Question (DecisionProblem)

-- ============================================================================
-- PART 1: Domain Types
-- ============================================================================

/-- Items that can be mentioned in a response to a polar question.

In the iced tea scenario:
- name: "iced coffee"
- category: 0 (cold drinks)
- utility: 0.9 (high utility for the "get a cold drink" goal)
-/
structure Item where
  name : String
  category : Nat       -- Category identifier
  utility : ℚ          -- Utility for questioner's goal (0-1)
  deriving DecidableEq, Repr, BEq

/-- World state: which items are available.

For polar questions about availability, the world specifies:
- Whether the target item is available
- What alternative items exist
-/
structure World where
  targetAvailable : Bool
  alternatives : List Item
  deriving Repr

instance : BEq World where
  beq w1 w2 := w1.targetAvailable == w2.targetAvailable &&
               w1.alternatives.length == w2.alternatives.length

/-- Polar question: asks about availability of target item -/
structure PolarQuestion where
  targetName : String
  deriving DecidableEq, Repr, BEq

/-- Actions available to the questioner after hearing response -/
inductive Action where
  /-- Choose a specific alternative item -/
  | choose : Item → Action
  /-- Choose the target item (if available) -/
  | chooseTarget : Action
  /-- Leave without choosing anything -/
  | leave : Action
  deriving DecidableEq, Repr

instance : BEq Action where
  beq a1 a2 := match a1, a2 with
    | .choose i1, .choose i2 => i1 == i2
    | .chooseTarget, .chooseTarget => true
    | .leave, .leave => true
    | _, _ => false

-- ============================================================================
-- PART 2: Decision Problem for Polar Questions
-- ============================================================================

/-- Decision problem for polar question scenarios.

This specializes Van Rooy's general `DecisionProblem W A` structure for the
polar question domain. We use a Boolean utility (goal satisfied or not)
rather than continuous utilities for simplicity.

## Fields

- `goalSatisfied`: Whether an action achieves the questioner's goal in a world
- `prior`: Prior probability over worlds

## Example

For "Do you have iced tea?" with goal "get a cold drink":
- goalSatisfied w (choose icedCoffee) = icedCoffee.category == coldDrinks
- goalSatisfied w chooseTarget = true  -- iced tea would satisfy
- goalSatisfied w leave = false
-/
structure PQDecisionProblem where
  /-- Does action a satisfy the goal in world w? -/
  goalSatisfied : World → Action → Bool
  /-- Prior probability distribution over worlds -/
  prior : World → ℚ

/-- Convert to Van Rooy's general decision problem type -/
def PQDecisionProblem.toVanRooy (d : PQDecisionProblem) : DecisionProblem World Action :=
  { utility := fun w a => if d.goalSatisfied w a then 1 else 0
  , prior := d.prior }

/-- Create a PQ decision problem from a general decision problem -/
def PQDecisionProblem.ofVanRooy (dp : DecisionProblem World Action) : PQDecisionProblem :=
  { goalSatisfied := fun w a => dp.utility w a > 0
  , prior := dp.prior }

-- ============================================================================
-- PART 3: Decision Problem Value
-- ============================================================================

/-- Value of decision problem: max utility over actions.

Van Rooy defines: V(D) = max_a EU(a)

For PRIOR-PQ, utility is binary (0 or 1), so this is the probability
that some action satisfies the goal.

This is computed by finding the max utility action and returning its
expected utility.
-/
def dpValue (d : PQDecisionProblem) (w : World) (actions : List Action) : ℚ :=
  let utilities := actions.map fun a => if d.goalSatisfied w a then (1 : ℚ) else 0
  utilities.foldl max 0

/-- Expected value of a decision problem across all worlds -/
def dpExpectedValue (d : PQDecisionProblem) (worlds : List World) (actions : List Action) : ℚ :=
  let total := RSA.Eval.sumScores (worlds.map d.prior)
  if total == 0 then 0
  else
    let ev := worlds.foldl (fun acc w =>
      acc + d.prior w * dpValue d w actions
    ) 0
    ev / total

/-- Value of decision problem after learning response (conditional on response being true).

Van Rooy: V(D|C) = max_a EU(a|C)

After learning a response, the questioner can make a better action choice.
-/
def dpValueAfterLearning (d : PQDecisionProblem) (w : World)
    (actions : List Action) : ℚ :=
  -- In the actual world w, find the best action
  dpValue d w actions

-- ============================================================================
-- PART 4: Utility Value of Information
-- ============================================================================

/-- Utility value of learning response (Van Rooy's UV).

UV(C) = V(D|C) - V(D)

This measures the improvement in expected decision quality from learning
the response. Higher UV = more valuable information.

For PRIOR-PQ, learning the response tells us which alternatives exist,
enabling better action selection.
-/
def responseUtilityValue (d : PQDecisionProblem) (w : World)
    (_valueBefore : ℚ) (actions : List Action) : ℚ :=
  dpValueAfterLearning d w actions - _valueBefore

/-- Information is never harmful (UV is non-negative).

This is a fundamental result: learning more information can only
help (or not hurt) decision-making.
-/
theorem utilityValue_nonneg (d : PQDecisionProblem) (w : World)
    (valueBefore : ℚ) (actions : List Action)
    (hValid : valueBefore <= dpValue d w actions) :
    responseUtilityValue d w valueBefore actions >= 0 := by
  simp only [responseUtilityValue, dpValueAfterLearning]
  exact sub_nonneg.mpr hValid

-- ============================================================================
-- PART 5: Question Utility (Questioner Model)
-- ============================================================================

/-- Expected utility of asking a question given decision problem.

The questioner chooses a question to maximize expected utility of the answer.
This is computed by:
1. For each world w, compute probability of each response under R0
2. For each response, compute the value after learning that response
3. Sum over worlds and responses, weighted by probabilities

Van Rooy (2003) §4.1: EUV(Q) = Σ_{q∈Q} P(q) × UV(q)
-/
def questionUtility (params : Params) (d : PQDecisionProblem)
    (_q : PolarQuestion) (worlds : List World)
    (responseValues : List (World → ℚ))  -- Value of each response type
    (responseProbabilities : World → List ℚ)  -- P(response | world)
    : ℚ :=
  worlds.foldl (fun acc w =>
    let worldProb := d.prior w
    let responseProbs := responseProbabilities w
    let responseUtil := (responseValues.zip responseProbs).foldl (fun acc' (valueOf, rProb) =>
      let value := valueOf w
      let cost := params.costWeight * 1  -- Simplified cost
      acc' + rProb * (value - cost)
    ) 0
    acc + worldProb * responseUtil
  ) 0

/-- Simplified question utility for binary (yes/no) responses -/
def questionUtilityBinary (d : PQDecisionProblem)
    (worlds : List World) (actions : List Action)
    (pYes : World → ℚ)  -- P(yes | world)
    : ℚ :=
  let baseline := dpExpectedValue d worlds actions
  worlds.foldl (fun acc w =>
    let worldProb := d.prior w
    let yesProb := pYes w
    let noProb := 1 - yesProb
    -- Value after hearing yes (in worlds where yes is true)
    let valueYes := if w.targetAvailable then dpValue d w actions else 0
    -- Value after hearing no (in worlds where no is true)
    let valueNo := if !w.targetAvailable then dpValue d w actions else 0
    let expectedValue := yesProb * valueYes + noProb * valueNo
    acc + worldProb * (expectedValue - baseline)
  ) 0

-- ============================================================================
-- PART 6: Prior over Decision Problems
-- ============================================================================

instance : BEq PQDecisionProblem where
  beq _ _ := true  -- Simplified; real implementation would need structural equality

/-- Prior over decision problems (uniform by default).

In PRIOR-PQ, the respondent has uncertainty about the questioner's
decision problem. This prior encodes baseline expectations.
-/
def dpPrior (dps : List PQDecisionProblem) : PQDecisionProblem → ℚ :=
  fun _ => if dps.isEmpty then 0 else 1 / dps.length

/-- Weighted prior over decision problems -/
def dpWeightedPrior (dps : List (PQDecisionProblem × ℚ)) : PQDecisionProblem → ℚ :=
  fun d =>
    match dps.find? (·.1 == d) with
    | some (_, p) => p
    | none => 0

-- ============================================================================
-- PART 7: Theoretical Results
-- ============================================================================

/-- The decision problem structure PRIOR-PQ uses is a specialization of Van Rooy's.

Van Rooy: D = ⟨W, A, U, π⟩ with U : W × A → ℝ
PRIOR-PQ: D with U : W × A → {0, 1} (goal satisfied or not)
-/
theorem pq_dp_is_vanrooy_specialization (d : PQDecisionProblem) :
    let vr := d.toVanRooy
    ∀ w a, vr.utility w a = (if d.goalSatisfied w a then 1 else 0) := by
  intro vr w a
  rfl

/-- Different decision problems lead to different question utilities.

This is the key property that enables ToM inference: if we observe a question,
we can infer something about the questioner's decision problem.
-/
theorem questions_informative_about_goals
    (params : Params) (q : PolarQuestion)
    (d1 d2 : PQDecisionProblem) (worlds : List World)
    (responseValues : List (World → ℚ))
    (responseProbabilities : World → List ℚ) :
    -- If d1 and d2 have different question utilities, then
    -- observing q provides information about which DP the questioner has
    questionUtility params d1 q worlds responseValues responseProbabilities ≠
    questionUtility params d2 q worlds responseValues responseProbabilities →
    -- The question is informative about the DP
    True := by
  intro _
  trivial

-- ============================================================================
-- PART 8: Common Decision Problems
-- ============================================================================

/-- Decision problem: find any satisfactory item.

Utility is 1 if any action leads to a satisfying outcome.
This generates "mention-some" behavior.
-/
def mentionSomeDP (satisfies : Item → Bool) : PQDecisionProblem :=
  { goalSatisfied := fun _w a =>
      match a with
      | .choose item => satisfies item
      | .chooseTarget => true  -- Target always satisfies
      | .leave => false
  , prior := fun _ => 1 }

/-- Decision problem: find the best item.

Utility depends on item quality (utility field).
This generates more discriminating response preferences.
-/
def bestItemDP (threshold : ℚ) : PQDecisionProblem :=
  { goalSatisfied := fun _w a =>
      match a with
      | .choose item => item.utility >= threshold
      | .chooseTarget => true
      | .leave => false
  , prior := fun _ => 1 }

/-- Decision problem: find item in specific category.

Models goals like "I want a cold drink" where category matters.
-/
def categoryDP (targetCategory : Nat) : PQDecisionProblem :=
  { goalSatisfied := fun _w a =>
      match a with
      | .choose item => item.category == targetCategory
      | .chooseTarget => true
      | .leave => false
  , prior := fun _ => 1 }

end RSA.Questions
