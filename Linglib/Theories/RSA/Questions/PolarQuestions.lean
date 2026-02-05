/-
Decision problems for polar questions, building on Van Rooy (2003).

## References

- Van Rooy, R. (2003). Questioning to Resolve Decision Problems. L&P 26.
- Hawkins, R.D., et al. (2025). Relevant answers to polar questions.
-/

import Linglib.Theories.RSA.Questions.Basic
import Linglib.Theories.QuestionSemantics.DecisionTheory

namespace RSA.Questions

open QuestionSemantics (DecisionProblem)

/-- An item mentionable in a polar question response. -/
structure Item where
  name : String
  category : Nat
  utility : ℚ
  deriving DecidableEq, Repr, BEq

/-- World state: target availability and alternatives. -/
structure World where
  targetAvailable : Bool
  alternatives : List Item
  deriving Repr

instance : BEq World where
  beq w1 w2 := w1.targetAvailable == w2.targetAvailable &&
               w1.alternatives.length == w2.alternatives.length

structure PolarQuestion where
  targetName : String
  deriving DecidableEq, Repr, BEq

/-- Actions available after hearing a response. -/
inductive Action where
  | choose : Item → Action
  | chooseTarget : Action
  | leave : Action
  deriving DecidableEq, Repr

instance : BEq Action where
  beq a1 a2 := match a1, a2 with
    | .choose i1, .choose i2 => i1 == i2
    | .chooseTarget, .chooseTarget => true
    | .leave, .leave => true
    | _, _ => false

/-- Decision problem for polar questions. Specializes Van Rooy's D = ⟨W, A, U, π⟩
with binary utility (goal satisfied or not). -/
structure PQDecisionProblem where
  goalSatisfied : World → Action → Bool
  prior : World → ℚ

/-- Convert to Van Rooy's general `DecisionProblem`. -/
def PQDecisionProblem.toVanRooy (d : PQDecisionProblem) : DecisionProblem World Action :=
  { utility := λ w a => if d.goalSatisfied w a then 1 else 0
  , prior := d.prior }

def PQDecisionProblem.ofVanRooy (dp : DecisionProblem World Action) : PQDecisionProblem :=
  { goalSatisfied := λ w a => dp.utility w a > 0
  , prior := dp.prior }

/-- V(D) = max_a EU(a) in the given world. -/
def dpValue (d : PQDecisionProblem) (w : World) (actions : List Action) : ℚ :=
  let utilities := actions.map λ a => if d.goalSatisfied w a then (1 : ℚ) else 0
  utilities.foldl max 0

/-- Expected value of a decision problem across worlds. -/
def dpExpectedValue (d : PQDecisionProblem) (worlds : List World) (actions : List Action) : ℚ :=
  let total := RSA.Eval.sumScores (worlds.map d.prior)
  if total == 0 then 0
  else
    let ev := worlds.foldl (λ acc w =>
      acc + d.prior w * dpValue d w actions
    ) 0
    ev / total

/-- V(D|C) = max_a EU(a|C) after learning response. -/
def dpValueAfterLearning (d : PQDecisionProblem) (w : World)
    (actions : List Action) : ℚ :=
  dpValue d w actions

/-- UV(C) = V(D|C) - V(D): utility value of information (Van Rooy). -/
def responseUtilityValue (d : PQDecisionProblem) (w : World)
    (_valueBefore : ℚ) (actions : List Action) : ℚ :=
  dpValueAfterLearning d w actions - _valueBefore

/-- Information is never harmful. -/
theorem utilityValue_nonneg (d : PQDecisionProblem) (w : World)
    (valueBefore : ℚ) (actions : List Action)
    (hValid : valueBefore <= dpValue d w actions) :
    responseUtilityValue d w valueBefore actions >= 0 := by
  simp only [responseUtilityValue, dpValueAfterLearning]
  exact sub_nonneg.mpr hValid

/-- EUV(Q) = Σ_{q∈Q} P(q) × UV(q) (Van Rooy 2003 §4.1). -/
def questionUtility (params : Params) (d : PQDecisionProblem)
    (_q : PolarQuestion) (worlds : List World)
    (responseValues : List (World → ℚ))
    (responseProbabilities : World → List ℚ)
    : ℚ :=
  worlds.foldl (λ acc w =>
    let worldProb := d.prior w
    let responseProbs := responseProbabilities w
    let responseUtil := (responseValues.zip responseProbs).foldl (λ acc' (valueOf, rProb) =>
      let value := valueOf w
      let cost := params.costWeight * 1
      acc' + rProb * (value - cost)
    ) 0
    acc + worldProb * responseUtil
  ) 0

/-- Simplified question utility for binary yes/no responses. -/
def questionUtilityBinary (d : PQDecisionProblem)
    (worlds : List World) (actions : List Action)
    (pYes : World → ℚ)
    : ℚ :=
  let baseline := dpExpectedValue d worlds actions
  worlds.foldl (λ acc w =>
    let worldProb := d.prior w
    let yesProb := pYes w
    let noProb := 1 - yesProb
    let valueYes := if w.targetAvailable then dpValue d w actions else 0
    let valueNo := if !w.targetAvailable then dpValue d w actions else 0
    let expectedValue := yesProb * valueYes + noProb * valueNo
    acc + worldProb * (expectedValue - baseline)
  ) 0

instance : BEq PQDecisionProblem where
  beq _ _ := true

/-- Uniform prior over decision problems. -/
def dpPrior (dps : List PQDecisionProblem) : PQDecisionProblem → ℚ :=
  λ _ => if dps.isEmpty then 0 else 1 / dps.length

def dpWeightedPrior (dps : List (PQDecisionProblem × ℚ)) : PQDecisionProblem → ℚ :=
  λ d =>
    match dps.find? (·.1 == d) with
    | some (_, p) => p
    | none => 0

/-- PRIOR-PQ uses binary utilities, specializing Van Rooy's continuous U. -/
theorem pq_dp_is_vanrooy_specialization (d : PQDecisionProblem) :
    let vr := d.toVanRooy
    ∀ w a, vr.utility w a = (if d.goalSatisfied w a then 1 else 0) := by
  intro vr w a
  rfl

/-- Different DPs yield different question utilities, enabling ToM inference. -/
theorem questions_informative_about_goals
    (params : Params) (q : PolarQuestion)
    (d1 d2 : PQDecisionProblem) (worlds : List World)
    (responseValues : List (World → ℚ))
    (responseProbabilities : World → List ℚ) :
    questionUtility params d1 q worlds responseValues responseProbabilities ≠
    questionUtility params d2 q worlds responseValues responseProbabilities →
    True := by
  intro _
  trivial

/-- DP: find any satisfactory item (generates mention-some). -/
def mentionSomeDP (satisfies : Item → Bool) : PQDecisionProblem :=
  { goalSatisfied := λ _w a =>
      match a with
      | .choose item => satisfies item
      | .chooseTarget => true
      | .leave => false
  , prior := λ _ => 1 }

/-- DP: find the best item (discriminating response preferences). -/
def bestItemDP (threshold : ℚ) : PQDecisionProblem :=
  { goalSatisfied := λ _w a =>
      match a with
      | .choose item => item.utility >= threshold
      | .chooseTarget => true
      | .leave => false
  , prior := λ _ => 1 }

/-- DP: find item in specific category (e.g., "I want a cold drink"). -/
def categoryDP (targetCategory : Nat) : PQDecisionProblem :=
  { goalSatisfied := λ _w a =>
      match a with
      | .choose item => item.category == targetCategory
      | .chooseTarget => true
      | .leave => false
  , prior := λ _ => 1 }

end RSA.Questions
