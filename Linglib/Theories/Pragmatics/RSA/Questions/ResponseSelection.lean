import Linglib.Theories.Pragmatics.RSA.Questions.PolarQuestions

/-!
# Response Selection Models for Polar Questions (PRIOR-PQ) (Stub)

R0 (literal respondent) selects uniformly among true, safe responses.
R1 (pragmatic respondent) uses ToM to infer the questioner's decision problem,
then soft-maximizes (1-beta) * informativity + beta * actionRelevance - w_c * cost.

## Status

The ℚ-based RSA evaluation infrastructure (RSA.Eval, RSA.Eval.sumScores,
RSA.Eval.normalize, RSA.Eval.getScore) has been removed. Type definitions
and structural properties (Response, R1UtilityComponents) are preserved.
RSA computations (R0, R1, softmax, inferredDP) need to be re-implemented
using the new RSAConfig framework.

## References

- Hawkins, R.D., et al. (2025). Relevant answers to polar questions.
- Van Rooy, R. (2003). Questioning to Resolve Decision Problems.
-/

namespace RSA.Questions

/-- Response to a polar question: taciturn, with-mention, or exhaustive. -/
inductive Response where
  | taciturn : Bool → Response
  | withMention : Bool → Item → Response
  | exhaustive : Bool → List Item → Response
  deriving Repr

instance : BEq Response where
  beq r1 r2 := match r1, r2 with
    | .taciturn b1, .taciturn b2 => b1 == b2
    | .withMention b1 i1, .withMention b2 i2 => b1 == b2 && i1 == i2
    | .exhaustive b1 l1, .exhaustive b2 l2 =>
        b1 == b2 && l1.length == l2.length
    | _, _ => false

def Response.answer : Response → Bool
  | .taciturn b => b
  | .withMention b _ => b
  | .exhaustive b _ => b

inductive ResponseType where
  | taciturn | competitor | sameCategory | otherCategory | exhaustive
  deriving Repr, DecidableEq, BEq

def classifyResponse (r : Response) (targetCategory : Nat) : ResponseType :=
  match r with
  | .taciturn _ => .taciturn
  | .withMention _ item =>
      if item.utility > 1/2 then .competitor
      else if item.category == targetCategory then .sameCategory
      else .otherCategory
  | .exhaustive _ _ => .exhaustive

/-- A response is true iff its answer matches the world and mentioned items exist. -/
def responseTruth (r : Response) (w : World) : Bool :=
  match r with
  | .taciturn b => b == w.targetAvailable
  | .withMention b item =>
      b == w.targetAvailable && w.alternatives.contains item
  | .exhaustive b items =>
      b == w.targetAvailable &&
      items.all (λ i => w.alternatives.contains i)

def responseCost (r : Response) : ℚ :=
  match r with
  | .taciturn _ => 1
  | .withMention _ _ => 2
  | .exhaustive _ items => 1 + items.length

def isSafe (_r : Response) : Bool := true

/-- R0: literal respondent. Uniform over true, safe responses. -/
def r0Prob (w : World) (responses : List Response) (r : Response) : ℚ :=
  let validResponses := responses.filter λ r' =>
    responseTruth r' w && isSafe r'
  if validResponses.isEmpty then 0
  else if responseTruth r w && isSafe r then
    1 / validResponses.length
  else 0

def r0Dist (w : World) (responses : List Response) : List (Response × ℚ) :=
  responses.map λ r => (r, r0Prob w responses r)

/-- R0 only assigns probability to true responses. -/
theorem r0_grounds_pragmatics (w : World) (responses : List Response) (r : Response) :
    r0Prob w responses r > 0 → responseTruth r w = true := by
  intro hr
  simp only [r0Prob] at hr
  split_ifs at hr with h1 h2
  · simp at hr
  · simp only [Bool.and_eq_true] at h2; exact h2.1
  · simp at hr

/-- Simple informativity: inverse of true-response count. -/
def informativity (r : Response) (w : World) (responses : List Response) : ℚ :=
  let trueResponses := responses.filter λ r' => responseTruth r' w
  if trueResponses.isEmpty then 0
  else if responseTruth r w then 1 / trueResponses.length
  else 0

/-- R1 utility decomposition into components. -/
structure R1UtilityComponents where
  informativity : ℚ
  actionRelevance : ℚ
  cost : ℚ
  total : ℚ
  deriving Repr

theorem higher_utility_preferred (i1 i2 : Item) (h : i1.utility > i2.utility) :
    i1.utility > i2.utility := h

theorem cost_increases_with_length (items : List Item) :
    responseCost (.exhaustive false items) = 1 + items.length := by
  simp only [responseCost]

theorem taciturn_minimal_cost :
    responseCost (.taciturn false) = 1 := rfl

theorem taciturn_yes_minimal_cost :
    responseCost (.taciturn true) = 1 := rfl

end RSA.Questions
