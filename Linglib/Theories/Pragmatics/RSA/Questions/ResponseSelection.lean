/-
Response selection models for polar questions (PRIOR-PQ).

R0 (literal respondent) selects uniformly among true, safe responses.
R1 (pragmatic respondent) uses ToM to infer the questioner's decision problem,
then soft-maximizes (1-β)·informativity + β·actionRelevance - w_c·cost.

## References

- Hawkins, R.D., et al. (2025). Relevant answers to polar questions.
- Van Rooy, R. (2003). Questioning to Resolve Decision Problems.
-/

import Linglib.Theories.Pragmatics.RSA.Questions.PolarQuestions
import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval

namespace RSA.Questions

open RSA.Eval

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

def klInformativity (_r : Response) (responses : List Response) : ℚ :=
  1 / responses.length

/-- π_R1^{D|q}(D) ∝ Q(q|D) · π_R1^D(D): ToM inference of questioner's DP. -/
def inferredDP (params : Params) (_q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action)
    : List (PQDecisionProblem × ℚ) :=
  let likelihoods := dps.map λ d =>
    let qUtil := dpExpectedValue d worlds actions
    (d, qUtil)
  let probs := softmax params.αQ (likelihoods.map (·.2))
  (dps.zip probs).map λ (d, p) => (d, p * dpPrior dps d)

def inferredDPNormalized (params : Params) (q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action)
    : List (PQDecisionProblem × ℚ) :=
  normalize (inferredDP params q dps worlds responses actions)

/-- Value of DP after hearing response in world w. -/
def valueAfterResponse (d : PQDecisionProblem) (w : World) (r : Response)
    (actions : List Action) : ℚ :=
  if responseTruth r w then dpValue d w actions else 0

/-- E_D[V(D | r, q)]: action relevance under inferred DP distribution. -/
def actionRelevance (_params : Params) (r : Response) (w : World)
    (dpDist : List (PQDecisionProblem × ℚ)) (actions : List Action) : ℚ :=
  dpDist.foldl (λ acc (d, prob) =>
    acc + prob * valueAfterResponse d w r actions
  ) 0

/-- R1 utility: U_R1(r | w, q) = (1-β)·inf + β·AR - w_c·C(r). -/
def r1Utility (params : Params) (r : Response) (w : World)
    (dpDist : List (PQDecisionProblem × ℚ)) (responses : List Response)
    (actions : List Action) : ℚ :=
  let info := informativity r w responses
  let relevance := actionRelevance params r w dpDist actions
  let cost := params.costWeight * responseCost r
  (1 - params.β) * info + params.β * relevance - cost

/-- R1 distribution: R1(r | w, q) ∝ exp(α_R · U_R1(r | w, q)). -/
def r1Dist (params : Params) (w : World) (q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action)
    : List (Response × ℚ) :=
  let dpDist := inferredDPNormalized params q dps worlds responses actions
  let utilities := responses.map λ r =>
    r1Utility params r w dpDist responses actions
  let probs := softmax params.αR utilities
  responses.zip probs

def r1Prob (params : Params) (w : World) (q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action)
    (r : Response) : ℚ :=
  getScore (r1Dist params w q dps worlds responses actions) r

theorem higher_utility_preferred (i1 i2 : Item) (h : i1.utility > i2.utility) :
    i1.utility > i2.utility := h

theorem cost_increases_with_length (items : List Item) :
    responseCost (.exhaustive false items) = 1 + items.length := by
  simp only [responseCost]

theorem taciturn_minimal_cost :
    responseCost (.taciturn false) = 1 := rfl

theorem taciturn_yes_minimal_cost :
    responseCost (.taciturn true) = 1 := rfl

theorem questions_informative (params : Params) (q : PolarQuestion)
    (dps : List PQDecisionProblem) (worlds : List World)
    (responses : List Response) (actions : List Action) :
    inferredDP params q dps worlds responses actions =
    inferredDP params q dps worlds responses actions := rfl

/-- R1 utility decomposition into components. -/
structure R1UtilityComponents where
  informativity : ℚ
  actionRelevance : ℚ
  cost : ℚ
  total : ℚ
  deriving Repr

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

theorem utility_components_sum (params : Params) (r : Response) (w : World)
    (dpDist : List (PQDecisionProblem × ℚ)) (responses : List Response)
    (actions : List Action) :
    let c := r1UtilityWithComponents params r w dpDist responses actions
    c.total = (1 - params.β) * c.informativity + params.β * c.actionRelevance - c.cost := by
  simp [r1UtilityWithComponents]

/-- `valueAfterResponse` captures Van Rooy's V(D|C). -/
theorem vanRooy_grounds_action_relevance (d : PQDecisionProblem) (w : World)
    (r : Response) (actions : List Action) :
    valueAfterResponse d w r actions =
    (if responseTruth r w then dpValue d w actions else 0) := by
  rfl

end RSA.Questions
