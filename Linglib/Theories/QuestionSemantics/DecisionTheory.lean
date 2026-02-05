import Linglib.Theories.QuestionSemantics.Partition

/-!
# Decision-Theoretic Question Semantics

Van Rooy's grounding of question semantics in decision theory.
Q refines Q' iff for all DPs, Value(Q) >= Value(Q') (Blackwell's theorem).

- Van Rooy (2003). Questioning to Resolve Decision Problems. L&P 26.
- Van Rooy (2003). Quality and Quantity of Information Exchange. JoLLI.
- Blackwell (1953). Equivalent Comparisons of Experiments.
-/

namespace QuestionSemantics

section DecisionProblems

/-- A decision problem D = (W, A, U, pi) with utility and prior. -/
structure DecisionProblem (W A : Type*) where
  /-- Utility of action a in world w -/
  utility : W -> A -> ℚ
  /-- Prior beliefs over worlds (should sum to 1 for proper probability) -/
  prior : W -> ℚ

namespace DecisionProblem

variable {W A : Type*}

/-- A uniform prior over a finite list of worlds -/
def uniformPrior [BEq W] (worlds : List W) : W -> ℚ :=
  let n := worlds.length
  if n == 0 then λ _ => 0
  else λ w => if worlds.contains w then 1 / n else 0

/-- Create a decision problem with uniform prior -/
def withUniformPrior [BEq W] (utility : W -> A -> ℚ) (worlds : List W) : DecisionProblem W A where
  utility := utility
  prior := uniformPrior worlds

end DecisionProblem

end DecisionProblems

section ExpectedUtility

/-- Expected utility of action a given beliefs. -/
def expectedUtility {W A : Type*} (dp : DecisionProblem W A)
    (worlds : List W) (a : A) : ℚ :=
  worlds.foldl (λ acc w => acc + dp.prior w * dp.utility w a) 0

/-- Optimal action: the one with highest expected utility -/
def optimalAction {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A) : Option A :=
  actions.foldl (λ best a =>
    match best with
    | none => some a
    | some b => if expectedUtility dp worlds a > expectedUtility dp worlds b
                then some a else some b
  ) none

/-- Value of a decision problem: EU of optimal action -/
def dpValue {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A) : ℚ :=
  match optimalAction dp worlds actions with
  | some a => expectedUtility dp worlds a
  | none => 0

/-- Conditional expected utility of action a given proposition C is true. -/
def conditionalEU {W A : Type*} (dp : DecisionProblem W A)
    (worlds : List W) (a : A) (c : W -> Bool) : ℚ :=
  let cWorlds := worlds.filter c
  let totalProb := cWorlds.foldl (λ acc w => acc + dp.prior w) 0
  if totalProb == 0 then 0
  else cWorlds.foldl (λ acc w =>
    acc + (dp.prior w / totalProb) * dp.utility w a
  ) 0

/-- Value of decision problem after learning C (best EU among actions) -/
def valueAfterLearning {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c : W -> Bool) : ℚ :=
  let cWorlds := worlds.filter c
  actions.foldl (λ best a =>
    max best (conditionalEU dp cWorlds a c)
  ) 0

/-- UV(C) = V(D|C) - V(D), the utility value of learning proposition C. -/
def utilityValue {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c : W -> Bool) : ℚ :=
  valueAfterLearning dp worlds actions c - dpValue dp worlds actions

/-- Probability of a cell in the partition -/
def cellProbability {W A : Type*} (dp : DecisionProblem W A)
    (worlds : List W) (cell : W -> Bool) : ℚ :=
  let cellWorlds := worlds.filter cell
  cellWorlds.foldl (λ acc w => acc + dp.prior w) 0

/-- EUV(Q) = Sum_{q in Q} P(q) * UV(q), expected utility value of question Q. -/
def questionUtility {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) : ℚ :=
  q.foldl (λ acc cell =>
    let prob := cellProbability dp worlds cell
    let uv := utilityValue dp worlds actions cell
    acc + prob * uv
  ) 0

/-- Question utility is always non-negative. -/
theorem questionUtility_nonneg {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) :
    questionUtility dp worlds actions q >= 0 := by
  sorry -- Requires showing EU with more info >= EU with less info

end ExpectedUtility

section Maximin

/-- S(a) = min_w U(w, a), security level of action a. -/
def securityLevel {W A : Type*} (dp : DecisionProblem W A) (worlds : List W) (a : A) : ℚ :=
  match worlds with
  | [] => 0
  | w :: ws => ws.foldl (λ m w' => min m (dp.utility w' a)) (dp.utility w a)

/-- MV = max_a min_w U(w, a), maximin value. -/
def maximinValue {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A) : ℚ :=
  match actions with
  | [] => 0
  | a :: as => as.foldl (λ m a' =>
      max m (securityLevel dp worlds a')
    ) (securityLevel dp worlds a)

/-- Conditional security level: worst case within cell C -/
def conditionalSecurityLevel {W A : Type*} (dp : DecisionProblem W A)
    (worlds : List W) (a : A) (c : W -> Bool) : ℚ :=
  let cWorlds := worlds.filter c
  securityLevel dp cWorlds a

/-- Maximin value after learning C -/
def maximinAfterLearning {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c : W -> Bool) : ℚ :=
  let cWorlds := worlds.filter c
  maximinValue dp cWorlds actions

/-- Maximin utility value of learning C -/
def maximinUtilityValue {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c : W -> Bool) : ℚ :=
  maximinAfterLearning dp worlds actions c - maximinValue dp worlds actions

/-- MV(Q) = min_{q in Q} MV(q), maximin question value. -/
def questionMaximin {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) : ℚ :=
  match q with
  | [] => 0
  | c :: cs => cs.foldl (λ m cell =>
      min m (maximinUtilityValue dp worlds actions cell)
    ) (maximinUtilityValue dp worlds actions c)

/-- Maximin value of information is always non-negative. -/
theorem maximinUtilityValue_nonneg {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c : W -> Bool) :
    maximinUtilityValue dp worlds actions c >= 0 := by
  sorry -- min over subset >= min over superset

end Maximin

section Blackwell

open GSQuestion in
/-- Blackwell (easy direction): refinement implies universal dominance. -/
theorem blackwell_refinement_implies_dominance {W A : Type*} [DecidableEq A]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (h : q ⊑ q') (dp : DecisionProblem W A) :
    questionUtility dp worlds actions (q.toQuestion worlds) >=
    questionUtility dp worlds actions (q'.toQuestion worlds) := by
  sorry

open GSQuestion in
/-- Blackwell (hard direction): universal dominance implies refinement. -/
theorem blackwell_dominance_implies_refinement {W A : Type*} [DecidableEq A] [DecidableEq W]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (h : forall dp : DecisionProblem W A,
         questionUtility dp worlds actions (q.toQuestion worlds) >=
         questionUtility dp worlds actions (q'.toQuestion worlds)) :
    q ⊑ q' := by
  sorry

open GSQuestion in
/-- Blackwell's Theorem (full characterization).

Semantic refinement equals universal pragmatic dominance. -/
theorem blackwell_theorem {W A : Type*} [DecidableEq A] [DecidableEq W]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (_hWorlds : worlds.length > 0) (_hActions : actions.length > 0) :
    q ⊑ q' <->
    forall dp : DecisionProblem W A,
      questionUtility dp worlds actions (q.toQuestion worlds) >=
      questionUtility dp worlds actions (q'.toQuestion worlds) := by
  constructor
  · intro h dp
    exact blackwell_refinement_implies_dominance q q' worlds actions h dp
  · intro h
    exact blackwell_dominance_implies_refinement q q' worlds actions h

open GSQuestion in
/-- Blackwell for Maximin: Q refines Q' iff Q dominates Q' under maximin. -/
theorem blackwell_maximin {W A : Type*} [DecidableEq A] [DecidableEq W]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (_hWorlds : worlds.length > 0) (_hActions : actions.length > 0) :
    q ⊑ q' <->
    forall dp : DecisionProblem W A,
      questionMaximin dp worlds actions (q.toQuestion worlds) >=
      questionMaximin dp worlds actions (q'.toQuestion worlds) := by
  sorry -- Similar proof structure to blackwell_theorem

end Blackwell

section MentionSome

/-- C resolves decision problem if one action dominates after learning C -/
def resolves {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c : W -> Bool) : Bool :=
  let cWorlds := worlds.filter c
  match actions with
  | [] => true
  | a :: rest =>
    rest.all λ b =>
      cWorlds.all λ w => dp.utility w a >= dp.utility w b

/-- Set of answers that resolve the decision problem -/
def resolvingAnswers {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) : List (W -> Bool) :=
  q.filter λ cell => resolves dp worlds actions cell

/-- A question has mention-some reading if multiple non-disjoint cells resolve the DP. -/
def isMentionSome {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) : Bool :=
  let resolving := resolvingAnswers dp worlds actions q
  resolving.length > 1 &&
    resolving.any λ c1 =>
      resolving.any λ c2 =>
        worlds.any λ w => c1 w && c2 w

/-- Mention-all reading: need the complete partition to resolve DP -/
def isMentionAll {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) : Bool :=
  !isMentionSome dp worlds actions q

end MentionSome

section SpecialDPs

/-- An epistemic DP where the agent wants to know the exact world state. -/
def epistemicDP {W A : Type*} [DecidableEq W] (target : W) : DecisionProblem W A where
  utility w _ := if w == target then 1 else 0
  prior _ := 1

/-- A complete-information DP where only exact-state knowledge is useful. -/
def completeInformationDP {W : Type*} [DecidableEq W] : DecisionProblem W W where
  utility w a := if a == w then 1 else 0
  prior _ := 1

/-- A mention-some DP: any satisfier resolves the problem. -/
def mentionSomeDP {W : Type*} (satisfies : W -> Bool) : DecisionProblem W Bool where
  utility w a := if a && satisfies w then 1 else 0
  prior _ := 1

end SpecialDPs

end QuestionSemantics
