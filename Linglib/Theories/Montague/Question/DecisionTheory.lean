import Linglib.Theories.Montague.Question.Partition

/-!
# Questions/DecisionTheory.lean

Van Rooy's Decision-Theoretic Question Semantics.

## Core Idea

Questions are asked because their answers help resolve the questioner's
decision problem. This grounds question semantics in decision theory.

A decision problem D = ⟨W, A, U, π⟩ consists of:
- W: world states
- A: actions available to the agent
- U: W × A → ℚ utility function
- π: probability distribution over W (agent's beliefs)

## Decision Criteria

Different ways to evaluate the value of information:

1. **Expected Utility** (standard): EUV(Q) = Σ P(q) × UV(q)
2. **Maximin** (pessimistic): MV(Q) = min_{q∈Q} MV(q)
3. **Minimax Loss** (regret-based): minimize worst-case regret

## Blackwell's Theorem

The semantic refinement relation (⊑) equals universal pragmatic dominance:
```
Q ⊑ Q'  ⟺  ∀DP: Value_DP(Q) ≥ Value_DP(Q')
```

This holds for ALL reasonable decision criteria!

## References

- Van Rooy (2003). Questioning to Resolve Decision Problems. L&P 26.
- Van Rooy (2003). Quality and Quantity of Information Exchange. JoLLI.
- Blackwell (1953). Equivalent Comparisons of Experiments.
- Savage (1954). The Foundations of Statistics.
-/

namespace Montague.Question

-- Decision Problems

/-- A decision problem with explicit world and action types.

The agent must choose an action a ∈ A without knowing the true world w ∈ W.
Her goal is to maximize expected utility given her beliefs. -/
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

-- Expected Utility (Standard Decision Criterion)

/-- Expected utility of action a given beliefs -/
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

-- Conditional Information Value

/-- Conditional expected utility of action a given proposition C is true -/
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

/-- Utility value of learning proposition C: UV(C) = V(D|C) - V(D)

This measures how much better off the agent is after learning C. -/
def utilityValue {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c : W -> Bool) : ℚ :=
  valueAfterLearning dp worlds actions c - dpValue dp worlds actions

/-- Probability of a cell in the partition -/
def cellProbability {W A : Type*} (dp : DecisionProblem W A)
    (worlds : List W) (cell : W -> Bool) : ℚ :=
  let cellWorlds := worlds.filter cell
  cellWorlds.foldl (λ acc w => acc + dp.prior w) 0

-- Question Utility (Expected Utility Criterion)

/-- Expected utility value of question Q:
EUV(Q) = Σ_{q∈Q} P(q) × UV(q)

This is the expected improvement in decision quality from learning
which cell contains the actual world. -/
def questionUtility {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) : ℚ :=
  q.foldl (λ acc cell =>
    let prob := cellProbability dp worlds cell
    let uv := utilityValue dp worlds actions cell
    acc + prob * uv
  ) 0

/-- Question utility is always non-negative.

This is a key result: asking a question can never hurt (in expectation). -/
theorem questionUtility_nonneg {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) :
    questionUtility dp worlds actions q >= 0 := by
  sorry -- Requires showing EU with more info >= EU with less info

-- Maximin Criterion (Pessimistic)

/-- Security level of action a: utility under worst-case world.
S(a) = min_{w} U(w, a) -/
def securityLevel {W A : Type*} (dp : DecisionProblem W A) (worlds : List W) (a : A) : ℚ :=
  match worlds with
  | [] => 0
  | w :: ws => ws.foldl (λ m w' => min m (dp.utility w' a)) (dp.utility w a)

/-- Maximin value: best security level among actions.
MV = max_a min_w U(w, a) -/
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

/-- Maximin question value: value of the WORST answer.
MV(Q) = min_{q∈Q} MV(q)

The pessimistic questioner assumes the worst answer will be given. -/
def questionMaximin {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) : ℚ :=
  match q with
  | [] => 0
  | c :: cs => cs.foldl (λ m cell =>
      min m (maximinUtilityValue dp worlds actions cell)
    ) (maximinUtilityValue dp worlds actions c)

/-- Maximin value of information is always non-negative.

Information can never hurt under maximin (unlike some criteria). -/
theorem maximinUtilityValue_nonneg {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c : W -> Bool) :
    maximinUtilityValue dp worlds actions c >= 0 := by
  sorry -- min over subset >= min over superset

-- Blackwell's Theorem

/-!
## Blackwell's Theorem

The fundamental result connecting semantic and pragmatic orderings:

```
Q ⊑ Q'  ⟺  ∀DP: Value_DP(Q) ≥ Value_DP(Q')
```

**Left-to-right (easy direction)**:
If Q refines Q', then Q's cells are subsets of Q''s cells.
More information can only help (or not hurt) decision-making.
So Q's value is at least Q''s value for any decision problem.

**Right-to-left (hard direction)**:
If Q doesn't refine Q', then there exist worlds w, v that are:
- Q-equivalent (same Q-answer)
- Q'-inequivalent (different Q'-answer)

We can construct a decision problem where knowing the Q'-answer
(which distinguishes w from v) is valuable, but the Q-answer isn't.

**Significance**:
G&S partition semantics is not arbitrary - it's the unique way to
compare questions that respects pragmatic usefulness across all goals.
-/

open GSQuestion in
/-- Blackwell (easy direction): refinement implies universal dominance.

If Q refines Q', then for ANY decision problem, Q is at least as useful. -/
theorem blackwell_refinement_implies_dominance {W A : Type*} [DecidableEq A]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (h : q ⊑ q') (dp : DecisionProblem W A) :
    questionUtility dp worlds actions (q.toQuestion worlds) >=
    questionUtility dp worlds actions (q'.toQuestion worlds) := by
  -- Proof sketch:
  -- q refines q' means q's cells are subsets of q''s cells
  -- Finer partition = more information
  -- More information = higher expected utility (by convexity of max)
  sorry

open GSQuestion in
/-- Blackwell (hard direction): universal dominance implies refinement.

If Q dominates Q' for ALL decision problems, then Q must refine Q'.

Proof by contraposition: if Q doesn't refine Q', construct a DP
where Q' is strictly better. -/
theorem blackwell_dominance_implies_refinement {W A : Type*} [DecidableEq A] [DecidableEq W]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (h : forall dp : DecisionProblem W A,
         questionUtility dp worlds actions (q.toQuestion worlds) >=
         questionUtility dp worlds actions (q'.toQuestion worlds)) :
    q ⊑ q' := by
  -- Proof by contraposition:
  -- Assume q does not refine q'
  -- Then ∃w,v: q.equiv w v = true but q'.equiv w v = false
  -- Construct DP where action a is optimal in w, action b is optimal in v
  -- q' distinguishes w from v (different cells), so q' is useful
  -- q doesn't distinguish them (same cell), so q is not as useful
  -- This contradicts h
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
/-- Blackwell for Maximin: same result holds.

This shows the robustness of G&S semantics - it's not tied to
expected utility specifically. -/
theorem blackwell_maximin {W A : Type*} [DecidableEq A] [DecidableEq W]
    (q q' : GSQuestion W) (worlds : List W) (actions : List A)
    (_hWorlds : worlds.length > 0) (_hActions : actions.length > 0) :
    q ⊑ q' <->
    forall dp : DecisionProblem W A,
      questionMaximin dp worlds actions (q.toQuestion worlds) >=
      questionMaximin dp worlds actions (q'.toQuestion worlds) := by
  sorry -- Similar proof structure to blackwell_theorem

-- Mention-Some vs Mention-All

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

/-- A question has a mention-some reading if:
1. Multiple cells resolve the DP
2. These cells are non-disjoint (can give partial answer) -/
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

-- Special Decision Problems

/-- An epistemic DP where the agent wants to know the exact world state. -/
def epistemicDP {W A : Type*} [DecidableEq W] (target : W) : DecisionProblem W A where
  utility w _ := if w == target then 1 else 0
  prior _ := 1

/-- A complete-information DP where only knowing the exact state is useful.
This generates mention-all readings. -/
def completeInformationDP {W : Type*} [DecidableEq W] : DecisionProblem W W where
  utility w a := if a == w then 1 else 0
  prior _ := 1

/-- A mention-some DP: any satisfier resolves the problem.
"Where can I buy coffee?" - any coffee shop suffices. -/
def mentionSomeDP {W : Type*} (satisfies : W -> Bool) : DecisionProblem W Bool where
  utility w a := if a && satisfies w then 1 else 0
  prior _ := 1

end Montague.Question
