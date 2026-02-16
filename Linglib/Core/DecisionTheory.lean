import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.BigOperators

/-!
# Core Decision Theory

Theory-neutral decision-theoretic infrastructure: decision problems, expected
utility, maximin, and mention-some/mention-all classification.

Promoted from `Theories.QuestionSemantics.DecisionTheory` so that any module
(RSA, causal decision theory, explanation models) can use decision problems
without pulling in question-semantic types.

## Design: Fintype + Finset (Hybrid)

Functions that sum over the full universe use `[Fintype W]` with `∑ w : W`.
Functions that operate on subsets (conditioning, cells) take explicit `Finset W`
and use `Finset.sum`. Functions that iterate for argmax/min keep `List A`
(since `Finset.toList` is noncomputable in Mathlib).
Question-related types (`Question W = List (W → Bool)`) remain List-based.

- Van Rooy (2003). Questioning to Resolve Decision Problems. L&P 26.
- Blackwell (1953). Equivalent Comparisons of Experiments.
-/

namespace Core.DecisionTheory

/-! ### Decision Problems -/

/-- A decision problem D = (W, A, U, π) with utility and prior. -/
structure DecisionProblem (W A : Type*) where
  /-- Utility of action a in world w -/
  utility : W -> A -> ℚ
  /-- Prior beliefs over worlds (should sum to 1 for proper probability) -/
  prior : W -> ℚ

namespace DecisionProblem

variable {W A : Type*}

/-- A uniform prior over a Fintype of worlds -/
def uniformPrior [Fintype W] [DecidableEq W] : W -> ℚ :=
  let n := Fintype.card W
  if n = 0 then λ _ => 0 else λ _ => 1 / n

/-- Create a decision problem with uniform prior -/
def withUniformPrior [Fintype W] [DecidableEq W] (utility : W -> A -> ℚ) : DecisionProblem W A where
  utility := utility
  prior := uniformPrior

end DecisionProblem

/-! ### Expected Utility -/

/-- Expected utility of action a given beliefs. -/
def expectedUtility {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (a : A) : ℚ :=
  ∑ w : W, dp.prior w * dp.utility w a

/-- Optimal action: the one with highest expected utility -/
def optimalAction {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A) : Option A :=
  actions.foldl (λ best a =>
    match best with
    | none => some a
    | some b => if expectedUtility dp a > expectedUtility dp b
                then some a else some b
  ) none

/-- Value of a decision problem: EU of optimal action -/
def dpValue {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A) : ℚ :=
  match optimalAction dp actions with
  | some a => expectedUtility dp a
  | none => 0

/-- Conditional expected utility of action a given cell membership. -/
def conditionalEU {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (cell : Finset W) (a : A) : ℚ :=
  let totalProb := cell.sum dp.prior
  if totalProb = 0 then 0
  else cell.sum (λ w => (dp.prior w / totalProb) * dp.utility w a)

/-- Value of decision problem after learning cell (best EU among actions) -/
def valueAfterLearning {W A : Type*} [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A) (cell : Finset W) : ℚ :=
  actions.foldl (λ best a =>
    max best (conditionalEU dp cell a)
  ) 0

/-- UV(C) = V(D|C) - V(D), the utility value of learning proposition C. -/
def utilityValue {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A) (cell : Finset W) : ℚ :=
  valueAfterLearning dp actions cell - dpValue dp actions

/-- Probability of a cell in the partition -/
def cellProbability {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (cell : Finset W) : ℚ :=
  cell.sum dp.prior

/-! ### Maximin -/

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

/-! ### Mention-Some / Mention-All -/

/-- Theory-neutral question type: a list of characteristic functions (cells). -/
abbrev Question (W : Type*) := List (W -> Bool)

/-- C resolves decision problem if some action dominates after learning C.

Per Van Rooy (2003, p.736): C resolves DP iff after learning C, there exists
an action a ∈ A that weakly dominates all other actions on every world in C. -/
def resolves {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c : W -> Bool) : Bool :=
  let cWorlds := worlds.filter c
  match actions with
  | [] => true
  | _ :: _ => actions.any λ a =>
    actions.all λ b =>
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

/-! ### Question Utility -/

/-- EUV(Q) = Sum_{q in Q} P(q) * UV(q), expected utility value of question Q.

Question-related functions bridge to the Finset world by converting
`cell : W → Bool` to `Finset.univ.filter (· = true)`. -/
def questionUtility {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (q : Question W) : ℚ :=
  q.foldl (λ acc cell =>
    let cellSet := Finset.univ.filter (fun w => cell w = true)
    let prob := cellProbability dp cellSet
    let uv := utilityValue dp actions cellSet
    acc + prob * uv
  ) 0

/-- Question utility is non-negative for partition-derived questions.

Requires non-negative priors. The general statement for arbitrary `Question W`
(which may not be a partition) is false — overlapping or non-covering cells
can produce incorrect utility decompositions. The QUD-specific version is
proved as `QUD.questionUtility_refinement_ge` applied with `q' = QUD.trivial`.

TODO: State and prove QUD-specific version in `Core.Partition`. -/
theorem questionUtility_nonneg {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (q : Question W)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    questionUtility dp actions q >= 0 := by
  sorry -- Needs: q is a partition + totalPrior ≤ 1, or QUD-specific statement

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

/-! ### Special Decision Problems -/

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

end Core.DecisionTheory
