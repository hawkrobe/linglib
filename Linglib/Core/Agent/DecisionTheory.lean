import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Linglib.Core.Question.Relevance

/-!
# Core Decision Theory
@cite{van-rooy-2003} @cite{blackwell-1953}

Theory-neutral decision-theoretic infrastructure: decision problems, expected
utility, maximin, and mention-some/mention-all classification.

Promoted from `Theories.Semantics.Questions.DecisionTheory` so that any module
(RSA, causal decision theory, explanation models) can use decision problems
without pulling in question-semantic types.

## Design: Fintype + Finset

Functions that sum over the full universe use `[Fintype W]` with `∑ w : W`.
Functions that operate over action sets or world subsets use `Finset`.
`questionUtility` and `expectedVSI` take `Finset (Finset W)` (cells as sets).
Ordering-sensitive operations (`questionMaximin`, `isMentionSome`,
`resolvingAnswers`, …) take a `List (Finset W)` of cells.

- @cite{van-rooy-2003}. Questioning to Resolve Decision Problems. L&P 26.
- @cite{blackwell-1953}. Equivalent Comparisons of Experiments.
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

/-- Value of a decision problem: max EU over actions, or 0 if empty. -/
def dpValue {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (actions : Finset A) : ℚ :=
  if h : actions.Nonempty then actions.sup' h (expectedUtility dp) else 0

/-- Conditional expected utility of action a given cell membership. -/
def conditionalEU {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (cell : Finset W) (a : A) : ℚ :=
  let totalProb := cell.sum dp.prior
  if totalProb = 0 then 0
  else cell.sum (λ w => (dp.prior w / totalProb) * dp.utility w a)

/-- Value of decision problem after learning cell (best EU among actions) -/
def valueAfterLearning {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (actions : Finset A) (cell : Finset W) : ℚ :=
  if h : actions.Nonempty then actions.sup' h (conditionalEU dp cell) else 0

/-- UV(C) = V(D|C) - V(D), the utility value of learning proposition C. -/
def utilityValue {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (actions : Finset A) (cell : Finset W) : ℚ :=
  valueAfterLearning dp actions cell - dpValue dp actions

/-- Probability of a cell in the partition -/
def cellProbability {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (cell : Finset W) : ℚ :=
  cell.sum dp.prior

/-! ### Maximin -/

/-- S(a) = min_w U(w, a), security level of action a. -/
def securityLevel {W A : Type*} (dp : DecisionProblem W A) (worlds : Finset W) (a : A) : ℚ :=
  if h : worlds.Nonempty then worlds.inf' h (fun w => dp.utility w a) else 0

/-- MV = max_a min_w U(w, a), maximin value. -/
def maximinValue {W A : Type*}
    (dp : DecisionProblem W A) (worlds : Finset W) (actions : Finset A) : ℚ :=
  if h : actions.Nonempty then actions.sup' h (fun a => securityLevel dp worlds a) else 0

/-- Conditional security level: worst case within cell C -/
def conditionalSecurityLevel {W A : Type*} [DecidableEq W] (dp : DecisionProblem W A)
    (worlds : Finset W) (a : A) (c : Finset W) : ℚ :=
  securityLevel dp (worlds ∩ c) a

/-- Maximin value after learning C -/
def maximinAfterLearning {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (worlds : Finset W) (actions : Finset A)
    (c : Finset W) : ℚ :=
  maximinValue dp (worlds ∩ c) actions

/-- Maximin utility value of learning C -/
def maximinUtilityValue {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (worlds : Finset W) (actions : Finset A)
    (c : Finset W) : ℚ :=
  maximinAfterLearning dp worlds actions c - maximinValue dp worlds actions

/-! ### Resolution

@cite{van-rooy-2003} p. 736 resolution definition: information `c`
**resolves** decision problem `(dp, acts)` iff some action in `acts`
weakly dominates every other action on every world in `c`. -/

/-- `c` **resolves** decision problem `(dp, acts)`: some action in `acts`
    weakly dominates every other action on every world in `c`.
    @cite{van-rooy-2003} p. 736. -/
def IsResolved {W A : Type*} (dp : DecisionProblem W A)
    (acts : Set A) (c : Set W) : Prop :=
  ∃ a ∈ acts, ∀ b ∈ acts, ∀ w ∈ c, dp.utility w a ≥ dp.utility w b

/-- Decidability of `IsResolved` under finite, decidable carriers. The
    consumer-side prerequisite for `decide`-based evaluation (e.g.,
    `List.filter` over candidate cells in worked study examples). -/
instance IsResolved.instDecidable {W A : Type*}
    (dp : DecisionProblem W A) (acts : Set A) (c : Set W)
    [Fintype A] [DecidablePred (· ∈ acts)]
    [Fintype W] [DecidablePred (· ∈ c)] :
    Decidable (IsResolved dp acts c) := by
  unfold IsResolved; infer_instance

/-! ### Question Utility -/

/-- EUV(Q) = Sum_{q in Q} P(q) * UV(q), expected utility value of question Q. -/
def questionUtility {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : Finset A)
    (cells : Finset (Finset W)) : ℚ :=
  cells.sum (fun cell =>
    cellProbability dp cell * utilityValue dp actions cell)

/-- MV(Q) = min_{q in Q} MV(q), maximin question value. -/
def questionMaximin {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (worlds : Finset W) (actions : Finset A)
    (q : List (Finset W)) : ℚ :=
  match q with
  | [] => 0
  | c :: cs => cs.foldl (λ m cell =>
      min m (maximinUtilityValue dp worlds actions cell)
    ) (maximinUtilityValue dp worlds actions c)

/-! ### Value of Sample Information -/

/-- Optimal action: the one with highest expected utility.

Noncomputable because it extracts a witness from an existential
(`Finset.exists_max_image` via `Classical.choice`). -/
noncomputable def optimalAction {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (actions : Finset A) : Option A :=
  if h : actions.Nonempty then
    some (Finset.exists_max_image actions (expectedUtility dp) h).choose
  else none

/-- VSI(C) = V(D|C) - EU(a⁰|C): the value of sample information from
learning proposition C, where a⁰ is the current optimal action.

Unlike UV(C) = V(D|C) - V(D), VSI is always non-negative: learning C
before choosing can never hurt relative to the current best action
applied within C. @cite{van-rooy-2003}, p. 742. -/
noncomputable def valueSampleInfo {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (actions : Finset A) (cell : Finset W) : ℚ :=
  let bestAction := optimalAction dp actions
  let currentActionEU := match bestAction with
    | some a => conditionalEU dp cell a
    | none => 0
  valueAfterLearning dp actions cell - currentActionEU

/-- EVSI(Q) = Σ P(C) · VSI(C): the expected value of sample information
from asking question Q. @cite{van-rooy-2003}, p. 742. -/
noncomputable def expectedVSI {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (actions : Finset A)
    (cells : Finset (Finset W)) : ℚ :=
  cells.sum (fun cell =>
    cellProbability dp cell * valueSampleInfo dp actions cell)

/-! #### EUV = EVSI -/

private lemma optimalAction_eu_eq_dpValue {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (actions : Finset A) :
    (match optimalAction dp actions with
     | some a => expectedUtility dp a
     | none => (0 : ℚ)) = dpValue dp actions := by
  unfold optimalAction dpValue
  by_cases hne : actions.Nonempty
  · rw [dif_pos hne, dif_pos hne]; simp only []
    have hspec := (Finset.exists_max_image actions (expectedUtility dp) hne).choose_spec
    exact le_antisymm (Finset.le_sup' _ hspec.1)
      (Finset.sup'_le hne _ fun a ha => hspec.2 a ha)
  · rw [dif_neg hne, dif_neg hne]

/-- EUV(Q) = EVSI(Q): the expected utility value of a question equals
its expected value of sample information.

@cite{van-rooy-2003}, p. 742: "The expected utility value of a question
is equal to its expected value of sample information."

The two hypotheses are the **law of total expectation** (`Σ P(C)·EU(a|C) = EU(a)`
for all actions) and **cell probability normalization** (`Σ P(C) = 1`). -/
theorem euv_eq_evsi {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : Finset A)
    (cells : Finset (Finset W))
    (hLTE : ∀ a, cells.sum (fun cell =>
      cellProbability dp cell * conditionalEU dp cell a) =
      expectedUtility dp a)
    (hSum : cells.sum (fun cell => cellProbability dp cell) = 1) :
    questionUtility dp actions cells = expectedVSI dp actions cells := by
  set S := cells.sum (fun cell =>
      cellProbability dp cell * valueAfterLearning dp actions cell)
  have hLHS : questionUtility dp actions cells = S - dpValue dp actions := by
    unfold questionUtility; simp only [utilityValue]; simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1; rw [← Finset.sum_mul, hSum, one_mul]
  have hRHS : expectedVSI dp actions cells = S - dpValue dp actions := by
    unfold expectedVSI; dsimp only [valueSampleInfo]; simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1; rw [← optimalAction_eu_eq_dpValue dp actions]
    generalize optimalAction dp actions = oa
    cases oa with
    | none => simp
    | some a => exact hLTE a
  rw [hLHS, hRHS]

/-! ### Maximin Monotonicity

Security level and maximin value are anti-monotone in the world set:
restricting to a subset can only improve worst-case guarantees.
These lemmas support the Blackwell maximin forward theorem. -/

/-- Security level is ≤ the utility of any world in the finset. -/
theorem securityLevel_le_utility {W A : Type*}
    (dp : DecisionProblem W A) (worlds : Finset W) (a : A)
    {w : W} (hw : w ∈ worlds) :
    securityLevel dp worlds a ≤ dp.utility w a := by
  have hne : worlds.Nonempty := ⟨w, hw⟩
  show securityLevel dp worlds a ≤ dp.utility w a
  unfold securityLevel; rw [dif_pos hne]
  exact Finset.inf'_le _ hw

/-- Security level on a subset ≥ security level on the superset.

min over fewer elements ≥ min over more elements. -/
theorem securityLevel_subset_ge {W A : Type*}
    (dp : DecisionProblem W A) (S₁ S₂ : Finset W) (a : A)
    (hne : S₁.Nonempty) (hsub : S₁ ⊆ S₂) :
    securityLevel dp S₁ a ≥ securityLevel dp S₂ a := by
  show securityLevel dp S₂ a ≤ securityLevel dp S₁ a
  unfold securityLevel; rw [dif_pos hne, dif_pos (hne.mono hsub)]
  exact Finset.inf'_mono _ hsub hne

/-- Maximin value on a subset ≥ maximin value on the superset.

Since `securityLevel` increases on subsets (fewer worst cases), `maximinValue`
(max over actions of security levels) also increases. -/
theorem maximinValue_subset_ge {W A : Type*}
    (dp : DecisionProblem W A) (S₁ S₂ : Finset W) (actions : Finset A)
    (hne : S₁.Nonempty) (hsub : S₁ ⊆ S₂) :
    maximinValue dp S₁ actions ≥ maximinValue dp S₂ actions := by
  unfold maximinValue
  by_cases ha : actions.Nonempty
  · show maximinValue dp S₂ actions ≤ maximinValue dp S₁ actions
    unfold maximinValue; rw [dif_pos ha, dif_pos ha]
    exact Finset.sup'_mono_fun fun a _ =>
      securityLevel_subset_ge dp S₁ S₂ a hne hsub
  · show maximinValue dp S₂ actions ≤ maximinValue dp S₁ actions
    unfold maximinValue; rw [dif_neg ha, dif_neg ha]

/-- Maximin utility value is monotone under cell containment:
learning a more specific proposition (subset of worlds) gives higher MUV. -/
theorem maximinUtilityValue_monotone_cell {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (worlds : Finset W) (actions : Finset A)
    (c1 c2 : Finset W) (hSub : c1 ⊆ c2)
    (hNe : (worlds ∩ c1).Nonempty) :
    maximinUtilityValue dp worlds actions c1 ≥
    maximinUtilityValue dp worlds actions c2 := by
  unfold maximinUtilityValue maximinAfterLearning
  have hFilterSub : worlds ∩ c1 ⊆ worlds ∩ c2 :=
    Finset.inter_subset_inter_left hSub
  linarith [maximinValue_subset_ge dp (worlds ∩ c1) (worlds ∩ c2) actions hNe hFilterSub]

/-- Maximin value of information is non-negative for nonempty cells.

When the cell is nonempty, `worlds ∩ c ⊆ worlds`, and the maximin over a
subset considers fewer worst cases, so `maximinAfterLearning ≥ maximinValue`. -/
theorem maximinUtilityValue_nonneg {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (worlds : Finset W) (actions : Finset A)
    (c : Finset W)
    (hNonempty : (worlds ∩ c).Nonempty) :
    maximinUtilityValue dp worlds actions c >= 0 := by
  unfold maximinUtilityValue maximinAfterLearning
  have hsub : worlds ∩ c ⊆ worlds := Finset.inter_subset_left
  linarith [maximinValue_subset_ge dp (worlds ∩ c) worlds actions hNonempty hsub]

-- ── List helpers for Question (List-based) iteration ────────────────

/-- A lower bound of all values is ≤ foldl min. -/
theorem le_foldl_min {α : Type*} (f : α → ℚ) (xs : List α) (init b : ℚ)
    (hinit : b ≤ init) (hxs : ∀ x ∈ xs, b ≤ f x) :
    b ≤ xs.foldl (λ m x => min m (f x)) init := by
  induction xs generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
    apply ih (min init (f x))
    · exact le_min hinit (hxs x List.mem_cons_self)
    · intro y hy; exact hxs y (List.mem_cons_of_mem x hy)

/-- foldl min is ≤ the initial value. -/
private lemma foldl_min_le_init {α : Type*} (f : α → ℚ) (xs : List α) (init : ℚ) :
    xs.foldl (λ m x => min m (f x)) init ≤ init := by
  induction xs generalizing init with
  | nil => exact le_refl _
  | cons x xs ih => exact le_trans (ih _) (min_le_left _ _)

/-- foldl min is ≤ f(x) for any x in the list. -/
private lemma foldl_min_le_of_mem {α : Type*} (f : α → ℚ) (xs : List α) (init : ℚ)
    {x : α} (hx : x ∈ xs) :
    xs.foldl (λ m x => min m (f x)) init ≤ f x := by
  induction xs generalizing init with
  | nil => exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · show ys.foldl (fun m z => min m (f z)) (min init (f x)) ≤ f x
      exact le_trans (foldl_min_le_init _ _ _) (min_le_right _ _)
    · show ys.foldl (fun m z => min m (f z)) (min init (f y)) ≤ f x
      exact ih _ h

/-- The question maximin value is ≤ MUV of each cell in the question. -/
theorem questionMaximin_le_muv {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (worlds : Finset W) (actions : Finset A)
    (q : List (Finset W)) (cell : Finset W) (hcell : cell ∈ q) :
    questionMaximin dp worlds actions q ≤
    maximinUtilityValue dp worlds actions cell := by
  cases q with
  | nil => exact absurd hcell List.not_mem_nil
  | cons c cs =>
    simp only [questionMaximin]
    rcases List.mem_cons.mp hcell with rfl | h
    · exact foldl_min_le_init _ _ _
    · exact foldl_min_le_of_mem _ _ _ h

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

/-! ### Binary Question Value Decomposition

For a binary partition [P, ¬P], the probability-weighted sum of conditional
DP values equals Van Rooy's question utility plus the baseline DP value.
This is the structural identity connecting "the value of asking a yes/no
question" to the decision-theoretic question framework of @cite{van-rooy-2003}. -/

/-- Cell probabilities of a binary partition [P, ¬P] sum to 1
    when the prior is a proper distribution. -/
theorem binary_cellProb_sum
    {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (P : W → Bool)
    (hPrior : Finset.univ.sum dp.prior = 1) :
    cellProbability dp (Finset.univ.filter (fun w => P w = true)) +
    cellProbability dp (Finset.univ.filter (fun w => (!P w) = true)) = 1 := by
  simp only [cellProbability]
  have hDisj : Disjoint
      (Finset.univ.filter (fun w => P w = true))
      (Finset.univ.filter (fun w => (!P w) = true)) := by
    rw [Finset.disjoint_filter]; intro w _ h1 h2; cases P w <;> simp_all
  have hCover : Finset.univ.filter (fun w => P w = true) ∪
                Finset.univ.filter (fun w => (!P w) = true) = Finset.univ := by
    ext w; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases P w <;> simp
  calc (Finset.univ.filter (fun w => P w = true)).sum dp.prior +
       (Finset.univ.filter (fun w => (!P w) = true)).sum dp.prior
      = (Finset.univ.filter (fun w => P w = true) ∪
         Finset.univ.filter (fun w => (!P w) = true)).sum dp.prior :=
          (Finset.sum_union hDisj).symm
    _ = Finset.univ.sum dp.prior := by rw [hCover]
    _ = 1 := hPrior

/-- **Binary question value decomposition**: for a binary partition {P, ¬P},

        Σ P(cell) · V(D|cell) = EUV({P,¬P}, D) + V(D)

    where the LHS is the probability-weighted sum of conditional DP values,
    EUV is `questionUtility`, and V(D) is `dpValue`. -/
theorem binary_question_value_decomposition
    {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : Finset A) (P : W → Bool)
    (hPrior : Finset.univ.sum dp.prior = 1) :
    let yesCell := Finset.univ.filter (fun w => P w = true)
    let noCell := Finset.univ.filter (fun w => (!P w) = true)
    cellProbability dp yesCell * valueAfterLearning dp actions yesCell +
    cellProbability dp noCell * valueAfterLearning dp actions noCell =
    questionUtility dp actions {yesCell, noCell} + dpValue dp actions := by
  have hSum := binary_cellProb_sum dp P hPrior
  -- W must be nonempty (from hPrior: 0 ≠ 1)
  have ⟨w₀⟩ : Nonempty W := by
    by_contra h; rw [not_nonempty_iff] at h; simp [Finset.univ_eq_empty] at hPrior
  have hne : Finset.univ.filter (fun w => P w = true) ≠
             Finset.univ.filter (fun w => (!P w) = true) := by
    intro heq
    cases hp : P w₀ with
    | false =>
      have : w₀ ∈ Finset.univ.filter (fun w => (!P w) = true) := by
        simp [Finset.mem_filter, hp]
      rw [← heq] at this; simp [Finset.mem_filter, hp] at this
    | true =>
      have : w₀ ∈ Finset.univ.filter (fun w => P w = true) := by
        simp [Finset.mem_filter, hp]
      rw [heq] at this; simp [Finset.mem_filter, hp] at this
  simp only [questionUtility, utilityValue, Finset.sum_pair hne]
  linarith [show cellProbability dp (Finset.univ.filter (fun w => P w = true)) *
               dpValue dp actions +
             cellProbability dp (Finset.univ.filter (fun w => (!P w) = true)) *
               dpValue dp actions = dpValue dp actions from by
    rw [← add_mul, hSum, one_mul]]

/-! ### Answer and Question Orderings

@cite{van-rooy-2003}'s relevance-based orderings on answers and questions. -/

/-- C >_Q D: answer C is strictly more relevant than D given question Q. -/
def moreRelevantAnswer {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : Finset A)
    (c d : Finset W) : Bool :=
  utilityValue dp actions c > utilityValue dp actions d

/-- Q > Q': question Q is strictly better than Q'. -/
def betterQuestion {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : Finset A)
    (q q' : Finset (Finset W)) : Bool :=
  questionUtility dp actions q > questionUtility dp actions q'

end Core.DecisionTheory
