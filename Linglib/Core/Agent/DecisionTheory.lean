import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Core Decision Theory
@cite{van-rooy-2003} @cite{blackwell-1953}

Theory-neutral decision-theoretic infrastructure: decision problems, expected
utility, maximin, and mention-some/mention-all classification.

Promoted from `Theories.Semantics.Questions.DecisionTheory` so that any module
(RSA, causal decision theory, explanation models) can use decision problems
without pulling in question-semantic types.

## Design: Fintype + Finset (Hybrid)

Functions that sum over the full universe use `[Fintype W]` with `∑ w : W`.
Functions that operate on subsets (conditioning, cells) take explicit `Finset W`
and use `Finset.sum`. Functions that iterate for argmax/min keep `List A`
(since `Finset.toList` is noncomputable in Mathlib).
Question-related types (`Question W = List (W → Bool)`) remain List-based.

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

Per @cite{van-rooy-2003}: C resolves DP iff after learning C, there exists
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

/-- MV(Q) = min_{q in Q} MV(q), maximin question value. -/
def questionMaximin {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) : ℚ :=
  match q with
  | [] => 0
  | c :: cs => cs.foldl (λ m cell =>
      min m (maximinUtilityValue dp worlds actions cell)
    ) (maximinUtilityValue dp worlds actions c)

/-! ### Value of Sample Information -/

/-- VSI(C) = V(D|C) - EU(a⁰|C): the value of sample information from
learning proposition C, where a⁰ is the current optimal action.

Unlike UV(C) = V(D|C) - V(D), VSI is always non-negative: learning C
before choosing can never hurt relative to the current best action
applied within C. @cite{van-rooy-2003}, p. 742. -/
def valueSampleInfo {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A) (cell : Finset W) : ℚ :=
  let bestAction := optimalAction dp actions
  let currentActionEU := match bestAction with
    | some a => conditionalEU dp cell a
    | none => 0
  valueAfterLearning dp actions cell - currentActionEU

/-- EVSI(Q) = Σ P(C) · VSI(C): the expected value of sample information
from asking question Q. @cite{van-rooy-2003}, p. 742. -/
def expectedVSI {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (q : Question W) : ℚ :=
  q.foldl (λ acc cell =>
    let cellSet := Finset.univ.filter (fun w => cell w = true)
    let prob := cellProbability dp cellSet
    let vsi := valueSampleInfo dp actions cellSet
    acc + prob * vsi
  ) 0

/-! #### EUV = EVSI helpers -/

private lemma foldl_add_shift' {α : Type*} (l : List α) (f : α → ℚ) (init : ℚ) :
    l.foldl (fun acc x => acc + f x) init = init + l.foldl (fun acc x => acc + f x) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih (init + f x), ih (f x)]; exact add_assoc _ _ _

private lemma foldl_add_eq_map_sum {α : Type*} (l : List α) (f : α → ℚ) :
    l.foldl (fun acc x => acc + f x) 0 = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, zero_add, List.map_cons, List.sum_cons]
    rw [foldl_add_shift' xs f (f x), ih]

private lemma list_map_sub_sum {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; linarith

private lemma list_sum_mul_const' {α : Type*} (l : List α) (f : α → ℚ) (k : ℚ) :
    (l.map (fun x => f x * k)).sum = k * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; linarith

private lemma per_cell_uv_sub_vsi {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A) (cell : W → Bool) :
    let cellSet := Finset.univ.filter (fun w => cell w = true)
    cellProbability dp cellSet * utilityValue dp actions cellSet -
    cellProbability dp cellSet * valueSampleInfo dp actions cellSet =
    cellProbability dp cellSet *
      ((match optimalAction dp actions with
        | some a => conditionalEU dp cellSet a
        | none => (0 : ℚ)) - dpValue dp actions) := by
  dsimp only []
  unfold utilityValue valueSampleInfo dpValue
  generalize optimalAction dp actions = oa
  generalize cellProbability dp (Finset.univ.filter (fun w => cell w = true)) = P
  generalize valueAfterLearning dp actions (Finset.univ.filter (fun w => cell w = true)) = V
  cases oa with
  | none => dsimp; ring
  | some a =>
    generalize conditionalEU dp (Finset.univ.filter (fun w => cell w = true)) a = C
    generalize expectedUtility dp a = E
    dsimp; ring

/-- EUV(Q) = EVSI(Q): the expected utility value of a question equals
its expected value of sample information.

@cite{van-rooy-2003}, p. 742: "The expected utility value of a question
is equal to its expected value of sample information."

The key identity `Σ P(C)·UV(C) = Σ P(C)·VSI(C)` follows from:

1. **Per-cell**: `P(C)·UV(C) - P(C)·VSI(C) = P(C)·(EU(a⁰|C) - V(D))`
2. **Summing**: the correction `Σ P(C)·EU(a⁰|C) - V(D)·Σ P(C) = EU(a⁰) - V(D) = 0`

The two hypotheses are the **law of total expectation** (`Σ P(C)·EU(a|C) = EU(a)`
for all actions) and **cell probability normalization** (`Σ P(C) = 1`). Both
follow from partition + non-negative prior + prior sums to 1 — see
`eu_eq_partitionEU` and `binary_cellProb_sum` in `Core.Partition`. -/
theorem euv_eq_evsi {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (q : Question W)
    (hLTE : ∀ a, (q.map (fun cell =>
      let cellSet := Finset.univ.filter (fun w => cell w = true)
      cellProbability dp cellSet * conditionalEU dp cellSet a)).sum =
      expectedUtility dp a)
    (hSum : (q.map (fun cell =>
      cellProbability dp (Finset.univ.filter (fun w => cell w = true)))).sum = 1) :
    questionUtility dp actions q = expectedVSI dp actions q := by
  -- Convert foldls to map+sum
  unfold questionUtility expectedVSI
  rw [foldl_add_eq_map_sum, foldl_add_eq_map_sum]
  -- Per-cell difference sums to 0
  suffices hdiff : (q.map (fun cell =>
      let cellSet := Finset.univ.filter (fun w => cell w = true)
      cellProbability dp cellSet * utilityValue dp actions cellSet -
      cellProbability dp cellSet * valueSampleInfo dp actions cellSet)).sum = 0 by
    rw [list_map_sub_sum] at hdiff; linarith
  -- Rewrite per-cell differences as P(C)·(EU(a*|C) - V(D))
  simp_rw [show ∀ cell : W → Bool,
    (fun cell => let cellSet := Finset.univ.filter (fun w => cell w = true)
      cellProbability dp cellSet * utilityValue dp actions cellSet -
      cellProbability dp cellSet * valueSampleInfo dp actions cellSet) cell =
    (fun cell => let cellSet := Finset.univ.filter (fun w => cell w = true)
      cellProbability dp cellSet *
        ((match optimalAction dp actions with
          | some a => conditionalEU dp cellSet a
          | none => (0 : ℚ)) - dpValue dp actions)) cell
    from fun cell => per_cell_uv_sub_vsi dp actions cell]
  -- Case split on optimalAction
  cases h : optimalAction dp actions with
  | none => unfold dpValue; rw [h]; simp
  | some a =>
    -- Σ P(C)·(EU(a|C) - EU(a)) = Σ P(C)·EU(a|C) - EU(a)·Σ P(C) = EU(a) - EU(a) = 0
    simp only [h, dpValue]
    simp_rw [show ∀ cell : W → Bool,
      (fun cell => let cellSet := Finset.univ.filter (fun w => cell w = true)
        cellProbability dp cellSet *
          (conditionalEU dp cellSet a - expectedUtility dp a)) cell =
      (fun cell => let cellSet := Finset.univ.filter (fun w => cell w = true)
        cellProbability dp cellSet * conditionalEU dp cellSet a -
        cellProbability dp cellSet * expectedUtility dp a) cell
      from fun cell => by dsimp; ring]
    rw [list_map_sub_sum]
    rw [list_sum_mul_const', hSum, mul_one]
    linarith [hLTE a]

/-! ### Maximin Monotonicity

Security level and maximin value are anti-monotone in the world set:
restricting to a subset can only improve worst-case guarantees.
These lemmas support the Blackwell maximin forward theorem. -/

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

/-- Security level is ≤ the utility of any world in the list. -/
theorem securityLevel_le_utility {W A : Type*}
    (dp : DecisionProblem W A) (worlds : List W) (a : A)
    {w : W} (hw : w ∈ worlds) :
    securityLevel dp worlds a ≤ dp.utility w a := by
  match worlds, hw with
  | _ :: ws, hmem =>
    simp only [securityLevel]
    rcases List.mem_cons.mp hmem with rfl | h
    · exact foldl_min_le_init _ _ _
    · exact foldl_min_le_of_mem _ _ _ h

/-- Security level on a subset ≥ security level on the superset.

min over fewer elements ≥ min over more elements. -/
theorem securityLevel_subset_ge {W A : Type*}
    (dp : DecisionProblem W A) (L₁ L₂ : List W) (a : A)
    (hne : L₁ ≠ []) (hsub : ∀ w ∈ L₁, w ∈ L₂) :
    securityLevel dp L₁ a ≥ securityLevel dp L₂ a := by
  match L₁, hne with
  | w :: ws, _ =>
    simp only [securityLevel, ge_iff_le]
    apply le_foldl_min
    · exact securityLevel_le_utility dp L₂ a (hsub w List.mem_cons_self)
    · intro w' hw'
      exact securityLevel_le_utility dp L₂ a (hsub w' (List.mem_cons_of_mem w hw'))

/-- foldl max is monotone in both the init and the function. -/
private lemma foldl_max_mono_fn {α : Type*} (f g : α → ℚ) (xs : List α)
    (init_f init_g : ℚ) (hinit : init_f ≥ init_g)
    (hfg : ∀ x ∈ xs, f x ≥ g x) :
    xs.foldl (λ m x => max m (f x)) init_f ≥
    xs.foldl (λ m x => max m (g x)) init_g := by
  induction xs generalizing init_f init_g with
  | nil => exact hinit
  | cons x xs ih =>
    apply ih
    · have hx : x ∈ x :: xs := List.mem_cons_self
      exact max_le_max hinit (hfg x hx)
    · intro y hy; exact hfg y (List.mem_cons_of_mem x hy)

/-- Maximin value on a subset ≥ maximin value on the superset.

Since `securityLevel` increases on subsets (fewer worst cases), `maximinValue`
(max over actions of security levels) also increases. -/
theorem maximinValue_subset_ge {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (L₁ L₂ : List W) (actions : List A)
    (hne : L₁ ≠ []) (hsub : ∀ w ∈ L₁, w ∈ L₂) :
    maximinValue dp L₁ actions ≥ maximinValue dp L₂ actions := by
  match actions with
  | [] => show maximinValue _ _ [] ≥ maximinValue _ _ []; simp [maximinValue]
  | a :: as =>
    simp only [maximinValue]
    exact foldl_max_mono_fn _ _ as _ _
      (securityLevel_subset_ge dp L₁ L₂ a hne hsub)
      (fun a' _ => securityLevel_subset_ge dp L₁ L₂ a' hne hsub)

/-- Maximin utility value is monotone under cell containment:
learning a more specific proposition (subset of worlds) gives higher MUV. -/
theorem maximinUtilityValue_monotone_cell {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c1 c2 : W → Bool) (hSub : ∀ w, c1 w = true → c2 w = true)
    (hNe : worlds.filter c1 ≠ []) :
    maximinUtilityValue dp worlds actions c1 ≥
    maximinUtilityValue dp worlds actions c2 := by
  unfold maximinUtilityValue maximinAfterLearning
  have hFilterSub : ∀ w ∈ worlds.filter c1, w ∈ worlds.filter c2 := by
    intro w hw; simp only [List.mem_filter] at hw ⊢; exact ⟨hw.1, hSub w hw.2⟩
  linarith [maximinValue_subset_ge dp (worlds.filter c1) (worlds.filter c2)
    actions hNe hFilterSub]

/-- Maximin value of information is non-negative for nonempty cells.

When the cell is nonempty, `worlds.filter c ⊆ worlds`, and the maximin over a
subset considers fewer worst cases, so `maximinAfterLearning ≥ maximinValue`. -/
theorem maximinUtilityValue_nonneg {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (c : W -> Bool)
    (hNonempty : ∃ w ∈ worlds, c w = true) :
    maximinUtilityValue dp worlds actions c >= 0 := by
  unfold maximinUtilityValue maximinAfterLearning
  have hne : worlds.filter c ≠ [] := by
    obtain ⟨w, hw, hc⟩ := hNonempty
    exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hw, hc⟩)
  have hsub : ∀ w ∈ worlds.filter c, w ∈ worlds :=
    fun w hw => (List.mem_filter.mp hw).1
  linarith [maximinValue_subset_ge dp (worlds.filter c) worlds actions hne hsub]

/-- The question maximin value is ≤ MUV of each cell in the question. -/
theorem questionMaximin_le_muv {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (q : Question W) (cell : W → Bool) (hcell : cell ∈ q) :
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

/-- **Binary question value decomposition**: for a binary partition [P, ¬P],

        Σ P(cell) · V(D|cell) = EUV([P,¬P], D) + V(D)

    where the LHS is the probability-weighted sum of conditional DP values,
    EUV is `questionUtility`, and V(D) is `dpValue`.

    This is the fundamental algebraic identity connecting the expected value
    of asking a polar question to @cite{van-rooy-2003}'s question utility
    framework. It holds for any decision problem with a proper prior. -/
theorem binary_question_value_decomposition
    {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A) (P : W → Bool)
    (hPrior : Finset.univ.sum dp.prior = 1) :
    let yesCell := Finset.univ.filter (fun w => P w = true)
    let noCell := Finset.univ.filter (fun w => (!P w) = true)
    cellProbability dp yesCell * valueAfterLearning dp actions yesCell +
    cellProbability dp noCell * valueAfterLearning dp actions noCell =
    questionUtility dp actions [P, fun w => !P w] + dpValue dp actions := by
  have hSum := binary_cellProb_sum dp P hPrior
  simp only [questionUtility, utilityValue, List.foldl]
  have key : cellProbability dp (Finset.univ.filter (fun w => P w = true)) *
               dpValue dp actions +
             cellProbability dp (Finset.univ.filter (fun w => (!P w) = true)) *
               dpValue dp actions = dpValue dp actions := by
    rw [← add_mul, hSum, one_mul]
  linarith

/-! ### Answer and Question Orderings

@cite{van-rooy-2003}'s relevance-based orderings on answers and questions. -/

/-- C >_Q D: answer C is strictly more relevant than D given question Q.

@cite{van-rooy-2003}, p. 737: C >_Q D iff either
(i) C_Q ⊂ D_Q (C partitions into strictly fewer equivalence classes), or
(ii) C_Q = D_Q and C ⊃ D (same partition but C is logically stronger).

We formalize criterion (i) via utility: C is more relevant than D for
some DP, while D is never more relevant than C. -/
def moreRelevantAnswer {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (c d : Finset W) : Bool :=
  -- C has strictly higher utility value than D
  utilityValue dp actions c > utilityValue dp actions d

/-- Q > Q': question Q is strictly better than Q'.

@cite{van-rooy-2003}, p. 743: Q > Q' iff either
(i) EUV(Q) > EUV(Q'), or
(ii) EUV(Q) = EUV(Q') and Q ⊐ Q' (Q is strictly finer). -/
def betterQuestion {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (q q' : Question W) : Bool :=
  questionUtility dp actions q > questionUtility dp actions q'

end Core.DecisionTheory
