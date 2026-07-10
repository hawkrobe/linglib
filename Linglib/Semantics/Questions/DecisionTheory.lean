import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Core Decision Theory
[van-rooy-2003] [blackwell-1953]

Theory-neutral decision-theoretic infrastructure: decision problems, expected
utility, maximin, and mention-some/mention-all classification. No
question-semantic imports: any module (RSA, causal decision theory,
explanation models) can use decision problems without pulling in the
`Question` cone.

## Design: Fintype + Finset

Functions that sum over the full universe use `[Fintype W]` with `∑ w : W`.
Functions that operate over action sets or world subsets use `Finset`.
`questionUtility` and `expectedVSI` take `Finset (Finset W)` (cells as sets).
Ordering-sensitive operations (`questionMaximin`, `isMentionSome`,
`resolvingAnswers`, …) take a `List (Finset W)` of cells.

- [van-rooy-2003]. Questioning to Resolve Decision Problems. L&P 26.
- [blackwell-1953]. Equivalent Comparisons of Experiments.
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

[van-rooy-2003] p. 736 resolution definition: information `c`
**resolves** decision problem `(dp, acts)` iff some action in `acts`
weakly dominates every other action on every world in `c`. -/

/-- `c` **resolves** decision problem `(dp, acts)`: some action in `acts`
    weakly dominates every other action on every world in `c`.
    [van-rooy-2003] p. 736. -/
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
applied within C. [van-rooy-2003], p. 742. -/
noncomputable def valueSampleInfo {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (actions : Finset A) (cell : Finset W) : ℚ :=
  let bestAction := optimalAction dp actions
  let currentActionEU := match bestAction with
    | some a => conditionalEU dp cell a
    | none => 0
  valueAfterLearning dp actions cell - currentActionEU

/-- EVSI(Q) = Σ P(C) · VSI(C): the expected value of sample information
from asking question Q. [van-rooy-2003], p. 742. -/
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

[van-rooy-2003], p. 742: "The expected utility value of a question
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

/-! ### Refinement monotonicity (Blackwell forward direction / [van-rooy-2003] §4.1)

[van-rooy-2003] p. 743 states that `Q ⊑ Q' ↔ ∀ DP, EUV(Q) ≥ EUV(Q')` is "a special
case of [blackwell-1953]". The `⟹` ("only if") direction is the data-processing /
Jensen inequality: a *finer* question can only raise question utility. We prove it
directly at the `questionUtility` level.

The mathematical core is the **unnormalized cell value** `maxₐ ∑_{w∈c} P(w)·U(w,a)`,
which equals `P(c)·V(D|c)` (`cellProb_mul_valueAfterLearning_eq_uValue`) and is
**superadditive** under splitting a cell into disjoint pieces
(`uValue_union_le`): the max of a sum is at most the sum of the maxes. Summed over a
partition, this gives `questionUtility (finer) ≥ questionUtility (coarser)`. -/

/-- The **unnormalized cell value** of `cell`: the best, over actions, of the
*unnormalized* expected utility `∑_{w∈cell} P(w)·U(w,a)`. This linearizes the
probability-weighted conditional value `P(cell)·V(D|cell)` (see
`cellProb_mul_valueAfterLearning_eq_uValue`), turning Van Rooy's question utility into
a sum that splitting a cell can only increase. -/
private def uValue {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (acts : Finset A) (cell : Finset W) : ℚ :=
  if h : acts.Nonempty then
    acts.sup' h (fun a => ∑ w ∈ cell, dp.prior w * dp.utility w a)
  else 0

/-- `P(cell)·V(D|cell) = maxₐ ∑_{w∈cell} P(w)·U(w,a)`: the probability-weighted
conditional value equals the unnormalized cell value. The normalizing `1/P(cell)` in
`conditionalEU` cancels against the `P(cell)` weight; when `P(cell) = 0`, a nonnegative
prior forces every `P(w) = 0` on the cell, so both sides vanish. -/
private lemma cellProb_mul_valueAfterLearning_eq_uValue {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (acts : Finset A) (cell : Finset W)
    (hprior : ∀ w, 0 ≤ dp.prior w) :
    cellProbability dp cell * valueAfterLearning dp acts cell = uValue dp acts cell := by
  unfold uValue valueAfterLearning
  by_cases hne : acts.Nonempty
  · rw [dif_pos hne, dif_pos hne]
    have htp_nonneg : 0 ≤ cellProbability dp cell :=
      Finset.sum_nonneg (fun w _ => hprior w)
    by_cases htp : cellProbability dp cell = 0
    · rw [htp, zero_mul]
      have hpw : ∀ w ∈ cell, dp.prior w = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hprior w)).mp htp
      have hz : ∀ a ∈ acts, (∑ w ∈ cell, dp.prior w * dp.utility w a) = 0 := by
        intro a _; exact Finset.sum_eq_zero (fun w hw => by rw [hpw w hw, zero_mul])
      rw [Finset.sup'_congr hne rfl hz, Finset.sup'_const]
    · rw [Finset.mul₀_sup' htp_nonneg (conditionalEU dp cell) acts hne]
      refine Finset.sup'_congr hne rfl (fun a _ => ?_)
      have htp' : cell.sum dp.prior ≠ 0 := htp
      have hcEU : conditionalEU dp cell a
          = cell.sum (fun w => dp.prior w / cell.sum dp.prior * dp.utility w a) := by
        show (if cell.sum dp.prior = 0 then (0 : ℚ) else
              cell.sum (fun w => dp.prior w / cell.sum dp.prior * dp.utility w a)) = _
        rw [if_neg htp']
      show cell.sum dp.prior * conditionalEU dp cell a
          = ∑ w ∈ cell, dp.prior w * dp.utility w a
      rw [hcEU, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_div_cancel_left₀ _ htp']
  · rw [dif_neg hne, dif_neg hne, mul_zero]

/-- **Superadditivity of unnormalized cell value under splitting**: when `cell` is the
disjoint union of `c₁` and `c₂`, splitting it can only raise the best-action value,
`uValue (c₁ ∪ c₂) ≤ uValue c₁ + uValue c₂` (max of a sum ≤ sum of maxes). This is the
combinatorial heart of [blackwell-1953]'s forward direction. -/
private lemma uValue_union_le {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (acts : Finset A) {c₁ c₂ : Finset W}
    (hdisj : Disjoint c₁ c₂) :
    uValue dp acts (c₁ ∪ c₂) ≤ uValue dp acts c₁ + uValue dp acts c₂ := by
  unfold uValue
  by_cases hne : acts.Nonempty
  · rw [dif_pos hne, dif_pos hne, dif_pos hne]
    refine Finset.sup'_le hne _ (fun a ha => ?_)
    rw [Finset.sum_union hdisj]
    exact add_le_add (Finset.le_sup' (fun a => ∑ w ∈ c₁, dp.prior w * dp.utility w a) ha)
      (Finset.le_sup' (fun a => ∑ w ∈ c₂, dp.prior w * dp.utility w a) ha)
  · rw [dif_neg hne, dif_neg hne, dif_neg hne, add_zero]

/-- **Splitting a cell never decreases its decision value**: for disjoint cells `c₁`, `c₂`
and a nonnegative prior,
`P(c₁)·V(D|c₁) + P(c₂)·V(D|c₂) ≥ P(c₁ ∪ c₂)·V(D|c₁ ∪ c₂)`.
This is [blackwell-1953]'s data-processing inequality for a single binary refinement, the
building block of [van-rooy-2003]'s §4.1 question-utility monotonicity (p. 743). -/
theorem cellProb_valueAfterLearning_split_ge {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (acts : Finset A) {c₁ c₂ : Finset W}
    (hdisj : Disjoint c₁ c₂) (hprior : ∀ w, 0 ≤ dp.prior w) :
    cellProbability dp (c₁ ∪ c₂) * valueAfterLearning dp acts (c₁ ∪ c₂) ≤
    cellProbability dp c₁ * valueAfterLearning dp acts c₁ +
    cellProbability dp c₂ * valueAfterLearning dp acts c₂ := by
  rw [cellProb_mul_valueAfterLearning_eq_uValue dp acts _ hprior,
    cellProb_mul_valueAfterLearning_eq_uValue dp acts _ hprior,
    cellProb_mul_valueAfterLearning_eq_uValue dp acts _ hprior]
  exact uValue_union_le dp acts hdisj

/-- **Question utility rises under refinement (binary split)** — the `⟹` ("only if")
direction of [van-rooy-2003]'s §4.1 Fact (p. 743), in its elementary case. Splitting one
cell `c₁ ∪ c₂` of a question into the two disjoint cells `c₁`, `c₂` can only increase the
expected utility value `EUV`. This is the finite-partition instance of [blackwell-1953]'s
data-processing inequality; any finite refinement of one partition by another is a
composition of such binary splits, so iterating gives the full §4.1 monotonicity. -/
theorem questionUtility_split_ge {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (acts : Finset A)
    {c₁ c₂ : Finset W} (rest : Finset (Finset W))
    (hdisj : Disjoint c₁ c₂) (hprior : ∀ w, 0 ≤ dp.prior w)
    (hc₁ : c₁ ∉ rest) (hc₂ : c₂ ∉ rest) (hne12 : c₁ ≠ c₂) (hcrest : c₁ ∪ c₂ ∉ rest) :
    questionUtility dp acts (insert (c₁ ∪ c₂) rest) ≤
    questionUtility dp acts (insert c₁ (insert c₂ rest)) := by
  have hc₁' : c₁ ∉ insert c₂ rest := by
    simp only [Finset.mem_insert, not_or]; exact ⟨hne12, hc₁⟩
  have hcp : cellProbability dp (c₁ ∪ c₂)
      = cellProbability dp c₁ + cellProbability dp c₂ := Finset.sum_union hdisj
  have hcpd : cellProbability dp (c₁ ∪ c₂) * dpValue dp acts
      = cellProbability dp c₁ * dpValue dp acts
        + cellProbability dp c₂ * dpValue dp acts := by rw [hcp]; ring
  have hsplit := cellProb_valueAfterLearning_split_ge dp acts hdisj hprior
  unfold questionUtility
  rw [Finset.sum_insert hcrest, Finset.sum_insert hc₁', Finset.sum_insert hc₂]
  simp only [utilityValue, mul_sub]
  linarith [hsplit, hcpd]

/-! #### General partition refinement

The binary `questionUtility_split_ge` lifts to an arbitrary refinement of one partition by
another, via general superadditivity of `uValue` and a fiberwise regrouping. The refinement
is presented by a map `assign` sending each finer cell to the coarser cell containing it,
with each coarser cell the union (`Finset.sup`) of its fiber. -/

private lemma uValue_empty {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (acts : Finset A) : uValue dp acts ∅ = 0 := by
  unfold uValue
  by_cases h : acts.Nonempty
  · rw [dif_pos h]; simp only [Finset.sum_empty, Finset.sup'_const]
  · rw [dif_neg h]

/-- **General superadditivity of `uValue`**: splitting a union of pairwise-disjoint cells
into its pieces never lowers the best-action value, `uValue (⨆ parts) ≤ ∑ uValue`. The
`Finset.induction` engine for the refinement monotonicity below. -/
private lemma uValue_sup_le {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) (acts : Finset A) :
    ∀ {parts : Finset (Finset W)},
      (∀ p₁ ∈ parts, ∀ p₂ ∈ parts, p₁ ≠ p₂ → Disjoint p₁ p₂) →
      uValue dp acts (parts.sup id) ≤ ∑ p ∈ parts, uValue dp acts p := by
  intro parts
  induction parts using Finset.induction with
  | empty => intro _; simp [uValue_empty]
  | insert p s hp ih =>
    intro hdisj
    have hsub : ∀ p₁ ∈ s, ∀ p₂ ∈ s, p₁ ≠ p₂ → Disjoint p₁ p₂ :=
      fun a ha b hb hab =>
        hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hdp : Disjoint p (s.sup id) :=
      Finset.disjoint_sup_right.mpr fun q hq =>
        hdisj p (Finset.mem_insert_self p s) q (Finset.mem_insert_of_mem hq)
          (fun h => hp (h ▸ hq))
    rw [Finset.sup_insert, Finset.sum_insert hp, id_eq]
    calc uValue dp acts (p ⊔ s.sup id)
        ≤ uValue dp acts p + uValue dp acts (s.sup id) := uValue_union_le dp acts hdp
      _ ≤ uValue dp acts p + ∑ q ∈ s, uValue dp acts q := by linarith [ih hsub]

/-- Cell probability is additive over a union of pairwise-disjoint cells. -/
private lemma cellProb_sup {W A : Type*} [DecidableEq W]
    (dp : DecisionProblem W A) :
    ∀ {parts : Finset (Finset W)},
      (∀ p₁ ∈ parts, ∀ p₂ ∈ parts, p₁ ≠ p₂ → Disjoint p₁ p₂) →
      cellProbability dp (parts.sup id) = ∑ p ∈ parts, cellProbability dp p := by
  intro parts
  induction parts using Finset.induction with
  | empty => intro _; simp [cellProbability, Finset.sup_empty, Finset.bot_eq_empty]
  | insert p s hp ih =>
    intro hdisj
    have hsub : ∀ p₁ ∈ s, ∀ p₂ ∈ s, p₁ ≠ p₂ → Disjoint p₁ p₂ :=
      fun a ha b hb hab =>
        hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hdp : Disjoint p (s.sup id) :=
      Finset.disjoint_sup_right.mpr fun q hq =>
        hdisj p (Finset.mem_insert_self p s) q (Finset.mem_insert_of_mem hq)
          (fun h => hp (h ▸ hq))
    rw [Finset.sup_insert, Finset.sum_insert hp, id_eq, ← ih hsub]
    exact Finset.sum_union hdp

/-- `questionUtility` in linearized form: total best-action value minus the baseline value
weighted by total cell mass. Lets refinement monotonicity reduce to `∑ uValue` superadditivity
once total mass is shown invariant. -/
private lemma questionUtility_eq {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (acts : Finset A) (cells : Finset (Finset W))
    (hprior : ∀ w, 0 ≤ dp.prior w) :
    questionUtility dp acts cells
      = (∑ c ∈ cells, uValue dp acts c)
        - dpValue dp acts * (∑ c ∈ cells, cellProbability dp c) := by
  unfold questionUtility
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  unfold utilityValue
  rw [mul_sub, cellProb_mul_valueAfterLearning_eq_uValue dp acts c hprior]
  ring

/-- **Question utility is monotone under partition refinement** — the `⟹` direction of
[van-rooy-2003]'s §4.1 Fact (p. 743), in full generality. A finer partition `fine`
(presented as a refinement of `coarse` via `assign`, with each coarse cell the disjoint
union of its fiber) has `EUV ≥` the coarser one. By [blackwell-1953]: post-processing the
finer experiment cannot raise the convex value. Generalizes `questionUtility_split_ge`. -/
theorem questionUtility_mono_of_refines {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (acts : Finset A)
    {fine coarse : Finset (Finset W)} (assign : Finset W → Finset W)
    (hmaps : ∀ f ∈ fine, assign f ∈ coarse)
    (hcover : ∀ c ∈ coarse, c = (fine.filter (fun f => assign f = c)).sup id)
    (hdisj : ∀ f₁ ∈ fine, ∀ f₂ ∈ fine, f₁ ≠ f₂ → Disjoint f₁ f₂)
    (hprior : ∀ w, 0 ≤ dp.prior w) :
    questionUtility dp acts coarse ≤ questionUtility dp acts fine := by
  have hfdisj : ∀ c ∈ coarse, ∀ f₁ ∈ fine.filter (fun f => assign f = c),
      ∀ f₂ ∈ fine.filter (fun f => assign f = c), f₁ ≠ f₂ → Disjoint f₁ f₂ :=
    fun c _ f₁ hf₁ f₂ hf₂ hne =>
      hdisj f₁ (Finset.mem_of_mem_filter _ hf₁) f₂ (Finset.mem_of_mem_filter _ hf₂) hne
  have hcell : ∑ c ∈ coarse, cellProbability dp c = ∑ f ∈ fine, cellProbability dp f := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun f => cellProbability dp f)]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [← cellProb_sup dp (hfdisj c hc)]
    exact congrArg (cellProbability dp) (hcover c hc)
  have huv : ∑ c ∈ coarse, uValue dp acts c ≤ ∑ f ∈ fine, uValue dp acts f := by
    calc ∑ c ∈ coarse, uValue dp acts c
        = ∑ c ∈ coarse, uValue dp acts ((fine.filter (fun f => assign f = c)).sup id) :=
          Finset.sum_congr rfl (fun c hc => congrArg (uValue dp acts) (hcover c hc))
      _ ≤ ∑ c ∈ coarse, ∑ f ∈ fine.filter (fun f => assign f = c), uValue dp acts f :=
          Finset.sum_le_sum (fun c hc => uValue_sup_le dp acts (hfdisj c hc))
      _ = ∑ f ∈ fine, uValue dp acts f :=
          Finset.sum_fiberwise_of_maps_to hmaps (fun f => uValue dp acts f)
  rw [questionUtility_eq dp acts coarse hprior, questionUtility_eq dp acts fine hprior, hcell]
  linarith [huv]

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
question" to the decision-theoretic question framework of [van-rooy-2003]. -/

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

[van-rooy-2003]'s relevance-based orderings on answers and questions. -/

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
