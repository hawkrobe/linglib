/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Linglib.Core.Order.Partition.Finpartition

/-!
# Decision problems and the value of information

A finite decision problem has a prior over worlds and a utility for each action in each world,
valued in a linearly ordered field. This file defines van Rooy's decision-theoretic values of
propositions and questions: expected utility, the utility value `UV` of learning a proposition,
the expected utility value `EUV` of a question, and the value of sample information `VSI` and its
expectation `EVSI`. It imports no question semantics, so any module can use decision problems.

## Main definitions

* `DecisionProblem`: a utility function `W → A → K` with a prior `W → K`.
  The structure itself is constraint-free; theorems assume
  `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`.
* `DecisionProblem.expectedUtility`, `.value`, `.condExpectedUtility`,
  `.condValue`, `.utilityValue`: `EU(a)`, `V(D)`, `EU(a ∣ C)`, `V(D ∣ C)`,
  and `UV(C) = V(D ∣ C) − V(D)`.
* `DecisionProblem.questionUtility`: `EUV(Q) = ∑_{q ∈ Q} P(q) · UV(q)`.
* `DecisionProblem.valueSampleInfo`, `.expectedValueSampleInfo`: `VSI` and `EVSI`.
* `DecisionProblem.IsResolved`: information resolves a decision problem.

## Main results

* `DecisionProblem.questionUtility_eq_expectedValueSampleInfo`,
  `.questionUtility_parts_eq_expectedValueSampleInfo`: `EUV(Q) = EVSI(Q)`, so a partition
  question is never worth less than nothing (`questionUtility_parts_nonneg`).
* `DecisionProblem.sum_cellProbability_mul_condExpectedUtility`: the law of total
  expectation over a partition.
* `DecisionProblem.questionUtility_anti_of_le`: `EUV` is antitone in the `Finpartition`
  refinement order.
* `DecisionProblem.questionUtility_mono_of_refines`: `EUV` is monotone under
  partition refinement.

## Implementation notes

Sums over all worlds use `[Fintype W]`; action sets, propositions and the cells of a question
are `Finset`s. An empty action set gets the junk value `0`, with `_of_nonempty` lemmas as the
working API.

## References

* [van-rooy-2003]
* [blackwell-1953]
-/

@[expose] public section

namespace Core.DecisionTheory

variable {K W A : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A decision problem `D = (W, A, U, π)` has a utility for each action in each world and a
prior over worlds. -/
structure DecisionProblem (K W A : Type*) where
  /-- Utility of action `a` in world `w`. -/
  utility : W → A → K
  /-- Prior beliefs over worlds (should sum to 1 for proper probability). -/
  prior : W → K

namespace DecisionProblem

/-! ### Expected utility -/

variable (dp : DecisionProblem K W A)

/-- The expected utility of action `a` is its utility averaged over the prior. -/
def expectedUtility [Fintype W] (a : A) : K :=
  ∑ w : W, dp.prior w * dp.utility w a

/-- The value of a decision problem is the best expected utility of an action, or `0` when
there is no action. -/
def value [Fintype W] (actions : Finset A) : K :=
  if h : actions.Nonempty then actions.sup' h dp.expectedUtility else 0

/-- The conditional expected utility of action `a` given `cell` averages its utility over the
prior restricted to `cell`, and is `0` on a cell of zero mass. -/
def condExpectedUtility (cell : Finset W) (a : A) : K :=
  if cell.sum dp.prior = 0 then 0
  else cell.sum (fun w ↦ (dp.prior w / cell.sum dp.prior) * dp.utility w a)

/-- The value of the decision problem after learning `cell` is the best conditional expected
utility of an action. -/
def condValue (actions : Finset A) (cell : Finset W) : K :=
  if h : actions.Nonempty then actions.sup' h (dp.condExpectedUtility cell) else 0

/-- The utility value `UV(C) = V(D ∣ C) − V(D)` of learning `C` is the value after learning it
less the value before. -/
def utilityValue [Fintype W] (actions : Finset A) (cell : Finset W) : K :=
  dp.condValue actions cell - dp.value actions

/-- The probability of a cell is its prior mass. -/
def cellProbability (cell : Finset W) : K :=
  cell.sum dp.prior

section CharacterizationApi

variable {dp} {actions : Finset A} {cell : Finset W}

omit [IsStrictOrderedRing K] in
theorem value_of_nonempty [Fintype W] (h : actions.Nonempty) :
    dp.value actions = actions.sup' h dp.expectedUtility := dite_eq_left h

omit [IsStrictOrderedRing K] in
@[simp] theorem value_empty [Fintype W] : dp.value (∅ : Finset A) = 0 :=
  dite_eq_right Finset.not_nonempty_empty

omit [IsStrictOrderedRing K] in
theorem condValue_of_nonempty (h : actions.Nonempty) :
    dp.condValue actions cell = actions.sup' h (dp.condExpectedUtility cell) :=
  dite_eq_left h

omit [IsStrictOrderedRing K] in
@[simp] theorem condValue_empty : dp.condValue (∅ : Finset A) cell = 0 :=
  dite_eq_right Finset.not_nonempty_empty

omit [IsStrictOrderedRing K] in
theorem condExpectedUtility_of_ne_zero (h : cell.sum dp.prior ≠ 0) (a : A) :
    dp.condExpectedUtility cell a
      = cell.sum (fun w ↦ (dp.prior w / cell.sum dp.prior) * dp.utility w a) :=
  ite_eq_right h

omit [IsStrictOrderedRing K] in
@[simp] theorem condExpectedUtility_of_eq_zero (h : cell.sum dp.prior = 0) (a : A) :
    dp.condExpectedUtility cell a = 0 := ite_eq_left h

omit [IsStrictOrderedRing K] in
/-- The value of a decision problem is the expected utility of an action at least as good as
every other. -/
theorem value_eq_of_forall_le [Fintype W] {a : A} (ha : a ∈ actions)
    (h : ∀ b ∈ actions, dp.expectedUtility b ≤ dp.expectedUtility a) :
    dp.value actions = dp.expectedUtility a := by
  rw [value_of_nonempty ⟨a, ha⟩]
  exact le_antisymm (Finset.sup'_le _ _ h) (Finset.le_sup' _ ha)

omit [IsStrictOrderedRing K] in
/-- The value after learning `cell` is the conditional expected utility of an action at least
as good as every other there. -/
theorem condValue_eq_of_forall_le {a : A} (ha : a ∈ actions)
    (h : ∀ b ∈ actions, dp.condExpectedUtility cell b ≤ dp.condExpectedUtility cell a) :
    dp.condValue actions cell = dp.condExpectedUtility cell a := by
  rw [condValue_of_nonempty ⟨a, ha⟩]
  exact le_antisymm (Finset.sup'_le _ _ h) (Finset.le_sup' _ ha)

/-- Weighting the conditional expected utility by the probability of the cell undoes the
conditioning, for a nonnegative prior. -/
theorem cellProbability_mul_condExpectedUtility (hprior : ∀ w, 0 ≤ dp.prior w) (a : A) :
    dp.cellProbability cell * dp.condExpectedUtility cell a =
      ∑ w ∈ cell, dp.prior w * dp.utility w a := by
  by_cases h : cell.sum dp.prior = 0
  · rw [condExpectedUtility_of_eq_zero h, mul_zero]
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦ hprior w).1 h
    exact (Finset.sum_eq_zero fun w hw ↦ by rw [h0 w hw, zero_mul]).symm
  · rw [condExpectedUtility_of_ne_zero h, cellProbability, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ ↦ by
      rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_div_cancel_left₀ _ h]

/-- Weighting the value after learning `cell` by the probability of the cell gives the best
unnormalized expected utility on the cell, for a nonnegative prior. -/
theorem cellProbability_mul_condValue (hprior : ∀ w, 0 ≤ dp.prior w) (hne : actions.Nonempty) :
    dp.cellProbability cell * dp.condValue actions cell =
      actions.sup' hne fun a ↦ ∑ w ∈ cell, dp.prior w * dp.utility w a := by
  have hnn : 0 ≤ dp.cellProbability cell := Finset.sum_nonneg fun w _ ↦ hprior w
  rw [condValue_of_nonempty hne, Finset.mul₀_sup' hnn]
  exact Finset.sup'_congr hne rfl fun a _ ↦ cellProbability_mul_condExpectedUtility hprior a

end CharacterizationApi

variable {dp}

/-! ### Resolution -/

/-- Information `c` resolves the decision problem when some action is at least as good as
every other in every world of `c` ([van-rooy-2003]). -/
def IsResolved (dp : DecisionProblem K W A) (acts : Set A) (c : Set W) : Prop :=
  ∃ a ∈ acts, ∀ b ∈ acts, ∀ w ∈ c, dp.utility w b ≤ dp.utility w a

/-- `IsResolved` is decidable over finite, decidable sets of actions and worlds. -/
instance IsResolved.instDecidable (dp : DecisionProblem K W A) (acts : Set A) (c : Set W)
    [Fintype A] [DecidablePred (· ∈ acts)] [Fintype W] [DecidablePred (· ∈ c)] :
    Decidable (IsResolved dp acts c) := by
  unfold IsResolved; infer_instance

/-! ### Question utility -/

/-- The expected utility value `EUV(Q) = ∑_{q ∈ Q} P(q) · UV(q)` of the question `Q` weights the
utility value of each cell by its probability. -/
def questionUtility [Fintype W] (dp : DecisionProblem K W A) (actions : Finset A)
    (cells : Finset (Finset W)) : K :=
  cells.sum (fun cell ↦ dp.cellProbability cell * dp.utilityValue actions cell)

/-! ### Value of sample information -/

/-- The optimal action is an action of highest expected utility, chosen classically. -/
noncomputable def optimalAction [Fintype W] (dp : DecisionProblem K W A)
    (actions : Finset A) : Option A :=
  if h : actions.Nonempty then
    some (Finset.exists_max_image actions dp.expectedUtility h).choose
  else none

/-- The value of sample information `VSI(C) = V(D ∣ C) − EU(a⁰ ∣ C)` of learning `C` compares
the best action after learning `C` with the currently optimal action `a⁰`. Unlike the utility
value it is never negative (`valueSampleInfo_nonneg`). -/
noncomputable def valueSampleInfo [Fintype W] (dp : DecisionProblem K W A)
    (actions : Finset A) (cell : Finset W) : K :=
  let currentActionEU := match optimalAction dp actions with
    | some a => dp.condExpectedUtility cell a
    | none => 0
  dp.condValue actions cell - currentActionEU

/-- The expected value of sample information `EVSI(Q) = ∑ P(C) · VSI(C)` of asking the question
`Q` weights the value of sample information of each cell by its probability. -/
noncomputable def expectedValueSampleInfo [Fintype W] (dp : DecisionProblem K W A)
    (actions : Finset A) (cells : Finset (Finset W)) : K :=
  cells.sum (fun cell ↦ dp.cellProbability cell * valueSampleInfo dp actions cell)

section EuvEvsi

variable [Fintype W]

omit [IsStrictOrderedRing K] in
private lemma optimalAction_expectedUtility_eq_value (dp : DecisionProblem K W A)
    (actions : Finset A) :
    (match optimalAction dp actions with
     | some a => dp.expectedUtility a
     | none => (0 : K)) = dp.value actions := by
  unfold optimalAction value
  by_cases hne : actions.Nonempty
  · rw [dite_eq_left hne, dite_eq_left hne]; simp only []
    have hspec := (Finset.exists_max_image actions dp.expectedUtility hne).choose_spec
    exact le_antisymm (Finset.le_sup' _ hspec.1)
      (Finset.sup'_le hne _ fun a ha ↦ hspec.2 a ha)
  · rw [dite_eq_right hne, dite_eq_right hne]

omit [IsStrictOrderedRing K] in
/-- The expected utility value of a question equals its expected value of sample information,
given the law of total expectation over its cells and cell probabilities summing to one
([van-rooy-2003]). -/
theorem questionUtility_eq_expectedValueSampleInfo (dp : DecisionProblem K W A)
    (actions : Finset A) (cells : Finset (Finset W))
    (hLTE : ∀ a, cells.sum (fun cell ↦
      dp.cellProbability cell * dp.condExpectedUtility cell a) = dp.expectedUtility a)
    (hSum : cells.sum (fun cell ↦ dp.cellProbability cell) = 1) :
    questionUtility dp actions cells = expectedValueSampleInfo dp actions cells := by
  set S := cells.sum (fun cell ↦
      dp.cellProbability cell * dp.condValue actions cell)
  have hLHS : questionUtility dp actions cells = S - dp.value actions := by
    unfold questionUtility; simp only [utilityValue]; simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1; rw [← Finset.sum_mul, hSum, one_mul]
  have hRHS : expectedValueSampleInfo dp actions cells = S - dp.value actions := by
    unfold expectedValueSampleInfo; dsimp only [valueSampleInfo]; simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1; rw [← optimalAction_expectedUtility_eq_value dp actions]
    generalize optimalAction dp actions = oa
    cases oa with
    | none => simp
    | some a => exact hLTE a
  rw [hLHS, hRHS]

/-- Sample information is never worth less than nothing. -/
theorem valueSampleInfo_nonneg (dp : DecisionProblem K W A) (actions : Finset A)
    (cell : Finset W) : 0 ≤ valueSampleInfo dp actions cell := by
  unfold valueSampleInfo optimalAction
  split_ifs with h
  · rw [condValue_of_nonempty h, sub_nonneg]
    exact Finset.le_sup' (dp.condExpectedUtility cell)
      (Finset.exists_max_image actions _ h).choose_spec.1
  · simp [condValue, h]

/-- The expected value of sample information is never negative. -/
theorem expectedValueSampleInfo_nonneg (dp : DecisionProblem K W A) (actions : Finset A)
    (hprior : ∀ w, 0 ≤ dp.prior w) (cells : Finset (Finset W)) :
    0 ≤ expectedValueSampleInfo dp actions cells :=
  Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (Finset.sum_nonneg fun w _ ↦ hprior w) (valueSampleInfo_nonneg dp actions _)

variable [DecidableEq W] (Q : Finpartition (Finset.univ : Finset W))

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The cells of a partition carry the whole prior mass. -/
theorem sum_cellProbability_parts (dp : DecisionProblem K W A) :
    ∑ c ∈ Q.parts, dp.cellProbability c = ∑ w, dp.prior w :=
  Q.sum_parts_sum dp.prior

/-- The law of total expectation holds over a partition. -/
theorem sum_cellProbability_mul_condExpectedUtility (dp : DecisionProblem K W A)
    (hprior : ∀ w, 0 ≤ dp.prior w) (a : A) :
    ∑ c ∈ Q.parts, dp.cellProbability c * dp.condExpectedUtility c a = dp.expectedUtility a := by
  simp_rw [cellProbability_mul_condExpectedUtility hprior]
  exact Q.sum_parts_sum _

/-- The expected utility value of a partition question is its expected value of sample
information. -/
theorem questionUtility_parts_eq_expectedValueSampleInfo (dp : DecisionProblem K W A)
    (actions : Finset A) (hprior : ∀ w, 0 ≤ dp.prior w) (hsum : ∑ w, dp.prior w = 1) :
    questionUtility dp actions Q.parts = expectedValueSampleInfo dp actions Q.parts :=
  questionUtility_eq_expectedValueSampleInfo dp actions Q.parts
    (sum_cellProbability_mul_condExpectedUtility Q dp hprior)
    ((sum_cellProbability_parts Q dp).trans hsum)

/-- A partition question is never worth less than nothing. -/
theorem questionUtility_parts_nonneg (dp : DecisionProblem K W A) (actions : Finset A)
    (hprior : ∀ w, 0 ≤ dp.prior w) (hsum : ∑ w, dp.prior w = 1) :
    0 ≤ questionUtility dp actions Q.parts :=
  questionUtility_parts_eq_expectedValueSampleInfo Q dp actions hprior hsum ▸
    expectedValueSampleInfo_nonneg dp actions hprior _

/-- A partition question is worth nothing when an optimal action stays optimal whatever the
answer. -/
theorem questionUtility_parts_eq_zero (dp : DecisionProblem K W A) {actions : Finset A}
    (hprior : ∀ w, 0 ≤ dp.prior w) (hsum : ∑ w, dp.prior w = 1) {a : A} (hmem : a ∈ actions)
    (ha : dp.expectedUtility a = dp.value actions)
    (hdom : ∀ c ∈ Q.parts, ∀ b ∈ actions, dp.condExpectedUtility c b ≤ dp.condExpectedUtility c a) :
    questionUtility dp actions Q.parts = 0 := by
  unfold questionUtility
  simp only [utilityValue]
  rw [Finset.sum_congr rfl fun c hc ↦ by rw [condValue_eq_of_forall_le hmem (hdom c hc)]]
  simp only [mul_sub, Finset.sum_sub_distrib,
    sum_cellProbability_mul_condExpectedUtility Q dp hprior, ← Finset.sum_mul,
    sum_cellProbability_parts, hsum, one_mul, ha, sub_self]

end EuvEvsi

/-! ### Refinement monotonicity

[van-rooy-2003] states on p. 743 that one question refines another exactly when it is at least
as useful in every decision problem, "a special case of [blackwell-1953]". This section proves
the direction that a finer question can only raise question utility. The unnormalized value
`maxₐ ∑_{w∈c} P(w)·U(w,a)` of a cell equals `P(c)·V(D|c)` and is superadditive under
splitting the cell, since the best of a sum is at most the sum of the bests; summing over a
partition gives the inequality. For arbitrary experiments in place of partitions, the same
direction is `valueOfInformation_decisionValue_comp_le` in
`Core.Probability.Decision.ValueOfInformation`. -/

section Refinement

/-- The unnormalized value of `cell` is the best unnormalized expected utility
`∑_{w∈cell} P(w)·U(w,a)` of an action on it. -/
private def uValue (dp : DecisionProblem K W A) (acts : Finset A) (cell : Finset W) : K :=
  if h : acts.Nonempty then
    acts.sup' h (fun a ↦ ∑ w ∈ cell, dp.prior w * dp.utility w a)
  else 0

/-- The probability-weighted value after learning `cell` is its unnormalized value. -/
private lemma cellProbability_mul_condValue_eq_uValue (dp : DecisionProblem K W A)
    (acts : Finset A) (cell : Finset W) (hprior : ∀ w, 0 ≤ dp.prior w) :
    dp.cellProbability cell * dp.condValue acts cell = uValue dp acts cell := by
  unfold uValue
  by_cases hne : acts.Nonempty
  · rw [dite_eq_left hne, cellProbability_mul_condValue hprior hne]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, condValue_empty, dite_eq_right
      Finset.not_nonempty_empty, mul_zero]

variable [DecidableEq W]

/-- Splitting a cell into two disjoint pieces cannot lower its unnormalized value, since the
best of a sum is at most the sum of the bests. -/
private lemma uValue_union_le (dp : DecisionProblem K W A) (acts : Finset A)
    {c₁ c₂ : Finset W} (hdisj : Disjoint c₁ c₂) :
    uValue dp acts (c₁ ∪ c₂) ≤ uValue dp acts c₁ + uValue dp acts c₂ := by
  unfold uValue
  by_cases hne : acts.Nonempty
  · rw [dite_eq_left hne, dite_eq_left hne, dite_eq_left hne]
    refine Finset.sup'_le hne _ (fun a ha ↦ ?_)
    rw [Finset.sum_union hdisj]
    exact add_le_add (Finset.le_sup' (fun a ↦ ∑ w ∈ c₁, dp.prior w * dp.utility w a) ha)
      (Finset.le_sup' (fun a ↦ ∑ w ∈ c₂, dp.prior w * dp.utility w a) ha)
  · rw [dite_eq_right hne, dite_eq_right hne, dite_eq_right hne, add_zero]

/-! A refinement is presented by a map `assign` sending each finer cell to the coarser cell
containing it, each coarser cell being the union (`Finset.sup`) of its fibre. Superadditivity of
`uValue` over each fibre then compares the two questions. -/

omit [DecidableEq W] [IsStrictOrderedRing K] in
private lemma uValue_empty (dp : DecisionProblem K W A) (acts : Finset A) :
    uValue dp acts ∅ = 0 := by
  unfold uValue
  by_cases h : acts.Nonempty
  · rw [dite_eq_left h]; simp only [Finset.sum_empty, Finset.sup'_const]
  · rw [dite_eq_right h]

/-- Splitting a union of pairwise disjoint cells into its pieces never lowers the unnormalized
value. -/
private lemma uValue_sup_le (dp : DecisionProblem K W A) (acts : Finset A) :
    ∀ {parts : Finset (Finset W)},
      (∀ p₁ ∈ parts, ∀ p₂ ∈ parts, p₁ ≠ p₂ → Disjoint p₁ p₂) →
      uValue dp acts (parts.sup id) ≤ ∑ p ∈ parts, uValue dp acts p := by
  intro parts
  induction parts using Finset.induction with
  | empty => intro _; simp [uValue_empty]
  | insert p s hp ih =>
    intro hdisj
    have hsub : ∀ p₁ ∈ s, ∀ p₂ ∈ s, p₁ ≠ p₂ → Disjoint p₁ p₂ :=
      fun a ha b hb hab ↦
        hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hdp : Disjoint p (s.sup id) :=
      Finset.disjoint_sup_right.mpr fun q hq ↦
        hdisj p (Finset.mem_insert_self p s) q (Finset.mem_insert_of_mem hq)
          (fun h ↦ hp (h ▸ hq))
    rw [Finset.sup_insert, Finset.sum_insert hp, id_eq]
    calc uValue dp acts (p ⊔ s.sup id)
        ≤ uValue dp acts p + uValue dp acts (s.sup id) := uValue_union_le dp acts hdp
      _ ≤ uValue dp acts p + ∑ q ∈ s, uValue dp acts q := by linarith [ih hsub]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Cell probability is additive over a union of pairwise-disjoint cells. -/
private lemma cellProbability_sup (dp : DecisionProblem K W A) :
    ∀ {parts : Finset (Finset W)},
      (∀ p₁ ∈ parts, ∀ p₂ ∈ parts, p₁ ≠ p₂ → Disjoint p₁ p₂) →
      dp.cellProbability (parts.sup id) = ∑ p ∈ parts, dp.cellProbability p := by
  intro parts
  induction parts using Finset.induction with
  | empty => intro _; simp [cellProbability, Finset.sup_empty, Finset.bot_eq_empty]
  | insert p s hp ih =>
    intro hdisj
    have hsub : ∀ p₁ ∈ s, ∀ p₂ ∈ s, p₁ ≠ p₂ → Disjoint p₁ p₂ :=
      fun a ha b hb hab ↦
        hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hdp : Disjoint p (s.sup id) :=
      Finset.disjoint_sup_right.mpr fun q hq ↦
        hdisj p (Finset.mem_insert_self p s) q (Finset.mem_insert_of_mem hq)
          (fun h ↦ hp (h ▸ hq))
    rw [Finset.sup_insert, Finset.sum_insert hp, id_eq, ← ih hsub]
    exact Finset.sum_union hdp

omit [DecidableEq W] in
/-- The expected utility value of a question is the total unnormalized value of its cells minus
the prior value weighted by their total mass. -/
private lemma questionUtility_eq [Fintype W] (dp : DecisionProblem K W A)
    (acts : Finset A) (cells : Finset (Finset W)) (hprior : ∀ w, 0 ≤ dp.prior w) :
    questionUtility dp acts cells
      = (∑ c ∈ cells, uValue dp acts c)
        - dp.value acts * (∑ c ∈ cells, dp.cellProbability c) := by
  unfold questionUtility
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun c _ ↦ ?_)
  unfold utilityValue
  rw [mul_sub, cellProbability_mul_condValue_eq_uValue dp acts c hprior]
  ring

/-- A finer question is worth at least as much as a coarser one, the refinement presented by a
map `assign` sending each finer cell to the coarser cell that is the union of its fibre. -/
theorem questionUtility_mono_of_refines [Fintype W] (dp : DecisionProblem K W A)
    (acts : Finset A) {fine coarse : Finset (Finset W)} (assign : Finset W → Finset W)
    (hmaps : ∀ f ∈ fine, assign f ∈ coarse)
    (hcover : ∀ c ∈ coarse, c = (fine.filter (fun f ↦ assign f = c)).sup id)
    (hdisj : ∀ f₁ ∈ fine, ∀ f₂ ∈ fine, f₁ ≠ f₂ → Disjoint f₁ f₂)
    (hprior : ∀ w, 0 ≤ dp.prior w) :
    questionUtility dp acts coarse ≤ questionUtility dp acts fine := by
  have hfdisj : ∀ c ∈ coarse, ∀ f₁ ∈ fine.filter (fun f ↦ assign f = c),
      ∀ f₂ ∈ fine.filter (fun f ↦ assign f = c), f₁ ≠ f₂ → Disjoint f₁ f₂ :=
    fun c _ f₁ hf₁ f₂ hf₂ hne ↦
      hdisj f₁ (Finset.mem_of_mem_filter _ hf₁) f₂ (Finset.mem_of_mem_filter _ hf₂) hne
  have hcell : ∑ c ∈ coarse, dp.cellProbability c
      = ∑ f ∈ fine, dp.cellProbability f := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun f ↦ dp.cellProbability f)]
    refine Finset.sum_congr rfl (fun c hc ↦ ?_)
    rw [← cellProbability_sup dp (hfdisj c hc)]
    exact congrArg dp.cellProbability (hcover c hc)
  have huv : ∑ c ∈ coarse, uValue dp acts c ≤ ∑ f ∈ fine, uValue dp acts f := by
    calc ∑ c ∈ coarse, uValue dp acts c
        = ∑ c ∈ coarse, uValue dp acts ((fine.filter (fun f ↦ assign f = c)).sup id) :=
          Finset.sum_congr rfl (fun c hc ↦ congrArg (uValue dp acts) (hcover c hc))
      _ ≤ ∑ c ∈ coarse, ∑ f ∈ fine.filter (fun f ↦ assign f = c), uValue dp acts f :=
          Finset.sum_le_sum (fun c hc ↦ uValue_sup_le dp acts (hfdisj c hc))
      _ = ∑ f ∈ fine, uValue dp acts f :=
          Finset.sum_fiberwise_of_maps_to hmaps (fun f ↦ uValue dp acts f)
  rw [questionUtility_eq dp acts coarse hprior, questionUtility_eq dp acts fine hprior,
    hcell]
  linarith [huv]

/-- The expected utility value of a question is antitone in the refinement order of
partitions. -/
theorem questionUtility_anti_of_le [Fintype W] (dp : DecisionProblem K W A) (acts : Finset A)
    {P Q : Finpartition (Finset.univ : Finset W)} (h : P ≤ Q) (hprior : ∀ w, 0 ≤ dp.prior w) :
    questionUtility dp acts Q.parts ≤ questionUtility dp acts P.parts := by
  choose! assign hmem hsub using fun f (hf : f ∈ P.parts) ↦ h hf
  refine questionUtility_mono_of_refines dp acts assign hmem (fun c hc ↦ ?_)
    (fun f₁ hf₁ f₂ hf₂ hne ↦ P.disjoint hf₁ hf₂ hne) hprior
  ext x
  simp only [Finset.mem_sup, Finset.mem_filter, id]
  constructor
  · intro hx
    obtain ⟨f, hf, hxf⟩ := P.exists_mem (Finset.mem_univ x)
    exact ⟨f, ⟨hf, Q.eq_of_mem_parts (hmem f hf) hc (hsub f hf hxf) hx⟩, hxf⟩
  · rintro ⟨f, ⟨hf, rfl⟩, hxf⟩
    exact hsub f hf hxf

end Refinement

/-! ### Special decision problems -/

/-- An epistemic DP where the agent wants to know the exact world state. -/
def epistemic [DecidableEq W] (target : W) : DecisionProblem K W A where
  utility w _ := if w = target then 1 else 0
  prior _ := 1

/-- In the mention-some decision problem any satisfier resolves the problem. -/
def mentionSome (satisfies : W → Prop) [DecidablePred satisfies] :
    DecisionProblem K W Bool where
  utility w a := if a ∧ satisfies w then 1 else 0
  prior _ := 1

end DecisionProblem

end Core.DecisionTheory
