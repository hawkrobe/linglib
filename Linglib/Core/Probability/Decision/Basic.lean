/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
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
# Decision problems and the value of information

Finite decision problems over an arbitrary `LinearOrder`ed `Field K` and
[van-rooy-2003]'s decision-theoretic values of propositions and questions:
expected utility, utility value `UV`, question utility `EUV`, value of sample
information `VSI`/`EVSI`, and the maximin analogues. Theory-neutral: no
question-semantic imports, so any module (RSA, causal decision theory,
explanation models) can use decision problems without pulling in the
`Question` cone.

## Main definitions

* `DecisionProblem`: a utility function `W → A → K` with a prior `W → K`.
  The structure itself is constraint-free; theorems assume
  `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`. Studies instantiate
  `K := ℚ` for exact, `decide`-friendly arithmetic;
  `Core.Probability.Decision.ExperimentDesign` uses `K := ℝ` against `eig`.
* `DecisionProblem.expectedUtility`, `.value`, `.condExpectedUtility`,
  `.condValue`, `.utilityValue`: `EU(a)`, `V(D)`, `EU(a ∣ C)`, `V(D ∣ C)`,
  and `UV(C) = V(D ∣ C) − V(D)`.
* `DecisionProblem.questionUtility`: `EUV(Q) = ∑_{q ∈ Q} P(q) · UV(q)`.
* `DecisionProblem.valueSampleInfo`, `.expectedValueSampleInfo`:
  [van-rooy-2003]'s `VSI`/`EVSI` (p. 742).
* `DecisionProblem.securityLevel`, `.maximinValue`, `.maximinUtilityValue`,
  `.questionMaximin`: the maximin (worst-case) analogues.
* `DecisionProblem.IsResolved`: [van-rooy-2003]'s resolution of a decision
  problem (p. 736).

## Main results

* `DecisionProblem.questionUtility_eq_expectedValueSampleInfo`:
  `EUV(Q) = EVSI(Q)` ([van-rooy-2003], p. 742).
* `DecisionProblem.questionUtility_mono_of_refines`: `EUV` is monotone under
  partition refinement — the `⟹` direction of [van-rooy-2003]'s §4.1 Fact
  (p. 743).
* `DecisionProblem.binary_question_value_decomposition`: the yes/no-question
  instance.

## Design: Fintype + Finset

Functions that sum over the full universe use `[Fintype W]` with `∑ w : W`.
Functions that operate over action sets or world subsets use `Finset`.
`questionUtility` and `expectedValueSampleInfo` take `Finset (Finset W)`
(cells as sets); `questionMaximin` takes a `List (Finset W)` of cells.
Empty action sets get the junk value `0` (the `Real.sSup` convention), with
`_of_nonempty` characterization lemmas as the working API.

- [van-rooy-2003]. Questioning to Resolve Decision Problems. L&P 26.
- [blackwell-1953]. Equivalent Comparisons of Experiments.
-/

namespace Core.DecisionTheory

variable {K W A : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A decision problem `D = (W, A, U, π)` with utility and prior. -/
structure DecisionProblem (K W A : Type*) where
  /-- Utility of action `a` in world `w`. -/
  utility : W → A → K
  /-- Prior beliefs over worlds (should sum to 1 for proper probability). -/
  prior : W → K

namespace DecisionProblem

/-- The uniform prior over a `Fintype` of worlds (`0` when `W` is empty,
    since `1 / 0 = 0` in a field). -/
def uniformPrior [Fintype W] : W → K := λ _ => 1 / Fintype.card W

/-- Create a decision problem with uniform prior. -/
def withUniformPrior [Fintype W] (utility : W → A → K) : DecisionProblem K W A where
  utility := utility
  prior := uniformPrior

/-! ### Expected utility -/

variable (dp : DecisionProblem K W A)

/-- Expected utility of action `a` given the prior. -/
def expectedUtility [Fintype W] (a : A) : K :=
  ∑ w : W, dp.prior w * dp.utility w a

/-- Value of a decision problem: max EU over actions, or `0` if empty. -/
def value [Fintype W] (actions : Finset A) : K :=
  if h : actions.Nonempty then actions.sup' h dp.expectedUtility else 0

/-- Conditional expected utility of action `a` given cell membership
    (`0` on zero-mass cells). -/
def condExpectedUtility (cell : Finset W) (a : A) : K :=
  if cell.sum dp.prior = 0 then 0
  else cell.sum (λ w => (dp.prior w / cell.sum dp.prior) * dp.utility w a)

/-- Value of the decision problem after learning `cell`: best conditional EU
    among actions. -/
def condValue (actions : Finset A) (cell : Finset W) : K :=
  if h : actions.Nonempty then actions.sup' h (dp.condExpectedUtility cell) else 0

/-- `UV(C) = V(D ∣ C) − V(D)`, the utility value of learning proposition `C`. -/
def utilityValue [Fintype W] (actions : Finset A) (cell : Finset W) : K :=
  dp.condValue actions cell - dp.value actions

/-- Probability of a cell of the partition. -/
def cellProbability (cell : Finset W) : K :=
  cell.sum dp.prior

section CharacterizationApi

variable {dp} {actions : Finset A} {cell : Finset W}

omit [IsStrictOrderedRing K] in
theorem value_of_nonempty [Fintype W] (h : actions.Nonempty) :
    dp.value actions = actions.sup' h dp.expectedUtility := dif_pos h

omit [IsStrictOrderedRing K] in
@[simp] theorem value_empty [Fintype W] : dp.value (∅ : Finset A) = 0 :=
  dif_neg Finset.not_nonempty_empty

omit [IsStrictOrderedRing K] in
theorem condValue_of_nonempty (h : actions.Nonempty) :
    dp.condValue actions cell = actions.sup' h (dp.condExpectedUtility cell) :=
  dif_pos h

omit [IsStrictOrderedRing K] in
@[simp] theorem condValue_empty : dp.condValue (∅ : Finset A) cell = 0 :=
  dif_neg Finset.not_nonempty_empty

omit [IsStrictOrderedRing K] in
theorem condExpectedUtility_of_ne_zero (h : cell.sum dp.prior ≠ 0) (a : A) :
    dp.condExpectedUtility cell a
      = cell.sum (λ w => (dp.prior w / cell.sum dp.prior) * dp.utility w a) :=
  if_neg h

omit [IsStrictOrderedRing K] in
@[simp] theorem condExpectedUtility_of_eq_zero (h : cell.sum dp.prior = 0) (a : A) :
    dp.condExpectedUtility cell a = 0 := if_pos h

end CharacterizationApi

/-! ### Maximin -/

/-- `S(a) = min_w U(w, a)`, the security level of action `a`. -/
def securityLevel (worlds : Finset W) (a : A) : K :=
  if h : worlds.Nonempty then worlds.inf' h (λ w => dp.utility w a) else 0

/-- `MV = max_a min_w U(w, a)`, the maximin value. -/
def maximinValue (worlds : Finset W) (actions : Finset A) : K :=
  if h : actions.Nonempty then actions.sup' h (dp.securityLevel worlds) else 0

section MaximinApi

variable {dp} {worlds : Finset W} {actions : Finset A} {a : A}

omit [IsStrictOrderedRing K] in
theorem securityLevel_of_nonempty (h : worlds.Nonempty) :
    dp.securityLevel worlds a = worlds.inf' h (λ w => dp.utility w a) := dif_pos h

omit [IsStrictOrderedRing K] in
theorem maximinValue_of_nonempty (h : actions.Nonempty) :
    dp.maximinValue worlds actions = actions.sup' h (dp.securityLevel worlds) :=
  dif_pos h

omit [IsStrictOrderedRing K] in
@[simp] theorem maximinValue_empty :
    dp.maximinValue worlds (∅ : Finset A) = 0 := dif_neg Finset.not_nonempty_empty

end MaximinApi

section InterCells

variable [DecidableEq W]

/-- Conditional security level: worst case within cell `c`. -/
def condSecurityLevel (worlds : Finset W) (a : A) (c : Finset W) : K :=
  dp.securityLevel (worlds ∩ c) a

/-- Maximin value after learning `c`. -/
def condMaximinValue (worlds : Finset W) (actions : Finset A) (c : Finset W) : K :=
  dp.maximinValue (worlds ∩ c) actions

/-- Maximin utility value of learning `c`. -/
def maximinUtilityValue (worlds : Finset W) (actions : Finset A) (c : Finset W) : K :=
  dp.condMaximinValue worlds actions c - dp.maximinValue worlds actions

end InterCells

variable {dp}

/-! ### Resolution -/

/-- `c` **resolves** decision problem `(dp, acts)`: some action in `acts`
    weakly dominates every other action on every world in `c`
    ([van-rooy-2003], p. 736). -/
def IsResolved (dp : DecisionProblem K W A) (acts : Set A) (c : Set W) : Prop :=
  ∃ a ∈ acts, ∀ b ∈ acts, ∀ w ∈ c, dp.utility w b ≤ dp.utility w a

/-- Decidability of `IsResolved` under finite, decidable carriers — the
    prerequisite for `decide`-based evaluation in worked study examples. -/
instance IsResolved.instDecidable (dp : DecisionProblem K W A) (acts : Set A) (c : Set W)
    [Fintype A] [DecidablePred (· ∈ acts)] [Fintype W] [DecidablePred (· ∈ c)] :
    Decidable (IsResolved dp acts c) := by
  unfold IsResolved; infer_instance

/-! ### Question utility -/

/-- `EUV(Q) = ∑_{q ∈ Q} P(q) · UV(q)`, the expected utility value of
    question `Q`. -/
def questionUtility [Fintype W] (dp : DecisionProblem K W A) (actions : Finset A)
    (cells : Finset (Finset W)) : K :=
  cells.sum (λ cell => dp.cellProbability cell * dp.utilityValue actions cell)

/-- `MV(Q) = min_{q ∈ Q} MV(q)`, the maximin question value. -/
def questionMaximin [DecidableEq W] (dp : DecisionProblem K W A) (worlds : Finset W)
    (actions : Finset A) (q : List (Finset W)) : K :=
  match q with
  | [] => 0
  | c :: cs => cs.foldl (λ m cell =>
      min m (dp.maximinUtilityValue worlds actions cell)
    ) (dp.maximinUtilityValue worlds actions c)

/-! ### Value of sample information -/

/-- Optimal action: the one with highest expected utility.

    Noncomputable because it extracts a witness from an existential
    (`Finset.exists_max_image` via `Classical.choice`). -/
noncomputable def optimalAction [Fintype W] (dp : DecisionProblem K W A)
    (actions : Finset A) : Option A :=
  if h : actions.Nonempty then
    some (Finset.exists_max_image actions dp.expectedUtility h).choose
  else none

/-- `VSI(C) = V(D ∣ C) − EU(a⁰ ∣ C)`: the value of sample information from
    learning proposition `C`, where `a⁰` is the current optimal action.

    Unlike `UV(C) = V(D ∣ C) − V(D)`, `VSI` is always non-negative: learning
    `C` before choosing can never hurt relative to the current best action
    applied within `C` ([van-rooy-2003], p. 742). -/
noncomputable def valueSampleInfo [Fintype W] (dp : DecisionProblem K W A)
    (actions : Finset A) (cell : Finset W) : K :=
  let currentActionEU := match optimalAction dp actions with
    | some a => dp.condExpectedUtility cell a
    | none => 0
  dp.condValue actions cell - currentActionEU

/-- `EVSI(Q) = ∑ P(C) · VSI(C)`: the expected value of sample information
    from asking question `Q` ([van-rooy-2003], p. 742). -/
noncomputable def expectedValueSampleInfo [Fintype W] (dp : DecisionProblem K W A)
    (actions : Finset A) (cells : Finset (Finset W)) : K :=
  cells.sum (λ cell => dp.cellProbability cell * valueSampleInfo dp actions cell)

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
  · rw [dif_pos hne, dif_pos hne]; simp only []
    have hspec := (Finset.exists_max_image actions dp.expectedUtility hne).choose_spec
    exact le_antisymm (Finset.le_sup' _ hspec.1)
      (Finset.sup'_le hne _ λ a ha => hspec.2 a ha)
  · rw [dif_neg hne, dif_neg hne]

omit [IsStrictOrderedRing K] in
/-- `EUV(Q) = EVSI(Q)`: the expected utility value of a question equals its
    expected value of sample information.

    [van-rooy-2003], p. 742: "The expected utility value of a question is
    equal to its expected value of sample information."

    The two hypotheses are the **law of total expectation**
    (`∑ P(C) · EU(a ∣ C) = EU(a)` for all actions) and **cell probability
    normalization** (`∑ P(C) = 1`). -/
theorem questionUtility_eq_expectedValueSampleInfo (dp : DecisionProblem K W A)
    (actions : Finset A) (cells : Finset (Finset W))
    (hLTE : ∀ a, cells.sum (λ cell =>
      dp.cellProbability cell * dp.condExpectedUtility cell a) = dp.expectedUtility a)
    (hSum : cells.sum (λ cell => dp.cellProbability cell) = 1) :
    questionUtility dp actions cells = expectedValueSampleInfo dp actions cells := by
  set S := cells.sum (λ cell =>
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

end EuvEvsi

/-! ### Refinement monotonicity (Blackwell forward direction / [van-rooy-2003] §4.1)

[van-rooy-2003] p. 743 states that `Q ⊑ Q' ↔ ∀ DP, EUV(Q) ≥ EUV(Q')` is "a special
case of [blackwell-1953]". The `⟹` ("only if") direction is the data-processing /
Jensen inequality: a *finer* question can only raise question utility. We prove it
directly at the `questionUtility` level; the kernel-level fact it specializes —
coarsening a deterministic classifier is a Markov garbling, so the finer partition
has lower Bayes risk in every decision problem — is
`ProbabilityTheory.bayesRisk_deterministic_le_deterministic_comp` in
`Core.Probability.Decision.Blackwell`, and `eig_deterministicObs_eq_euv` in
`Core.Probability.Decision.ExperimentDesign` identifies `questionUtility` with the
expected value of the corresponding deterministic experiment.

The mathematical core is the **unnormalized cell value** `maxₐ ∑_{w∈c} P(w)·U(w,a)`,
which equals `P(c)·V(D|c)` (`cellProbability_mul_condValue_eq_uValue`) and is
**superadditive** under splitting a cell into disjoint pieces
(`uValue_union_le`): the max of a sum is at most the sum of the maxes. Summed over a
partition, this gives `questionUtility (finer) ≥ questionUtility (coarser)`. -/

section Refinement

/-- The **unnormalized cell value** of `cell`: the best, over actions, of the
*unnormalized* expected utility `∑_{w∈cell} P(w)·U(w,a)`. This linearizes the
probability-weighted conditional value `P(cell)·V(D|cell)` (see
`cellProbability_mul_condValue_eq_uValue`), turning Van Rooy's question utility
into a sum that splitting a cell can only increase. -/
private def uValue (dp : DecisionProblem K W A) (acts : Finset A) (cell : Finset W) : K :=
  if h : acts.Nonempty then
    acts.sup' h (λ a => ∑ w ∈ cell, dp.prior w * dp.utility w a)
  else 0

/-- `P(cell)·V(D|cell) = maxₐ ∑_{w∈cell} P(w)·U(w,a)`: the probability-weighted
conditional value equals the unnormalized cell value. The normalizing `1/P(cell)` in
`condExpectedUtility` cancels against the `P(cell)` weight; when `P(cell) = 0`, a
nonnegative prior forces every `P(w) = 0` on the cell, so both sides vanish. -/
private lemma cellProbability_mul_condValue_eq_uValue (dp : DecisionProblem K W A)
    (acts : Finset A) (cell : Finset W) (hprior : ∀ w, 0 ≤ dp.prior w) :
    dp.cellProbability cell * dp.condValue acts cell = uValue dp acts cell := by
  unfold uValue
  by_cases hne : acts.Nonempty
  · rw [condValue_of_nonempty hne, dif_pos hne]
    have htp_nonneg : 0 ≤ dp.cellProbability cell :=
      Finset.sum_nonneg (λ w _ => hprior w)
    by_cases htp : dp.cellProbability cell = 0
    · rw [htp, zero_mul]
      have hpw : ∀ w ∈ cell, dp.prior w = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (λ w _ => hprior w)).mp htp
      have hz : ∀ a ∈ acts, (∑ w ∈ cell, dp.prior w * dp.utility w a) = 0 := by
        intro a _; exact Finset.sum_eq_zero (λ w hw => by rw [hpw w hw, zero_mul])
      rw [Finset.sup'_congr hne rfl hz, Finset.sup'_const]
    · have hS : cell.sum dp.prior ≠ 0 := htp
      rw [Finset.mul₀_sup' htp_nonneg (dp.condExpectedUtility cell) acts hne]
      refine Finset.sup'_congr hne rfl (λ a _ => ?_)
      show cell.sum dp.prior * dp.condExpectedUtility cell a
          = ∑ w ∈ cell, dp.prior w * dp.utility w a
      rw [condExpectedUtility_of_ne_zero hS, Finset.mul_sum]
      refine Finset.sum_congr rfl (λ w _ => ?_)
      rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_div_cancel_left₀ _ hS]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, condValue_empty, dif_neg
      Finset.not_nonempty_empty, mul_zero]

variable [DecidableEq W]

/-- **Superadditivity of unnormalized cell value under splitting**: when `cell` is the
disjoint union of `c₁` and `c₂`, splitting it can only raise the best-action value,
`uValue (c₁ ∪ c₂) ≤ uValue c₁ + uValue c₂` (max of a sum ≤ sum of maxes). This is the
combinatorial heart of [blackwell-1953]'s forward direction. -/
private lemma uValue_union_le (dp : DecisionProblem K W A) (acts : Finset A)
    {c₁ c₂ : Finset W} (hdisj : Disjoint c₁ c₂) :
    uValue dp acts (c₁ ∪ c₂) ≤ uValue dp acts c₁ + uValue dp acts c₂ := by
  unfold uValue
  by_cases hne : acts.Nonempty
  · rw [dif_pos hne, dif_pos hne, dif_pos hne]
    refine Finset.sup'_le hne _ (λ a ha => ?_)
    rw [Finset.sum_union hdisj]
    exact add_le_add (Finset.le_sup' (λ a => ∑ w ∈ c₁, dp.prior w * dp.utility w a) ha)
      (Finset.le_sup' (λ a => ∑ w ∈ c₂, dp.prior w * dp.utility w a) ha)
  · rw [dif_neg hne, dif_neg hne, dif_neg hne, add_zero]

/-- **Splitting a cell never decreases its decision value**: for disjoint cells `c₁`, `c₂`
and a nonnegative prior,
`P(c₁ ∪ c₂)·V(D|c₁ ∪ c₂) ≤ P(c₁)·V(D|c₁) + P(c₂)·V(D|c₂)`.
This is [blackwell-1953]'s data-processing inequality for a single binary refinement, the
building block of [van-rooy-2003]'s §4.1 question-utility monotonicity (p. 743). -/
theorem cellProbability_mul_condValue_union_le (dp : DecisionProblem K W A)
    (acts : Finset A) {c₁ c₂ : Finset W} (hdisj : Disjoint c₁ c₂)
    (hprior : ∀ w, 0 ≤ dp.prior w) :
    dp.cellProbability (c₁ ∪ c₂) * dp.condValue acts (c₁ ∪ c₂) ≤
    dp.cellProbability c₁ * dp.condValue acts c₁ +
    dp.cellProbability c₂ * dp.condValue acts c₂ := by
  rw [cellProbability_mul_condValue_eq_uValue dp acts _ hprior,
    cellProbability_mul_condValue_eq_uValue dp acts _ hprior,
    cellProbability_mul_condValue_eq_uValue dp acts _ hprior]
  exact uValue_union_le dp acts hdisj

/-- **Question utility rises under refinement (binary split)** — the `⟹` ("only if")
direction of [van-rooy-2003]'s §4.1 Fact (p. 743), in its elementary case. Splitting one
cell `c₁ ∪ c₂` of a question into the two disjoint cells `c₁`, `c₂` can only increase the
expected utility value `EUV`. This is the finite-partition instance of [blackwell-1953]'s
data-processing inequality; any finite refinement of one partition by another is a
composition of such binary splits, so iterating gives the full §4.1 monotonicity. -/
theorem questionUtility_split_ge [Fintype W] (dp : DecisionProblem K W A)
    (acts : Finset A) {c₁ c₂ : Finset W} (rest : Finset (Finset W))
    (hdisj : Disjoint c₁ c₂) (hprior : ∀ w, 0 ≤ dp.prior w)
    (hc₁ : c₁ ∉ rest) (hc₂ : c₂ ∉ rest) (hne12 : c₁ ≠ c₂) (hcrest : c₁ ∪ c₂ ∉ rest) :
    questionUtility dp acts (insert (c₁ ∪ c₂) rest) ≤
    questionUtility dp acts (insert c₁ (insert c₂ rest)) := by
  have hc₁' : c₁ ∉ insert c₂ rest := by
    simp only [Finset.mem_insert, not_or]; exact ⟨hne12, hc₁⟩
  have hcp : dp.cellProbability (c₁ ∪ c₂)
      = dp.cellProbability c₁ + dp.cellProbability c₂ := Finset.sum_union hdisj
  have hcpd : dp.cellProbability (c₁ ∪ c₂) * dp.value acts
      = dp.cellProbability c₁ * dp.value acts
        + dp.cellProbability c₂ * dp.value acts := by rw [hcp]; ring
  have hsplit := cellProbability_mul_condValue_union_le dp acts hdisj hprior
  unfold questionUtility
  rw [Finset.sum_insert hcrest, Finset.sum_insert hc₁', Finset.sum_insert hc₂]
  simp only [utilityValue, mul_sub]
  linarith [hsplit, hcpd]

/-! #### General partition refinement

The binary `questionUtility_split_ge` lifts to an arbitrary refinement of one partition by
another, via general superadditivity of `uValue` and a fiberwise regrouping. The refinement
is presented by a map `assign` sending each finer cell to the coarser cell containing it,
with each coarser cell the union (`Finset.sup`) of its fiber. -/

omit [DecidableEq W] [IsStrictOrderedRing K] in
private lemma uValue_empty (dp : DecisionProblem K W A) (acts : Finset A) :
    uValue dp acts ∅ = 0 := by
  unfold uValue
  by_cases h : acts.Nonempty
  · rw [dif_pos h]; simp only [Finset.sum_empty, Finset.sup'_const]
  · rw [dif_neg h]

/-- **General superadditivity of `uValue`**: splitting a union of pairwise-disjoint cells
into its pieces never lowers the best-action value, `uValue (⨆ parts) ≤ ∑ uValue`. The
`Finset.induction` engine for the refinement monotonicity below. -/
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
      λ a ha b hb hab =>
        hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hdp : Disjoint p (s.sup id) :=
      Finset.disjoint_sup_right.mpr λ q hq =>
        hdisj p (Finset.mem_insert_self p s) q (Finset.mem_insert_of_mem hq)
          (λ h => hp (h ▸ hq))
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
      λ a ha b hb hab =>
        hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hdp : Disjoint p (s.sup id) :=
      Finset.disjoint_sup_right.mpr λ q hq =>
        hdisj p (Finset.mem_insert_self p s) q (Finset.mem_insert_of_mem hq)
          (λ h => hp (h ▸ hq))
    rw [Finset.sup_insert, Finset.sum_insert hp, id_eq, ← ih hsub]
    exact Finset.sum_union hdp

omit [DecidableEq W] in
/-- `questionUtility` in linearized form: total best-action value minus the baseline value
weighted by total cell mass. Lets refinement monotonicity reduce to `∑ uValue` superadditivity
once total mass is shown invariant. -/
private lemma questionUtility_eq [Fintype W] (dp : DecisionProblem K W A)
    (acts : Finset A) (cells : Finset (Finset W)) (hprior : ∀ w, 0 ≤ dp.prior w) :
    questionUtility dp acts cells
      = (∑ c ∈ cells, uValue dp acts c)
        - dp.value acts * (∑ c ∈ cells, dp.cellProbability c) := by
  unfold questionUtility
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (λ c _ => ?_)
  unfold utilityValue
  rw [mul_sub, cellProbability_mul_condValue_eq_uValue dp acts c hprior]
  ring

/-- **Question utility is monotone under partition refinement** — the `⟹` direction of
[van-rooy-2003]'s §4.1 Fact (p. 743), in full generality. A finer partition `fine`
(presented as a refinement of `coarse` via `assign`, with each coarse cell the disjoint
union of its fiber) has `EUV ≥` the coarser one. By [blackwell-1953]: post-processing the
finer experiment cannot raise the convex value. Generalizes `questionUtility_split_ge`. -/
theorem questionUtility_mono_of_refines [Fintype W] (dp : DecisionProblem K W A)
    (acts : Finset A) {fine coarse : Finset (Finset W)} (assign : Finset W → Finset W)
    (hmaps : ∀ f ∈ fine, assign f ∈ coarse)
    (hcover : ∀ c ∈ coarse, c = (fine.filter (λ f => assign f = c)).sup id)
    (hdisj : ∀ f₁ ∈ fine, ∀ f₂ ∈ fine, f₁ ≠ f₂ → Disjoint f₁ f₂)
    (hprior : ∀ w, 0 ≤ dp.prior w) :
    questionUtility dp acts coarse ≤ questionUtility dp acts fine := by
  have hfdisj : ∀ c ∈ coarse, ∀ f₁ ∈ fine.filter (λ f => assign f = c),
      ∀ f₂ ∈ fine.filter (λ f => assign f = c), f₁ ≠ f₂ → Disjoint f₁ f₂ :=
    λ c _ f₁ hf₁ f₂ hf₂ hne =>
      hdisj f₁ (Finset.mem_of_mem_filter _ hf₁) f₂ (Finset.mem_of_mem_filter _ hf₂) hne
  have hcell : ∑ c ∈ coarse, dp.cellProbability c
      = ∑ f ∈ fine, dp.cellProbability f := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (λ f => dp.cellProbability f)]
    refine Finset.sum_congr rfl (λ c hc => ?_)
    rw [← cellProbability_sup dp (hfdisj c hc)]
    exact congrArg dp.cellProbability (hcover c hc)
  have huv : ∑ c ∈ coarse, uValue dp acts c ≤ ∑ f ∈ fine, uValue dp acts f := by
    calc ∑ c ∈ coarse, uValue dp acts c
        = ∑ c ∈ coarse, uValue dp acts ((fine.filter (λ f => assign f = c)).sup id) :=
          Finset.sum_congr rfl (λ c hc => congrArg (uValue dp acts) (hcover c hc))
      _ ≤ ∑ c ∈ coarse, ∑ f ∈ fine.filter (λ f => assign f = c), uValue dp acts f :=
          Finset.sum_le_sum (λ c hc => uValue_sup_le dp acts (hfdisj c hc))
      _ = ∑ f ∈ fine, uValue dp acts f :=
          Finset.sum_fiberwise_of_maps_to hmaps (λ f => uValue dp acts f)
  rw [questionUtility_eq dp acts coarse hprior, questionUtility_eq dp acts fine hprior,
    hcell]
  linarith [huv]

end Refinement

/-! ### Maximin monotonicity

Security level and maximin value are antitone in the world set: restricting to a
subset can only improve worst-case guarantees. -/

section MaximinMono

omit [IsStrictOrderedRing K] in
/-- The security level is at most the utility of any world in the set. -/
theorem securityLevel_le_utility (dp : DecisionProblem K W A) (worlds : Finset W)
    (a : A) {w : W} (hw : w ∈ worlds) :
    dp.securityLevel worlds a ≤ dp.utility w a := by
  rw [securityLevel_of_nonempty ⟨w, hw⟩]
  exact Finset.inf'_le _ hw

omit [IsStrictOrderedRing K] in
/-- The security level is antitone in the world set: a min over fewer elements is
    at least the min over more. -/
theorem securityLevel_anti (dp : DecisionProblem K W A) {S₁ S₂ : Finset W} (a : A)
    (hne : S₁.Nonempty) (hsub : S₁ ⊆ S₂) :
    dp.securityLevel S₂ a ≤ dp.securityLevel S₁ a := by
  rw [securityLevel_of_nonempty hne, securityLevel_of_nonempty (hne.mono hsub)]
  exact Finset.inf'_mono _ hsub hne

omit [IsStrictOrderedRing K] in
/-- The maximin value is antitone in the world set. -/
theorem maximinValue_anti (dp : DecisionProblem K W A) {S₁ S₂ : Finset W}
    (actions : Finset A) (hne : S₁.Nonempty) (hsub : S₁ ⊆ S₂) :
    dp.maximinValue S₂ actions ≤ dp.maximinValue S₁ actions := by
  by_cases ha : actions.Nonempty
  · rw [maximinValue_of_nonempty ha, maximinValue_of_nonempty ha]
    exact Finset.sup'_mono_fun λ a _ => securityLevel_anti dp a hne hsub
  · rw [Finset.not_nonempty_iff_eq_empty.mp ha, maximinValue_empty, maximinValue_empty]

variable [DecidableEq W]

/-- Maximin utility value is antitone in the cell: learning a more specific
    proposition (subset of worlds) gives a higher MUV. -/
theorem maximinUtilityValue_anti (dp : DecisionProblem K W A) (worlds : Finset W)
    (actions : Finset A) {c₁ c₂ : Finset W} (hsub : c₁ ⊆ c₂)
    (hne : (worlds ∩ c₁).Nonempty) :
    dp.maximinUtilityValue worlds actions c₂ ≤
      dp.maximinUtilityValue worlds actions c₁ := by
  unfold maximinUtilityValue condMaximinValue
  have hsub' : worlds ∩ c₁ ⊆ worlds ∩ c₂ := Finset.inter_subset_inter_left hsub
  linarith [maximinValue_anti dp actions hne hsub']

/-- Maximin value of information is non-negative for nonempty cells: the maximin
    over `worlds ∩ c ⊆ worlds` considers fewer worst cases. -/
theorem maximinUtilityValue_nonneg (dp : DecisionProblem K W A) (worlds : Finset W)
    (actions : Finset A) (c : Finset W) (hne : (worlds ∩ c).Nonempty) :
    0 ≤ dp.maximinUtilityValue worlds actions c := by
  unfold maximinUtilityValue condMaximinValue
  linarith [maximinValue_anti dp actions hne Finset.inter_subset_left]

end MaximinMono

/-! ### List minimum helpers -/

section FoldlMin

variable {α : Type*}

omit [Field K] [IsStrictOrderedRing K] in
private lemma foldl_min_le_init (f : α → K) (xs : List α) (init : K) :
    xs.foldl (λ m x => min m (f x)) init ≤ init := by
  induction xs generalizing init with
  | nil => exact le_refl _
  | cons x xs ih => exact le_trans (ih _) (min_le_left _ _)

omit [Field K] [IsStrictOrderedRing K] in
private lemma foldl_min_le_of_mem (f : α → K) (xs : List α) (init : K)
    {x : α} (hx : x ∈ xs) :
    xs.foldl (λ m x => min m (f x)) init ≤ f x := by
  induction xs generalizing init with
  | nil => exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · show ys.foldl (λ m z => min m (f z)) (min init (f x)) ≤ f x
      exact le_trans (foldl_min_le_init _ _ _) (min_le_right _ _)
    · show ys.foldl (λ m z => min m (f z)) (min init (f y)) ≤ f x
      exact ih _ h

omit [IsStrictOrderedRing K] in
/-- The question maximin value is at most the MUV of each cell in the question. -/
theorem questionMaximin_le_maximinUtilityValue [DecidableEq W]
    (dp : DecisionProblem K W A) (worlds : Finset W) (actions : Finset A)
    (q : List (Finset W)) {cell : Finset W} (hcell : cell ∈ q) :
    questionMaximin dp worlds actions q ≤
      dp.maximinUtilityValue worlds actions cell := by
  cases q with
  | nil => exact absurd hcell List.not_mem_nil
  | cons c cs =>
    simp only [questionMaximin]
    rcases List.mem_cons.mp hcell with rfl | h
    · exact foldl_min_le_init _ _ _
    · exact foldl_min_le_of_mem _ _ _ h

end FoldlMin

/-! ### Special decision problems -/

/-- An epistemic DP where the agent wants to know the exact world state. -/
def epistemic [DecidableEq W] (target : W) : DecisionProblem K W A where
  utility w _ := if w = target then 1 else 0
  prior _ := 1

/-- A complete-information DP where only exact-state knowledge is useful. -/
def completeInformation [DecidableEq W] : DecisionProblem K W W where
  utility w a := if a = w then 1 else 0
  prior _ := 1

/-- A mention-some DP: any satisfier resolves the problem. -/
def mentionSome (satisfies : W → Prop) [DecidablePred satisfies] :
    DecisionProblem K W Bool where
  utility w a := if a ∧ satisfies w then 1 else 0
  prior _ := 1

/-! ### Binary question value decomposition

For a binary partition `{P, ¬P}`, the probability-weighted sum of conditional
DP values equals Van Rooy's question utility plus the baseline DP value.
This is the structural identity connecting "the value of asking a yes/no
question" to the decision-theoretic question framework of [van-rooy-2003]. -/

section BinaryQuestion

variable [Fintype W] [DecidableEq W]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Cell probabilities of a binary partition `{P, ¬P}` sum to `1` when the
    prior is a proper distribution. -/
theorem cellProbability_filter_add_filter_not (dp : DecisionProblem K W A)
    (P : W → Prop) [DecidablePred P] (hPrior : Finset.univ.sum dp.prior = 1) :
    dp.cellProbability (Finset.univ.filter P) +
      dp.cellProbability (Finset.univ.filter (¬ P ·)) = 1 := by
  unfold cellProbability
  rw [← Finset.sum_union (Finset.disjoint_filter_filter_not _ _ P),
    Finset.filter_union_filter_not_eq P Finset.univ, hPrior]

/-- **Binary question value decomposition**: for a binary partition `{P, ¬P}`,

        `∑ P(cell) · V(D|cell) = EUV({P, ¬P}, D) + V(D)`

    where the LHS is the probability-weighted sum of conditional DP values,
    `EUV` is `questionUtility`, and `V(D)` is `value`. -/
theorem binary_question_value_decomposition (dp : DecisionProblem K W A)
    (actions : Finset A) (P : W → Prop) [DecidablePred P]
    (hPrior : Finset.univ.sum dp.prior = 1) :
    dp.cellProbability (Finset.univ.filter P) *
        dp.condValue actions (Finset.univ.filter P) +
      dp.cellProbability (Finset.univ.filter (¬ P ·)) *
        dp.condValue actions (Finset.univ.filter (¬ P ·)) =
    questionUtility dp actions
        {Finset.univ.filter P, Finset.univ.filter (¬ P ·)} +
      dp.value actions := by
  have hSum := cellProbability_filter_add_filter_not dp P hPrior
  have ⟨w₀⟩ : Nonempty W := by
    by_contra h; rw [not_nonempty_iff] at h; simp [Finset.univ_eq_empty] at hPrior
  have hne : Finset.univ.filter P ≠ Finset.univ.filter (¬ P ·) := by
    intro heq
    by_cases hp : P w₀
    · have : w₀ ∈ Finset.univ.filter P := by simp [hp]
      rw [heq] at this; simp [hp] at this
    · have : w₀ ∈ Finset.univ.filter (¬ P ·) := by simp [hp]
      rw [← heq] at this; simp [hp] at this
  simp only [questionUtility, utilityValue, Finset.sum_pair hne]
  linarith [show dp.cellProbability (Finset.univ.filter P) * dp.value actions +
      dp.cellProbability (Finset.univ.filter (¬ P ·)) * dp.value actions
      = dp.value actions from by rw [← add_mul, hSum, one_mul]]

end BinaryQuestion

end DecisionProblem

end Core.DecisionTheory
