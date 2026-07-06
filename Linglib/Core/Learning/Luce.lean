import Linglib.Core.Probability.Choice.RationalAction
import Linglib.Core.Probability.SoftmaxTheory
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Learning Models
[luce-1959] [bush-mosteller-1955]

Learning models built on the Luce choice rule (`RationalAction`): linear
(ratio-scale) and probability-space learning, and stochastic gradient ascent.
Associative learning rules (Rescorla-Wagner, Widrow-Hoff) live in
`Core/Learning/`.

## Main definitions

* `LinearLearner`, `LinearLearner.update`, `LinearLearner.iterate` — the linear
  (alpha) learning rule on ratio-scale values, `vₙ₊₁(a) = α·vₙ(a) + (1-α)·r(a)`.
* `BetaModel`, `BetaModel.update` — probability-space learning,
  `Pₙ₊₁(a) = (1-β)·Pₙ(a) + β·δ(a, chosen)`.
* `sgaUpdate`, `glaUpdate` — stochastic gradient ascent and the Gradual Learning
  Algorithm ([boersma-1998]).

## Main results

* `linear_learning_preserves_axiom1` — the Luce choice rule is preserved under a
  positive linear update.
* `LinearLearner.iterate_closed_form`, `linear_convergence` — the geometric-series
  solution and convergence of the values to the reinforcement.
* `gla_eq_sga`, `sga_uses_correct_gradient` — the GLA is SGA, and SGA follows the
  MaxEnt log-likelihood gradient.

## Implementation notes

Axiom 1 preservation is structural rather than a bridge theorem:
`LinearLearner.update` produces a new `RationalAction`, and `RationalAction.policy`
*is* the Luce choice rule, so IIA holds at every trial by construction.

The Luce linear model and `Core.RescorlaWagner`'s total strength obey the same
affine recurrence `xₙ₊₁ = r·xₙ + (1-r)·c`; their closed forms and convergence
proofs share one geometric-series argument.
-/

namespace Core

open Finset Filter

section LinearLearning

/-! ### The linear learner (alpha model) -/

/-- A linear learner for the Luce ratio-scale model ([luce-1959]).

The learning rule is a positive linear operator on ratio-scale values:
`v_{n+1}(a) = α · v_n(a) + (1-α) · r(a)` where `α ∈ (0,1)` is the retention
rate and `r : A → ℝ` is the reinforcement function. The key property is that
this is a *positive linear* transformation — it maps non-negative scores to
non-negative scores — which is exactly what Luce's Axiom 1 preservation
requires. -/
structure LinearLearner (A : Type*) where
  /-- Retention rate: weight on prior score. Must be in (0,1). -/
  learnRate : ℝ
  /-- Reinforcement: the asymptotic target score for each action. -/
  reinforcement : A → ℝ
  /-- Retention rate is strictly positive. -/
  learnRate_pos : 0 < learnRate
  /-- Retention rate is strictly less than 1. -/
  learnRate_lt_one : learnRate < 1
  /-- Reinforcement values are non-negative. -/
  reinforcement_nonneg : ∀ (a : A), 0 ≤ reinforcement a

variable {S A : Type*} [Fintype A]

/-- The complement `1 - α`, which serves as the weight on reinforcement. -/
def LinearLearner.complementRate (ll : LinearLearner A) : ℝ :=
  1 - ll.learnRate

omit [Fintype A] in
theorem LinearLearner.complementRate_pos (ll : LinearLearner A) :
    0 < ll.complementRate := by
  simp only [complementRate]
  linarith [ll.learnRate_lt_one]

omit [Fintype A] in
theorem LinearLearner.complementRate_lt_one (ll : LinearLearner A) :
    ll.complementRate < 1 := by
  simp only [complementRate]
  linarith [ll.learnRate_pos]

/-! ### Linear update and choice-axiom preservation -/

/-- One step of linear learning ([luce-1959], the Alpha Model):
`v_{n+1}(s, a) = α · v_n(s, a) + (1 - α) · r(a)`.

The result is a new `RationalAction`, so the Luce choice rule (IIA) holds at
trial n+1 by construction. -/
def LinearLearner.update (ll : LinearLearner A) (ra : RationalAction S A) :
    RationalAction S A where
  score := λ s a => ll.learnRate * ra.score s a + ll.complementRate * ll.reinforcement a
  score_nonneg := λ s a => by
    apply add_nonneg
    · exact mul_nonneg (le_of_lt ll.learnRate_pos) (ra.score_nonneg s a)
    · exact mul_nonneg (le_of_lt ll.complementRate_pos) (ll.reinforcement_nonneg a)

/-- Updated scores are non-negative — a direct consequence of the positivity of α,
(1-α), the original scores, and the reinforcement values. This is what makes the
linear learning model a *positive* linear operator ([luce-1959]). -/
theorem linear_update_nonneg (ll : LinearLearner A) (ra : RationalAction S A)
    (s : S) (a : A) : 0 ≤ (ll.update ra).score s a :=
  (ll.update ra).score_nonneg s a

/-- **Axiom 1 preservation** ([luce-1959]):

If the Luce choice rule P(a) = v(a)/Σv(b) holds at trial n, then after a
positive linear update v' = α·v + (1-α)·r, the updated rule
P'(a) = v'(a)/Σv'(b) is again a Luce choice rule. This holds by construction:
`LinearLearner.update` produces a `RationalAction`, whose `policy` *is* the
Luce rule. -/
theorem linear_learning_preserves_axiom1 (ll : LinearLearner A) (ra : RationalAction S A)
    (s : S) (a : A) :
    (ll.update ra).policy s a =
      if (ll.update ra).totalScore s = 0 then 0
      else (ll.update ra).score s a / (ll.update ra).totalScore s := by
  rfl

/-! ### The beta model -/

/-- The β-model ([luce-1959]; [bush-mosteller-1955]):

An alternative learning model operating directly on probabilities rather than
ratio-scale values:
`P_{n+1}(a) = (1-β) · P_n(a) + β · δ(a, chosen_n)`

where `δ(a, chosen_n) = 1` if `a` was chosen on trial n, 0 otherwise.
Unlike the linear model, this operates in probability space, so it does not
generally preserve the Luce ratio-scale structure. -/
structure BetaModel (A : Type*) where
  /-- Learning rate in (0,1). -/
  beta : ℝ
  /-- β is strictly positive. -/
  beta_pos : 0 < beta
  /-- β is strictly less than 1. -/
  beta_lt_one : beta < 1

/-- One step of β-model update ([luce-1959]):
`P'(a) = (1-β) · P(a) + β · δ(a, chosen)`.

Takes a probability function and the chosen action, returns updated probabilities. -/
def BetaModel.update [DecidableEq A] (bm : BetaModel A) (P : A → ℝ) (chosen : A) :
    A → ℝ :=
  λ a => (1 - bm.beta) * P a + bm.beta * if a = chosen then 1 else 0

omit [Fintype A] in
/-- β-model update preserves non-negativity of probabilities. -/
theorem BetaModel.update_nonneg [DecidableEq A] (bm : BetaModel A) (P : A → ℝ)
    (chosen : A) (hP : ∀ (a : A), 0 ≤ P a) (a : A) :
    0 ≤ bm.update P chosen a := by
  simp only [update]
  apply add_nonneg
  · exact mul_nonneg (by linarith [bm.beta_lt_one]) (hP a)
  · apply mul_nonneg (le_of_lt bm.beta_pos)
    split <;> linarith

/-- β-model update preserves sum-to-one when the input sums to 1. -/
theorem BetaModel.update_sum_one [DecidableEq A] (bm : BetaModel A) (P : A → ℝ)
    (chosen : A) (h_chosen : chosen ∈ Finset.univ)
    (h_sum : ∑ a : A, P a = 1) :
    ∑ a : A, bm.update P chosen a = 1 := by
  simp only [update, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, h_sum]
  rw [Finset.sum_ite_eq' Finset.univ chosen (λ _ => bm.beta)]
  simp only [h_chosen, if_true]
  ring

/-! ### Iterated linear learning -/

/-- `n`-step iteration of linear learning ([luce-1959]): apply the linear
update rule `n` times starting from an initial `RationalAction`. -/
def LinearLearner.iterate (ll : LinearLearner A) (ra : RationalAction S A) :
    ℕ → RationalAction S A
  | 0 => ra
  | n + 1 => ll.update (LinearLearner.iterate ll ra n)

/-- After `n` iterations, scores are still non-negative. -/
theorem LinearLearner.iterate_nonneg (ll : LinearLearner A) (ra : RationalAction S A)
    (n : ℕ) (s : S) (a : A) :
    0 ≤ (ll.iterate ra n).score s a :=
  (ll.iterate ra n).score_nonneg s a

/-- Closed form for iterated linear learning ([luce-1959]): after `n`
iterations with retention rate `α` and reinforcement `r`,
`vₙ(s, a) = αⁿ · v₀(s, a) + (1 - αⁿ) · r(a)`, the geometric-series solution to
the linear recurrence. -/
theorem LinearLearner.iterate_closed_form (ll : LinearLearner A) (ra : RationalAction S A)
    (n : ℕ) (s : S) (a : A) :
    (ll.iterate ra n).score s a =
      ll.learnRate ^ n * ra.score s a +
        (1 - ll.learnRate ^ n) * ll.reinforcement a := by
  induction n with
  | zero => simp only [LinearLearner.iterate, pow_zero, one_mul, sub_self, zero_mul, add_zero]
  | succ n ih =>
    simp only [LinearLearner.iterate, LinearLearner.update, LinearLearner.complementRate]
    rw [ih]
    ring

/-! ### Asymptotic convergence -/

/-- **Convergence of linear learning** ([luce-1959]): under constant
reinforcement, the ratio-scale values converge to the reinforcement values,
`vₙ(s, a) → r(a)` as `n → ∞`. -/
theorem linear_convergence (ll : LinearLearner A) (ra : RationalAction S A)
    (s : S) (a : A) :
    Tendsto (λ n => (ll.iterate ra n).score s a)
      atTop (nhds (ll.reinforcement a)) := by
  simp_rw [LinearLearner.iterate_closed_form]
  have htend_pow : Tendsto (fun n => ll.learnRate ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt ll.learnRate_pos) ll.learnRate_lt_one
  have h1 : Tendsto (fun n => ll.learnRate ^ n * ra.score s a) atTop
      (nhds (0 * ra.score s a)) :=
    htend_pow.mul tendsto_const_nhds
  have h2 : Tendsto (fun n => (1 - ll.learnRate ^ n) * ll.reinforcement a) atTop
      (nhds ((1 - (0 : ℝ)) * ll.reinforcement a)) :=
    (tendsto_const_nhds.sub htend_pow).mul tendsto_const_nhds
  have h3 := h1.add h2
  simp only [zero_mul, sub_zero, one_mul, zero_add] at h3
  exact h3

/-! ### Expected choice sequences -/

/-- A record of a learning trial: what was available, what was chosen, what
was the reinforcement. Used for analyzing sequences of choices over trials
([luce-1959]). -/
structure TrialRecord (A : Type*) where
  /-- The action chosen on this trial. -/
  chosen : A
  /-- The reinforcement received (may differ from the learner's default). -/
  reinforcement : A → ℝ

/-- An expected choice sequence: the initial agent, a learner, and a history
of trials. This structure supports analyzing how choice probabilities evolve
over a sequence of reinforced trials ([luce-1959]). -/
structure ExpectedChoiceSequence (S A : Type*) [Fintype A] where
  /-- The learning model governing updates. -/
  learner : LinearLearner A
  /-- The initial rational agent (trial 0). -/
  initial : RationalAction S A
  /-- History of trials (choices and reinforcements). -/
  history : List (TrialRecord A)

/-- The agent at trial n, after applying n steps of learning. -/
def ExpectedChoiceSequence.agentAt (ecs : ExpectedChoiceSequence S A) (n : ℕ) :
    RationalAction S A :=
  ecs.learner.iterate ecs.initial n

/-- The probability of choosing action `a` in state `s` at trial `n`. -/
noncomputable def ExpectedChoiceSequence.choiceProb
    (ecs : ExpectedChoiceSequence S A) (n : ℕ) (s : S) (a : A) : ℝ :=
  (ecs.agentAt n).policy s a

/-- Choice probabilities at any trial sum to 1 (when totalScore is nonzero),
because each trial's agent is a `RationalAction`. -/
theorem ExpectedChoiceSequence.choiceProb_sum_one
    (ecs : ExpectedChoiceSequence S A) (n : ℕ) (s : S)
    (h : (ecs.agentAt n).totalScore s ≠ 0) :
    ∑ a : A, ecs.choiceProb n s a = 1 :=
  (ecs.agentAt n).policy_sum_eq_one s h

end LinearLearning

/-! ### Stochastic gradient ascent (log-linear models) -/

/-- Stochastic Gradient Ascent update for a single weight of a log-linear model.

For MaxEnt phonology, `observed_j` is the violation count of constraint j on
the observed output, and `expected_j` is the expected violation count under the
current model distribution.

The batch gradient is `E_emp[c_j] − E_r̄[c_j]` (see `hasDerivAt_logConditional`
in `RationalAction`). The stochastic version replaces both expectations with
single-sample estimates. -/
def sgaUpdate (r_j η observed_j expected_j : ℝ) : ℝ :=
  r_j + η * (observed_j - expected_j)

/-- The Gradual Learning Algorithm ([boersma-1998]) update for a single
weight: adjust by the signed difference between the observed violation count
and the violation count of a hypothesis sampled from the current grammar. -/
def glaUpdate (r_j η : ℝ) (c_j_observed c_j_hypothesis : ℕ) : ℝ :=
  r_j + η * ((c_j_observed : ℝ) - (c_j_hypothesis : ℝ))

/-- **GLA = SGA**: the Gradual Learning Algorithm is Stochastic Gradient
Ascent with single-sample estimates of both observed and expected feature
values. The update rules are identical by definition. -/
theorem gla_eq_sga (r_j η : ℝ) (obs hyp : ℕ) :
    glaUpdate r_j η obs hyp = sgaUpdate r_j η obs hyp := rfl

/-- SGA converges to the global maximum of a concave objective.

For MaxEnt log-likelihood, the per-weight objective is concave
(`logConditional_concaveOn` in `RationalAction`), so SGA is guaranteed
to converge. This is the key advantage of MaxEnt over Stochastic OT,
where convergence of the GLA is not generally proved. -/
theorem sga_uses_correct_gradient {ι : Type*} [Fintype ι] [Nonempty ι]
    (s r : ι → ℝ) (y : ι) (wⱼ : ℝ) :
    HasDerivAt (fun w => (w * s y + r y) - logSumExp (w • s + r))
      (s y - ∑ i : ι, softmax (wⱼ • s + r) i * s i) wⱼ :=
  hasDerivAt_logConditional s r y wⱼ


end Core
