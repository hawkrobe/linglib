import Linglib.Core.Agent.RationalAction
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Luce (1959) Chapter 4: Learning @cite{luce-1959}

Luce extends the choice axiom to dynamic settings where choice probabilities
change over trials via learning and reinforcement. The central question: if
the Luce choice rule (IIA) holds at trial n, does it hold at trial n+1 after
a learning update?

## Architecture

The key result (§4.B) is that the Luce rule is *closed under positive linear
transformations* of the ratio scale values. Since the linear learning model
(§4.A) is exactly such a transformation, IIA is preserved across learning
trials. This is structurally guaranteed in our formalization: `LinearLearner.update`
produces a new `RationalAction`, and `RationalAction` *is* the Luce choice rule.

We also formalize:

1. **Linear learning model** (§4.A): `v_{n+1}(a) = α·v_n(a) + (1-α)·r(a)`
2. **Axiom 1 preservation** (§4.B): `update` yields a `RationalAction` — IIA by construction
3. **β-model** (§4.C): probability-space learning `P_{n+1}(a) = (1-β)·P_n(a) + β·δ(a, chosen)`
4. **Iteration** (§4.D): n-fold application of the linear update
5. **Convergence** (§4.E): under constant reinforcement, `v_n(a) → r(a)` as `n → ∞`

## References

- Luce, R. D. (1959). Individual Choice Behavior (Vol. 4). Wiley. Chapter 4, pp. 113–128.
- Bush, R. R. & Mosteller, F. (1955). Stochastic Models for Learning. Wiley.
-/

namespace Core

open BigOperators Finset Filter

-- ============================================================================
-- §1. Linear Learning Model (§4.A)
-- ============================================================================

/-- A linear learner for the Luce ratio-scale model (Luce 1959, §4.A).

The learning rule is a positive linear operator on ratio-scale values:
`v_{n+1}(a) = α · v_n(a) + (1-α) · r(a)` where `α ∈ (0,1)` is the retention
rate and `r : A → ℝ` is the reinforcement function. The key property is that
this is a *positive linear* transformation — it maps non-negative scores to
non-negative scores — which is exactly what Luce's Axiom 1 preservation
(§4.B) requires. -/
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

-- ============================================================================
-- §2. Linear Update & Axiom 1 Preservation (§4.A–B)
-- ============================================================================

/-- One step of linear learning (Luce 1959, §4.A):
`v_{n+1}(s, a) = α · v_n(s, a) + (1 - α) · r(a)`.

The result is a new `RationalAction`, so the Luce choice rule (IIA) holds at
trial n+1 by construction — this is the content of §4.B. -/
def LinearLearner.update (ll : LinearLearner A) (ra : RationalAction S A) :
    RationalAction S A where
  score := λ s a => ll.learnRate * ra.score s a + ll.complementRate * ll.reinforcement a
  score_nonneg := λ s a => by
    apply add_nonneg
    · exact mul_nonneg (le_of_lt ll.learnRate_pos) (ra.score_nonneg s a)
    · exact mul_nonneg (le_of_lt ll.complementRate_pos) (ll.reinforcement_nonneg a)

/-- Updated scores are non-negative — a direct consequence of the positivity of α,
(1-α), the original scores, and the reinforcement values. This is what makes the
linear learning model a *positive* linear operator (Luce 1959, §4.B). -/
theorem linear_update_nonneg (ll : LinearLearner A) (ra : RationalAction S A)
    (s : S) (a : A) : 0 ≤ (ll.update ra).score s a :=
  (ll.update ra).score_nonneg s a

/-- **Axiom 1 preservation** (Luce 1959, §4.B, Theorem 17):

If the Luce choice rule P(a) = v(a)/Σv(b) holds at trial n, then after a
positive linear update v' = α·v + (1-α)·r, the updated rule
P'(a) = v'(a)/Σv'(b) is again a Luce choice rule.

In our formalization this is true *by construction*: `LinearLearner.update`
produces a `RationalAction`, and `RationalAction.policy` *is* the Luce rule.
We state this as an explicit equational theorem for clarity. -/
theorem linear_learning_preserves_axiom1 (ll : LinearLearner A) (ra : RationalAction S A)
    (s : S) (a : A) :
    (ll.update ra).policy s a =
      if (ll.update ra).totalScore s = 0 then 0
      else (ll.update ra).score s a / (ll.update ra).totalScore s := by
  rfl

-- ============================================================================
-- §3. β-Model (§4.C)
-- ============================================================================

/-- The β-model (Luce 1959, §4.C; Bush & Mosteller 1955):

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

/-- One step of β-model update (Luce 1959, §4.C):
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

-- ============================================================================
-- §4. Iteration of Linear Learning (§4.D)
-- ============================================================================

/-- n-step iteration of linear learning (Luce 1959, §4.D):

Apply the linear update rule n times starting from an initial `RationalAction`.
At each step, Axiom 1 is preserved because `update` produces a `RationalAction`. -/
def iterate_linear (ll : LinearLearner A) (ra : RationalAction S A) :
    ℕ → RationalAction S A
  | 0 => ra
  | n + 1 => ll.update (iterate_linear ll ra n)

/-- After n iterations, scores are still non-negative. Follows by induction
since each `update` step preserves non-negativity. -/
theorem iterate_linear_nonneg (ll : LinearLearner A) (ra : RationalAction S A)
    (n : ℕ) (s : S) (a : A) :
    0 ≤ (iterate_linear ll ra n).score s a :=
  (iterate_linear ll ra n).score_nonneg s a

/-- Closed-form for iterated linear learning (Luce 1959, §4.D):

After n iterations with retention rate α and reinforcement r:
`v_n(s, a) = α^n · v_0(s, a) + (1 - α^n) · r(a)`

This is the geometric-series solution to the linear recurrence. -/
theorem iterate_linear_closed_form (ll : LinearLearner A) (ra : RationalAction S A)
    (n : ℕ) (s : S) (a : A) :
    (iterate_linear ll ra n).score s a =
      ll.learnRate ^ n * ra.score s a +
        (1 - ll.learnRate ^ n) * ll.reinforcement a := by
  induction n with
  | zero => simp only [iterate_linear, pow_zero, one_mul, sub_self, zero_mul, add_zero]
  | succ n ih =>
    simp only [iterate_linear, LinearLearner.update, LinearLearner.complementRate]
    rw [ih]
    ring

-- ============================================================================
-- §5. Asymptotic Convergence (§4.E)
-- ============================================================================

/-- **Convergence of linear learning** (Luce 1959, §4.E):

Under constant reinforcement, the ratio-scale values converge to the
reinforcement values: `v_n(s, a) → r(a)` as `n → ∞`.

This follows from the closed form: `v_n = α^n · v_0 + (1 - α^n) · r`, and
`α^n → 0` since `0 < α < 1`. -/
-- TODO: Prove via `iterate_linear_closed_form` + `tendsto_pow_atTop_nhds_zero_of_lt_one`
-- from Mathlib. The key steps are:
--   1. Rewrite using `iterate_linear_closed_form`
--   2. Apply `Filter.Tendsto.add` and `Filter.Tendsto.mul`
--   3. Use `tendsto_pow_atTop_nhds_zero_of_lt_one` for `α^n → 0`
theorem linear_convergence (ll : LinearLearner A) (ra : RationalAction S A)
    (s : S) (a : A) :
    Tendsto (λ n => (iterate_linear ll ra n).score s a)
      atTop (nhds (ll.reinforcement a)) := by
  sorry

-- ============================================================================
-- §6. Expected Choice Sequences (§4.D–E)
-- ============================================================================

/-- A record of a learning trial: what was available, what was chosen, what
was the reinforcement. Used for analyzing sequences of choices over trials
(Luce 1959, §4.D–E). -/
structure TrialRecord (A : Type*) where
  /-- The action chosen on this trial. -/
  chosen : A
  /-- The reinforcement received (may differ from the learner's default). -/
  reinforcement : A → ℝ

/-- An expected choice sequence: the initial agent, a learner, and a history
of trials. This structure supports analyzing how choice probabilities evolve
over a sequence of reinforced trials (Luce 1959, §4.D–E). -/
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
  iterate_linear ecs.learner ecs.initial n

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

end Core
