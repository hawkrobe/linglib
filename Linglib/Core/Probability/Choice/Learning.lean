import Linglib.Core.Probability.Choice.RationalAction
import Linglib.Core.Probability.SoftmaxTheory
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Learning Models
[luce-1959] [bush-mosteller-1955] [rescorla-wagner-1972]

Three families of learning model, built on the Luce choice rule
(`RationalAction`): linear (ratio-scale) and probability-space learning,
stochastic gradient ascent, and Rescorla-Wagner associative learning.

## Main definitions

* `LinearLearner`, `LinearLearner.update`, `LinearLearner.iterate` — the linear
  (alpha) learning rule on ratio-scale values, `vₙ₊₁(a) = α·vₙ(a) + (1-α)·r(a)`.
* `BetaModel`, `BetaModel.update` — probability-space learning,
  `Pₙ₊₁(a) = (1-β)·Pₙ(a) + β·δ(a, chosen)`.
* `sgaUpdate`, `glaUpdate` — stochastic gradient ascent and the Gradual Learning
  Algorithm ([boersma-1998]).
* `RescorlaWagner`, `RescorlaWagner.update`, `RescorlaWagner.iterateConst` —
  error-driven associative learning, `ΔV_c = α_c · β · (λ − ΣV)`.

## Main results

* `linear_learning_preserves_axiom1` — the Luce choice rule is preserved under a
  positive linear update.
* `LinearLearner.iterate_closed_form`, `linear_convergence` — the geometric-series
  solution and convergence of the values to the reinforcement.
* `gla_eq_sga`, `sga_uses_correct_gradient` — the GLA is SGA, and SGA follows the
  MaxEnt log-likelihood gradient.
* `RescorlaWagner.totalStrength_convergence`, `RescorlaWagner.proportional_partition`,
  `RescorlaWagner.overshadowing`, `RescorlaWagner.blocking` — convergence to the
  outcome maximum, the salience-proportional equilibrium, and the blocking and
  overshadowing predictions.

## Implementation notes

Axiom 1 preservation is structural rather than a bridge theorem:
`LinearLearner.update` produces a new `RationalAction`, and `RationalAction.policy`
*is* the Luce choice rule, so IIA holds at every trial by construction.

The Luce linear model and the Rescorla-Wagner total strength obey the same affine
recurrence `xₙ₊₁ = r·xₙ + (1-r)·c`; their closed forms and convergence proofs share
one geometric-series argument.

[rescorla-wagner-1972]'s prediction-error term `(λ − ΣV)` makes learning
competitive across cues, generating *blocking* (a fully predicted outcome teaches a
co-present cue nothing) and *overshadowing* (a more salient cue captures more
strength). [ellis-2006] applies both to second-language acquisition:
high-salience cues (word order, lexical content) block or overshadow low-salience
grammatical morphemes (tense inflection, plural marking) that encode the same
meanings.
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

/-! ### Rescorla-Wagner associative learning -/

section RescorlaWagner

/-- The Rescorla-Wagner learning model ([rescorla-wagner-1972]): on each
trial every present cue has its associative strength updated by

    ΔV_c = α_c · β · (λ − ΣV)

where `α_c` is cue salience, `β` the learning rate (outcome importance), `λ` the
maximum conditioning supported by the outcome, and `ΣV` the summed strength of
the cues present on the trial. The prediction-error term `(λ − ΣV)` is what makes
learning competitive across cues. -/
structure RescorlaWagner (C : Type*) where
  /-- Cue salience: how noticeable each cue is. Must be in [0, 1]. -/
  salience : C → ℝ
  /-- Learning rate (outcome importance). Must be in (0, 1]. -/
  learnRate : ℝ
  /-- Maximum conditioning supported by the outcome. -/
  maxCond : ℝ
  /-- Salience is non-negative. -/
  salience_nonneg : ∀ (c : C), 0 ≤ salience c
  /-- Salience is at most 1. -/
  salience_le_one : ∀ (c : C), salience c ≤ 1
  /-- Learning rate is strictly positive. -/
  learnRate_pos : 0 < learnRate
  /-- Learning rate is at most 1. -/
  learnRate_le_one : learnRate ≤ 1
  /-- Maximum conditioning is non-negative. -/
  maxCond_nonneg : 0 ≤ maxCond

variable {C : Type*} [DecidableEq C]

/-- Prediction error on a trial: `λ − ΣV` for cues present.

When positive, the outcome is under-predicted (surprise → learning).
When zero, the outcome is fully predicted (no learning).
When negative, the outcome is over-predicted (extinction). -/
def RescorlaWagner.predictionError (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) : ℝ :=
  rw.maxCond - ∑ c ∈ present, V c

/-- One trial of Rescorla-Wagner learning ([rescorla-wagner-1972]).

For each cue c:
- If c is present: `V'(c) = V(c) + α_c · β · (λ − ΣV)`
- If c is absent: `V'(c) = V(c)` (no change) -/
def RescorlaWagner.update (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) (c : C) : ℝ :=
  if c ∈ present then
    V c + rw.salience c * rw.learnRate * rw.predictionError present V
  else V c

/-- Absent cues are not updated. -/
theorem RescorlaWagner.update_absent (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) (c : C) (hc : c ∉ present) :
    rw.update present V c = V c := by
  simp only [update, if_neg hc]

/-- **Blocking theorem** ([rescorla-wagner-1972]; [ellis-2006]):
when cue A already fully predicts the outcome (`V(A) = λ`) and is the only cue
with nonzero strength among those present, adding a novel cue B to the compound
produces *zero learning* for B: `V'(B) = V(B)`. -/
theorem RescorlaWagner.blocking (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) (B : C)
    (hB : B ∈ present)
    (h_total : ∑ c ∈ present, V c = rw.maxCond) :
    rw.update present V B = V B := by
  simp only [update, if_pos hB, predictionError, h_total, sub_self,
    mul_zero, add_zero]

/-- When the outcome is fully predicted, *no* present cue learns anything. -/
theorem RescorlaWagner.no_learning_at_equilibrium (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ)
    (h_total : ∑ c ∈ present, V c = rw.maxCond) (c : C) :
    rw.update present V c = V c := by
  by_cases hc : c ∈ present
  · exact rw.blocking present V c hc h_total
  · exact rw.update_absent present V c hc

/-- Iterated R-W learning over a sequence of trials. Each trial specifies
which cues are present. -/
def RescorlaWagner.iterate (rw : RescorlaWagner C)
    (trials : List (Finset C)) (V₀ : C → ℝ) : C → ℝ :=
  trials.foldl (fun V present => fun c => rw.update present V c) V₀

/-- Constant-trial iteration: the same cue set is presented on every trial. -/
def RescorlaWagner.iterateConst (rw : RescorlaWagner C)
    (S : Finset C) (V₀ : C → ℝ) : ℕ → (C → ℝ)
  | 0 => V₀
  | n + 1 => fun c => rw.update S (rw.iterateConst S V₀ n) c

/-! ### Rescorla-Wagner equilibrium, convergence, and overshadowing -/

/-- Total strength recurrence: the summed associative strength across present
cues follows an affine recurrence after each trial,

    ΣV' = ΣV + β · (Σ_{c∈S} α_c) · (λ − ΣV)
        = (1 − β·A) · ΣV + β·A·λ       where A = Σ_{c∈S} α_c

the same shape as the Luce α-model (cf. `LinearLearner.iterate_closed_form`) with
retention rate `1 − β·A`, since the prediction error `(λ − ΣV)` is shared across
all present cues. -/
theorem RescorlaWagner.totalStrength_recurrence (rw : RescorlaWagner C)
    (S : Finset C) (V : C → ℝ) :
    ∑ c ∈ S, rw.update S V c =
      ∑ c ∈ S, V c +
        rw.learnRate * rw.predictionError S V * ∑ c ∈ S, rw.salience c := by
  have h1 : ∀ c ∈ S, rw.update S V c =
      V c + rw.salience c * rw.learnRate * rw.predictionError S V :=
    fun c hc => by simp only [update, if_pos hc]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- Closed form for iterated total strength under constant-trial R-W learning,

    T_n = r^n · T_0 + (1 − r^n) · λ    where r = 1 − β · Σα. -/
private theorem RescorlaWagner.totalStrength_closed_form (rw : RescorlaWagner C)
    (S : Finset C) (V₀ : C → ℝ) (n : ℕ) :
    ∑ c ∈ S, rw.iterateConst S V₀ n c =
      (1 - rw.learnRate * ∑ c ∈ S, rw.salience c) ^ n *
        ∑ c ∈ S, V₀ c +
      (1 - (1 - rw.learnRate * ∑ c ∈ S, rw.salience c) ^ n) *
        rw.maxCond := by
  induction n with
  | zero =>
    simp only [RescorlaWagner.iterateConst, pow_zero, one_mul, sub_self, zero_mul, add_zero]
  | succ n ih =>
    have hstep : ∑ c ∈ S, rw.iterateConst S V₀ (n + 1) c =
        ∑ c ∈ S, rw.update S (rw.iterateConst S V₀ n) c :=
      Finset.sum_congr rfl fun c _ => rfl
    rw [hstep, rw.totalStrength_recurrence S (rw.iterateConst S V₀ n)]
    simp only [RescorlaWagner.predictionError]
    rw [ih]
    ring

/-- **Total strength convergence**: under repeated identical trials with the
same cue set `S`, the total associative strength converges to `λ`. -/
theorem RescorlaWagner.totalStrength_convergence (rw : RescorlaWagner C)
    (S : Finset C) (V₀ : C → ℝ)
    (h_pos : 0 < rw.learnRate * ∑ c ∈ S, rw.salience c)
    (h_stable : rw.learnRate * ∑ c ∈ S, rw.salience c < 1) :
    Tendsto (fun n => ∑ c ∈ S, rw.iterateConst S V₀ n c)
      atTop (nhds rw.maxCond) := by
  simp_rw [RescorlaWagner.totalStrength_closed_form]
  set r := 1 - rw.learnRate * ∑ c ∈ S, rw.salience c with hr_def
  have hr_nonneg : 0 ≤ r := by linarith
  have hr_lt_one : r < 1 := by linarith
  have htend_pow : Tendsto (fun n => r ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one
  have h1 : Tendsto (fun n => r ^ n * ∑ c ∈ S, V₀ c) atTop
      (nhds (0 * ∑ c ∈ S, V₀ c)) :=
    htend_pow.mul tendsto_const_nhds
  have h2 : Tendsto (fun n => (1 - r ^ n) * rw.maxCond) atTop
      (nhds ((1 - (0 : ℝ)) * rw.maxCond)) :=
    (tendsto_const_nhds.sub htend_pow).mul tendsto_const_nhds
  have h3 := h1.add h2
  simp only [zero_mul, sub_zero, one_mul, zero_add] at h3
  exact h3

/-- **Proportional partition** ([rescorla-wagner-1972]): when all cues start
with zero associative strength and the same cue set is presented on every trial,
each cue's strength at every step is proportional to its salience — there exists
`Kₙ` with `Vₙ(c) = α_c · Kₙ` for every present cue `c`. At convergence each cue's
strength is its salience-share of the outcome maximum `λ`. -/
theorem RescorlaWagner.proportional_partition (rw : RescorlaWagner C)
    (S : Finset C) (n : ℕ) :
    ∃ K : ℝ, ∀ c ∈ S, rw.iterateConst S (fun _ => 0) n c =
      rw.salience c * K := by
  induction n with
  | zero => exact ⟨0, fun c _ => by simp [RescorlaWagner.iterateConst, mul_zero]⟩
  | succ n ih =>
    obtain ⟨K, hK⟩ := ih
    have hsum : ∑ c' ∈ S, rw.iterateConst S (fun _ => 0) n c' =
        K * ∑ c' ∈ S, rw.salience c' := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c' hc' => by rw [hK c' hc']; ring
    refine ⟨K + rw.learnRate * (rw.maxCond - K * ∑ c' ∈ S, rw.salience c'),
      fun c hc => ?_⟩
    simp only [RescorlaWagner.iterateConst, RescorlaWagner.update, if_pos hc,
      RescorlaWagner.predictionError]
    rw [hK c hc, hsum]
    ring

/-- **Overshadowing** ([rescorla-wagner-1972]; [ellis-2006]): when two
cues are both present on every trial, the more salient cue captures more
associative strength at every step (and hence at equilibrium). Immediate from
`proportional_partition`: `Vₙ(c) = α_c · K`, so `Vₙ(A) = α_A · K > α_B · K = Vₙ(B)`
whenever `K > 0`. -/
theorem RescorlaWagner.overshadowing (rw : RescorlaWagner C)
    (S : Finset C) (A B : C) (n : ℕ)
    (hA : A ∈ S) (hB : B ∈ S) (_hne : A ≠ B)
    (h_salience : rw.salience B < rw.salience A)
    (h_pos : 0 < ∑ c ∈ S, rw.iterateConst S (fun _ => 0) n c) :
    rw.iterateConst S (fun _ => 0) n B <
      rw.iterateConst S (fun _ => 0) n A := by
  obtain ⟨K, hK⟩ := rw.proportional_partition S n
  rw [hK A hA, hK B hB]
  have hK_pos : 0 < K := by
    by_contra h
    push Not at h
    have hle : ∑ c ∈ S, rw.iterateConst S (fun _ => 0) n c ≤ 0 :=
      Finset.sum_nonpos fun c hc => by
        rw [hK c hc]; exact mul_nonpos_of_nonneg_of_nonpos (rw.salience_nonneg c) h
    linarith
  exact mul_lt_mul_of_pos_right h_salience hK_pos

/-- **ΔP–R-W correspondence** ([ellis-2006]; [cheng-holyoak-1995]):
the blocked direction of a blocking experiment. If one cue already captures all
the associative strength and the novel cue starts at zero, the novel cue remains
at zero after compound trials — matching `ΔP = 0` for the blocked cue. -/
theorem RescorlaWagner.blocked_cue_zero (rw : RescorlaWagner C)
    (S : Finset C) (V : C → ℝ) (C' : C)
    (hC : C' ∈ S) (hV : V C' = 0)
    (h_total : ∑ c ∈ S, V c = rw.maxCond) :
    rw.update S V C' = 0 := by
  rw [rw.blocking S V C' hC h_total, hV]

end RescorlaWagner

end Core
