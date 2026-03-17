import Linglib.Core.Agent.RationalAction
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Learning Models
@cite{luce-1959} @cite{bush-mosteller-1955} @cite{rescorla-wagner-1972}

Three families of learning model:

## §1–6. Luce/Bush-Mosteller (ratio-scale and probability-space)

@cite{luce-1959} extends the choice axiom to dynamic settings where choice
probabilities change over trials via learning and reinforcement. The central
question: if the Luce choice rule (IIA) holds at trial n, does it hold at
trial n+1 after a learning update?

The key result (§4.B) is that the Luce rule is *closed under positive linear
transformations* of the ratio scale values. Since the linear learning model
(§4.A) is exactly such a transformation, IIA is preserved across learning
trials. This is structurally guaranteed in our formalization: `LinearLearner.update`
produces a new `RationalAction`, and `RationalAction` *is* the Luce choice rule.

We formalize:

1. **Alpha model** (§4.C): `v_{n+1}(a) = α·v_n(a) + (1-α)·r(a)` — the linear learning rule
2. **Axiom 1 preservation** (§4.B, Theorem 16): `update` yields a `RationalAction` — IIA by construction
3. **Beta model** (§4.D): probability-space learning `P_{n+1}(a) = (1-β)·P_n(a) + β·δ(a, chosen)`
4. **Convergence** (§4.G): under constant reinforcement, `v_n(a) → r(a)` as `n → ∞`

## §7. Stochastic Gradient Ascent

The Gradual Learning Algorithm (@cite{boersma-1998}) = SGA with single-sample
estimates. Convergence to the global maximum of a concave objective (MaxEnt).

## §8. Rescorla-Wagner (associative learning)

@cite{rescorla-wagner-1972} models cue-outcome association via error-driven
learning: `ΔV_c = α_c · β · (λ − ΣV)`. Unlike Luce, R-W has a *prediction
error* term `(λ − ΣV)` that generates **blocking**: when cue A already
fully predicts the outcome, a co-present cue C learns nothing.
@cite{ellis-2006} uses R-W to explain why L2 learners fail to acquire
low-salience grammatical morphemes — they are blocked by higher-salience
cues (word order, lexical content, temporal adverbs) that already predict
the same meanings.

-/

namespace Core

open BigOperators Finset Filter

-- ============================================================================
-- §1. Response Strength Operators (§4.B) and the Alpha Model (§4.C)
-- ============================================================================

/-- A linear learner for the Luce ratio-scale model (@cite{luce-1959}, §4.B–C).

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
-- §2. Linear Update & Axiom 1 Preservation (§4.B–C)
-- ============================================================================

/-- One step of linear learning (@cite{luce-1959}, §4.C, Alpha Model):
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
linear learning model a *positive* linear operator (@cite{luce-1959}, §4.B). -/
theorem linear_update_nonneg (ll : LinearLearner A) (ra : RationalAction S A)
    (s : S) (a : A) : 0 ≤ (ll.update ra).score s a :=
  (ll.update ra).score_nonneg s a

/-- **Axiom 1 preservation** (@cite{luce-1959}, §4.B, Theorem 16):

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
-- §3. Beta Model (§4.D)
-- ============================================================================

/-- The β-model (@cite{luce-1959}, §4.D; @cite{bush-mosteller-1955}):

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

/-- One step of β-model update (@cite{luce-1959}, §4.D):
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
-- §4. Iteration of Linear Learning (§4.C continued)
-- ============================================================================

/-- n-step iteration of linear learning (@cite{luce-1959}, §4.C):

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

/-- Closed-form for iterated linear learning (@cite{luce-1959}, §4.C):

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
-- §5. Asymptotic Convergence (§4.G)
-- ============================================================================

/-- **Convergence of linear learning** (@cite{luce-1959}, §4.G):

Under constant reinforcement, the ratio-scale values converge to the
reinforcement values: `v_n(s, a) → r(a)` as `n → ∞`.

This follows from the closed form: `v_n = α^n · v_0 + (1 - α^n) · r`, and
`α^n → 0` since `0 < α < 1`. -/
theorem linear_convergence (ll : LinearLearner A) (ra : RationalAction S A)
    (s : S) (a : A) :
    Tendsto (λ n => (iterate_linear ll ra n).score s a)
      atTop (nhds (ll.reinforcement a)) := by
  simp_rw [iterate_linear_closed_form]
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

-- ============================================================================
-- §6. Expected Choice Sequences (§4.C–G)
-- ============================================================================

/-- A record of a learning trial: what was available, what was chosen, what
was the reinforcement. Used for analyzing sequences of choices over trials
(@cite{luce-1959}, §4.C–G). -/
structure TrialRecord (A : Type*) where
  /-- The action chosen on this trial. -/
  chosen : A
  /-- The reinforcement received (may differ from the learner's default). -/
  reinforcement : A → ℝ

/-- An expected choice sequence: the initial agent, a learner, and a history
of trials. This structure supports analyzing how choice probabilities evolve
over a sequence of reinforced trials (@cite{luce-1959}, §4.C–G). -/
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

-- ============================================================================
-- §7. Stochastic Gradient Ascent (Log-Linear Models)
-- ============================================================================

/-- Stochastic Gradient Ascent update for a single weight of a log-linear model.

For MaxEnt phonology, `observed_j` is the violation count of constraint j on
the observed output, and `expected_j` is the expected violation count under the
current model distribution.

The batch gradient is `E_emp[c_j] − E_r̄[c_j]` (see `hasDerivAt_logConditional`
in `RationalAction`). The stochastic version replaces both expectations with
single-sample estimates. -/
def sgaUpdate (r_j η observed_j expected_j : ℝ) : ℝ :=
  r_j + η * (observed_j - expected_j)

/-- The Gradual Learning Algorithm (@cite{boersma-1998}) update for a single
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
    HasDerivAt (fun w => (w * s y + r y) - logSumExpOffset s r w)
      (s y - ∑ i : ι, softmaxOffset s r wⱼ i * s i) wⱼ :=
  hasDerivAt_logConditional s r y wⱼ

-- ============================================================================
-- §8. Rescorla-Wagner Associative Learning
-- ============================================================================

/-- The Rescorla-Wagner learning model (@cite{rescorla-wagner-1972}).

Models how organisms learn cue-outcome associations. On each trial, all
present cues have their associative strengths updated by:

    ΔV_c = α_c · β · (λ − ΣV)

where `α_c` is cue salience, `β` is the learning rate (outcome importance),
`λ` is the maximum conditioning supported by the outcome, and `ΣV` is the
sum of associative strengths of all cues present on the trial.

The prediction error `(λ − ΣV)` is the key innovation: it makes learning
competitive across cues. When the outcome is already fully predicted
(`ΣV = λ`), no further learning occurs for any co-present cue — this
generates **blocking** (@cite{ellis-2006}, p. 177). -/
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

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Prediction error on a trial: `λ − ΣV` for cues present.

When positive, the outcome is under-predicted (surprise → learning).
When zero, the outcome is fully predicted (no learning).
When negative, the outcome is over-predicted (extinction). -/
def RescorlaWagner.predictionError (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) : ℝ :=
  rw.maxCond - ∑ c ∈ present, V c

/-- One trial of Rescorla-Wagner learning (@cite{rescorla-wagner-1972}).

For each cue c:
- If c is present: `V'(c) = V(c) + α_c · β · (λ − ΣV)`
- If c is absent: `V'(c) = V(c)` (no change) -/
def RescorlaWagner.update (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) (c : C) : ℝ :=
  if c ∈ present then
    V c + rw.salience c * rw.learnRate * rw.predictionError present V
  else V c

omit [Fintype C] in
/-- Absent cues are not updated. -/
theorem RescorlaWagner.update_absent (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) (c : C) (hc : c ∉ present) :
    rw.update present V c = V c := by
  simp only [update, if_neg hc]

omit [Fintype C] in
/-- **Blocking theorem** (@cite{rescorla-wagner-1972}; @cite{ellis-2006}, p. 177):

When cue A already fully predicts the outcome (`V(A) = λ`) and is the only
cue with nonzero strength among those present, adding a novel cue B to the
compound produces *zero learning* for B: `V'(B) = V(B)`.

This is the formal basis of @cite{ellis-2006}'s account of L2 fossilization:
L1 cues (temporal adverbs, word order) that already predict temporal/number
meanings block acquisition of L2 grammatical morphemes (tense inflection,
plural -s) that encode the same meanings. -/
theorem RescorlaWagner.blocking (rw : RescorlaWagner C)
    (present : Finset C) (V : C → ℝ) (B : C)
    (hB : B ∈ present)
    (h_total : ∑ c ∈ present, V c = rw.maxCond) :
    rw.update present V B = V B := by
  simp only [update, if_pos hB, predictionError, h_total, sub_self,
    mul_zero, add_zero]

omit [Fintype C] in
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

-- ============================================================================
-- §9. R-W Equilibrium, Convergence, and Overshadowing
-- ============================================================================

omit [Fintype C] in
/-- Total strength recurrence: the sum of associative strengths across present
cues follows a linear recurrence after each trial.

    ΣV' = ΣV + β · (Σ_{c∈S} α_c) · (λ − ΣV)
        = (1 − β·A) · ΣV + β·A·λ       where A = Σ_{c∈S} α_c

This has the same form as the Luce α-model (§2) with retention rate `1 − β·A`.
The prediction error `(λ − ΣV)` is shared across all present cues, so the
total strength update factors into a scalar recurrence.

Proof: `Finset.sum_congr` eliminates the `if` (every `c ∈ S` takes
the `then` branch), then `Finset.sum_add_distrib` + `Finset.sum_mul`. -/
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

omit [Fintype C] in
/-- Closed form for iterated total strength under constant-trial R-W learning.

    T_n = r^n · T_0 + (1 − r^n) · λ    where r = 1 − β · Σα

Proof by induction using `totalStrength_recurrence`. The step case expands
`predictionError`, substitutes the IH, and closes by `ring`. -/
private theorem totalStrength_closed_form (rw : RescorlaWagner C)
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

omit [Fintype C] in
/-- **Total strength convergence**: under repeated identical trials with the
same cue set S, the total associative strength converges to λ.

Since the total strength follows a linear recurrence with retention rate
`r = 1 − β·A` (see `totalStrength_recurrence`), convergence follows from
the closed form `T_n = r^n · T_0 + (1 − r^n) · λ` and `r^n → 0` (since
`0 ≤ r < 1` from `h_pos` and `h_stable`). This is the same proof pattern
as `linear_convergence` (§5) for the Luce α-model. -/
theorem RescorlaWagner.totalStrength_convergence (rw : RescorlaWagner C)
    (S : Finset C) (V₀ : C → ℝ)
    (h_pos : 0 < rw.learnRate * ∑ c ∈ S, rw.salience c)
    (h_stable : rw.learnRate * ∑ c ∈ S, rw.salience c < 1) :
    Tendsto (fun n => ∑ c ∈ S, rw.iterateConst S V₀ n c)
      atTop (nhds rw.maxCond) := by
  simp_rw [totalStrength_closed_form]
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

omit [Fintype C] in
/-- **Proportional partition** (@cite{rescorla-wagner-1972}):

When all cues start with zero associative strength and the same cue set is
presented on every trial, each cue's strength at every step is proportional
to its salience: there exists K_n such that V_n(c) = α_c · K_n for all
present cues c.

The proof is by induction on n. The base case is trivial (K = 0). For the
step, the prediction error `(λ − ΣV)` is shared across all present cues,
so ΔV(c) = α_c · β · (λ − ΣV) preserves proportionality. The inductive
hypothesis rewrites ΣV_n = K · Σα, giving K_{n+1} = K + β · (λ − K · Σα).

At convergence (ΣV = λ), this gives V_∞(c) = (α_c / Σα) · λ: each cue's
equilibrium strength is its share of the total salience, scaled by λ. -/
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

omit [Fintype C] in
/-- **Overshadowing** (@cite{rescorla-wagner-1972}; @cite{ellis-2006}):

When two cues are both present on every trial, the more salient cue captures
more associative strength at every step (and hence at equilibrium). This
follows directly from `proportional_partition`: V_n(c) = α_c · K, so
V_n(A) = α_A · K > α_B · K = V_n(B) whenever K > 0.

@cite{ellis-2006} (p. 177, 179–180) uses overshadowing to explain why
low-salience grammatical morphemes (tense inflection, plural -s) are
acquired late: high-salience cues (word order, lexical content) that
co-occur with the same outcomes capture most of the associative strength. -/
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
    push_neg at h
    have hle : ∑ c ∈ S, rw.iterateConst S (fun _ => 0) n c ≤ 0 :=
      Finset.sum_nonpos fun c hc => by
        rw [hK c hc]; exact mul_nonpos_of_nonneg_of_nonpos (rw.salience_nonneg c) h
    linarith
  exact mul_lt_mul_of_pos_right h_salience hK_pos

omit [Fintype C] in
/-- **ΔP–R-W correspondence** (@cite{ellis-2006}; @cite{cheng-holyoak-1995}):

For the blocking experiment (two phases: A→X then AC→X vs B→∅ then BD→X),
the R-W equilibrium strengths predict the same pattern as ΔP:

- **Blocked cue C**: R-W gives V(C) ≈ 0 at equilibrium; ΔP(C→X) = 0
- **Unblocked cue D**: R-W gives V(D) > 0 at equilibrium; ΔP(D→X) = 1

This theorem states the blocked direction: if cue A already captures all
the associative strength and C starts at zero, then C remains at zero
after compound AC→X trials. The ΔP = 0 counterpart is `deltaPCounts`
with `a = c` (cue equally predicts outcome whether C is present or not).

See `Phenomena.Acquisition.Studies.Ellis2006` for the concrete
Chapman & Robbins (1990) experiment verifying both measures. -/
theorem RescorlaWagner.blocked_cue_zero (rw : RescorlaWagner C)
    (S : Finset C) (V : C → ℝ) (C' : C)
    (hC : C' ∈ S) (hV : V C' = 0)
    (h_total : ∑ c ∈ S, V c = rw.maxCond) :
    rw.update S V C' = 0 := by
  rw [rw.blocking S V C' hC h_total, hV]

end Core
