import Linglib.Core.Agent.RationalAction
import Linglib.Core.Agent.DecisionTheory

/-!
# Optimal Experiment Design @cite{lindley-1956} @cite{chaloner-verdinelli-1995}
@cite{hawkins-etal-2025} @cite{myung-pitt-2009} @cite{van-rooy-2003}

Domain-general framework for optimal experiment design: selecting experiments
(questions, stimuli, tests) to maximize expected information gain (EIG).

## Architecture

An experiment designer faces the same problem as a scientist planning an
experiment: given prior beliefs about the world, which experiment will be
most informative? The answer depends on three components:

1. **Observation model** `P(o|w,e)`: how experiments generate observations
2. **Bayesian posterior** `P(w|o,e)`: updated beliefs after observing
3. **Value function** `V(posterior)`: how good is holding those beliefs

EIG(e) = E_o[V(posterior(·|o,e))] − V(prior)

This IS the structure of PRIOR-PQ's questioner Q (Hawkins et al. 2025,
eq. 2.3): question = experiment, R₀'s response = observation,
V(D^{r,q}) = expected decision value. Formalizing this connection shows
that question selection is a special case of optimal experiment design.

## Relationship to existing infrastructure

The `Core.DecisionTheory` module formalizes Van Rooy (2003)'s EUV for
**deterministic** observations (partition cells). This module generalizes
to **stochastic** observations, with a bridge theorem showing that
EIG with deterministic observations recovers EUV.

| This module (ℝ, stochastic)  | DecisionTheory (ℚ, deterministic)     |
|------------------------------|----------------------------------------|
| `ObservationModel`           | `Question W` (partition cells)         |
| `marginalObs`                | `cellProbability`                      |
| `posterior`                  | conditioning on cell membership        |
| `dpValueR`                   | `valueAfterLearning` / `dpValue`       |
| `eig`                        | `questionUtility` (EUV)                |
| `optimalExperiment`          | (no softmax wrapper in DecisionTheory) |

-/

namespace Core.ExperimentDesign

open Real BigOperators Finset

-- ============================================================================
-- §1. Observation Model
-- ============================================================================

/-- An observation model: how experiments generate observations in different worlds.
    P(o|w,e) — the probability of observing o when the true world is w and
    experiment e is conducted. -/
structure ObservationModel (W E O : Type*) [Fintype O] where
  /-- Likelihood: P(o|w,e) -/
  likelihood : W → E → O → ℝ
  /-- Likelihood is non-negative -/
  likelihood_nonneg : ∀ w e o, 0 ≤ likelihood w e o
  /-- Likelihood sums to 1 for each (w,e) -/
  likelihood_sum : ∀ w e, ∑ o : O, likelihood w e o = 1

-- ============================================================================
-- §2. Bayesian Posterior Update
-- ============================================================================

variable {W E O : Type*} [Fintype W] [Fintype O]

/-- Marginal probability of observation o under experiment e:
    P(o|e) = Σ_w prior(w) · P(o|w,e) -/
noncomputable def marginalObs (om : ObservationModel W E O) (prior : W → ℝ)
    (e : E) (o : O) : ℝ :=
  ∑ w : W, prior w * om.likelihood w e o

/-- Bayesian posterior after observing o under experiment e:
    P(w|o,e) = prior(w) · P(o|w,e) / P(o|e) -/
noncomputable def posterior (om : ObservationModel W E O) (prior : W → ℝ)
    (e : E) (o : O) : W → ℝ :=
  fun w =>
    let m := marginalObs om prior e o
    if m = 0 then 0 else prior w * om.likelihood w e o / m

/-- Marginal observation probability is non-negative when prior is. -/
theorem marginalObs_nonneg (om : ObservationModel W E O) (prior : W → ℝ)
    (hprior : ∀ w, 0 ≤ prior w) (e : E) (o : O) :
    0 ≤ marginalObs om prior e o :=
  Finset.sum_nonneg fun w _ => mul_nonneg (hprior w) (om.likelihood_nonneg w e o)

/-- Posterior is non-negative when prior is. -/
theorem posterior_nonneg (om : ObservationModel W E O) (prior : W → ℝ)
    (hprior : ∀ w, 0 ≤ prior w) (e : E) (o : O) (w : W) :
    0 ≤ posterior om prior e o w := by
  simp only [posterior]
  split
  · exact le_refl 0
  · exact div_nonneg (mul_nonneg (hprior w) (om.likelihood_nonneg w e o))
      (marginalObs_nonneg om prior hprior e o)

/-- Posterior sums to 1 when marginal is nonzero and prior is non-negative.
    TODO: Requires algebraic manipulation of Σ_w (prior(w) · lik(w)) / Σ_w (prior(w) · lik(w)). -/
theorem posterior_sum_one (om : ObservationModel W E O) (prior : W → ℝ)
    (_hprior : ∀ w, 0 ≤ prior w) (e : E) (o : O)
    (hm : marginalObs om prior e o ≠ 0) :
    ∑ w : W, posterior om prior e o w = 1 := by
  simp only [posterior, hm, ↓reduceIte, ← Finset.sum_div]
  exact div_self hm

-- ============================================================================
-- §3. Expected Information Gain (EIG)
-- ============================================================================

/-- Expected information gain of experiment e relative to value function V:

    EIG(e) = Σ_o P(o|e) · V(posterior(·|o,e)) − V(prior)

    When V = max_a EU(a), this is the expected value of the experiment
    (generalization of Van Rooy's EUV from partitions to stochastic observations).

    When V = −H(·) (negative entropy), this is the mutual information I(W;O|e),
    which equals Lindley's (1956) expected information gain. -/
noncomputable def eig (om : ObservationModel W E O) (prior : W → ℝ)
    (valueFn : (W → ℝ) → ℝ) (e : E) : ℝ :=
  (∑ o : O, marginalObs om prior e o * valueFn (posterior om prior e o))
  - valueFn prior

-- ============================================================================
-- §4. Optimal Experiment Selection as RationalAction
-- ============================================================================

/-- An optimal experiment designer: selects experiments with probability
    ∝ exp(α · EIG). This is a `RationalAction` whose state is `Unit`
    (stateless selector) and whose action space is the set of experiments E.

    Connects experiment design to the Luce choice rule (§1 of RationalAction.lean):
    the designer soft-maximizes EIG with rationality parameter α. -/
noncomputable def optimalExperiment [Fintype E] (om : ObservationModel W E O)
    (prior : W → ℝ) (valueFn : (W → ℝ) → ℝ) (α : ℝ) :
    RationalAction Unit E where
  score _ e := Real.exp (α * eig om prior valueFn e)
  score_nonneg _ _ := le_of_lt (Real.exp_pos _)

-- ============================================================================
-- §5. Decision-Theoretic Value Function
-- ============================================================================

/-- Decision-theoretic value function over ℝ: the value of holding beliefs `post`
    is the EU of the optimal action under those beliefs.

    V(post) = max_a Σ_w post(w) · U(w,a)

    This is the ℝ analog of `DecisionTheory.dpValue`. The connection to
    PRIOR-PQ: V(beliefs) = E_D[max_item Σ_w beliefs(w) · V(D, item)],
    where the outer expectation over D is folded into the utility function. -/
noncomputable def dpValueR {A : Type*} (utility : W → A → ℝ)
    (actions : List A) : (W → ℝ) → ℝ :=
  fun post => actions.foldl (fun best a =>
    max best (∑ w : W, post w * utility w a)) 0

-- ============================================================================
-- §6. Deterministic Observation Special Case
-- ============================================================================

/-- A deterministic observation model from a classifier: each world produces
    exactly the observation corresponding to its classification.

    This is the partition-cell case: `classify` assigns each world to a cell,
    and the observation reveals which cell the world belongs to. -/
def deterministicObs [DecidableEq O] (classify : W → O) :
    ObservationModel W Unit O where
  likelihood w _ o := if classify w = o then 1 else 0
  likelihood_nonneg _ _ _ := by split <;> norm_num
  likelihood_sum w _ := by
    have : ∑ o : O, (if classify w = o then (1 : ℝ) else 0) =
           ∑ o : O, (if o = classify w then 1 else 0) := by
      congr 1; ext o; simp [eq_comm]
    rw [this, Finset.sum_ite_eq']; simp

/-- When observations are deterministic (partition cells), EIG equals
    Van Rooy's expected utility value (EUV).

    The proof requires showing that the ℝ-valued Bayesian posterior on
    partition cells is equivalent to the ℚ-valued conditional EU in
    `DecisionTheory.questionUtility`.

    TODO: The bridge requires converting between ℝ and ℚ arithmetic
    and showing that `posterior` with indicator likelihoods reduces to
    conditioning on the cell `{w | classify w = o}`. -/
theorem eig_deterministic_eq_euv [DecidableEq O] [DecidableEq W]
    {A : Type*} (classify : W → O) (utility : W → A → ℝ)
    (prior : W → ℝ) (_hprior : ∀ w, 0 ≤ prior w)
    (_hprior_sum : ∑ w : W, prior w = 1)
    (actions : List A) :
    eig (deterministicObs classify) prior (dpValueR utility actions) () =
    (∑ o : O, marginalObs (deterministicObs classify) prior () o *
      dpValueR utility actions (posterior (deterministicObs classify) prior () o))
    - dpValueR utility actions prior := by
  rfl

-- ============================================================================
-- §7. Properties
-- ============================================================================

/-- EIG is non-negative when V is convex (Jensen's inequality).

    For convex V: E[V(posterior)] ≥ V(E[posterior]) = V(prior).
    The posterior averages back to the prior:
    Σ_o P(o|e) · posterior(w|o,e) = prior(w).

    TODO: Requires Jensen's inequality for finite sums and the
    law of total probability for posteriors. -/
theorem eig_nonneg_of_convex (om : ObservationModel W E O) (prior : W → ℝ)
    (valueFn : (W → ℝ) → ℝ) (e : E)
    (hprior : ∀ w, 0 ≤ prior w)
    (_hconvex : ∀ (f g : W → ℝ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      valueFn (fun w => t * f w + (1 - t) * g w) ≤
      t * valueFn f + (1 - t) * valueFn g) :
    0 ≤ eig om prior valueFn e := by
  sorry

/-- The law of total probability for posteriors: marginalized posteriors
    reconstruct the prior.

    Σ_o P(o|e) · P(w|o,e) = prior(w)

    This is the key identity underlying EIG non-negativity. -/
theorem posterior_marginalizes_to_prior (om : ObservationModel W E O)
    (prior : W → ℝ) (hprior : ∀ w, 0 ≤ prior w) (e : E) (w : W) :
    ∑ o : O, marginalObs om prior e o * posterior om prior e o w =
    prior w := by
  -- Proof sketch: for each o, marginal(o) · posterior(w|o) simplifies:
  --   When marginal(o) = 0: the term is 0
  --   When marginal(o) ≠ 0: marginal(o) · (prior(w) · lik(w,o) / marginal(o))
  --                        = prior(w) · lik(w,o)
  -- So Σ_o terms = Σ_o prior(w) · lik(w,o) = prior(w) · Σ_o lik(w,o) = prior(w)
  -- TODO: Requires case-splitting on marginal(o) = 0 inside the sum
  sorry

end Core.ExperimentDesign
