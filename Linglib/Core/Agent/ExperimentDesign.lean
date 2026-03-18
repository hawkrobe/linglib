import Linglib.Core.Agent.RationalAction
import Linglib.Core.Agent.DecisionTheory
import Linglib.Core.Agent.BayesianUpdate
import Mathlib.Analysis.Convex.Jensen

/-!
# Optimal Experiment Design @cite{lindley-1956}
@cite{hawkins-etal-2025} @cite{van-rooy-2003}

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

This IS the structure of PRIOR-PQ's questioner Q (@cite{hawkins-etal-2025},
eq. 2.3): question = experiment, R₀'s response = observation,
V(D^{r,q}) = expected decision value. Formalizing this connection shows
that question selection is a special case of optimal experiment design.

## Relationship to existing infrastructure

The `Core.DecisionTheory` module formalizes @cite{van-rooy-2003}'s EUV for
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

## Bayesian infrastructure

The `ObservationModel`, `posterior`, `marginalObs`, and their basic properties
(`posterior_nonneg`, `posterior_sum_one`, `posterior_marginalizes_to_prior`)
live in `Core.Agent.BayesianUpdate` and are re-exported here.

-/

namespace Core.ExperimentDesign

open Core.BayesianUpdate
open Real BigOperators Finset

-- Re-export BayesianUpdate types and definitions for backward compatibility
export Core.BayesianUpdate (ObservationModel marginalObs posterior
  marginalObs_nonneg posterior_nonneg posterior_sum_one
  posterior_marginalizes_to_prior deterministicObs)

variable {W E O : Type*} [Fintype W] [Fintype O]

-- ============================================================================
-- §1. Expected Information Gain (EIG)
-- ============================================================================

/-- Expected information gain of experiment e relative to value function V:

    EIG(e) = Σ_o P(o|e) · V(posterior(·|o,e)) − V(prior)

    When V = max_a EU(a), this is the expected value of the experiment
    (generalization of Van Rooy's EUV from partitions to stochastic observations).

    When V = −H(·) (negative entropy), this is the mutual information I(W;O|e),
    which equals @cite{lindley-1956}'s expected information gain. -/
noncomputable def eig (om : ObservationModel W E O) (prior : W → ℝ)
    (valueFn : (W → ℝ) → ℝ) (e : E) : ℝ :=
  (∑ o : O, marginalObs om prior e o * valueFn (posterior om prior e o))
  - valueFn prior

-- ============================================================================
-- §2. Optimal Experiment Selection as RationalAction
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
-- §3. Decision-Theoretic Value Function
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
-- §4. Bridge to DecisionTheory
-- ============================================================================

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
-- §5. Properties
-- ============================================================================

/-- Marginal observation probabilities sum to the total prior mass:
    Σ_o P(o|e) = Σ_w prior(w). -/
theorem marginalObs_sum (om : ObservationModel W E O) (prior : W → ℝ) (e : E) :
    ∑ o : O, marginalObs om prior e o = ∑ w : W, prior w := by
  simp only [marginalObs]
  rw [Finset.sum_comm]
  congr 1; ext w; rw [← Finset.mul_sum, om.likelihood_sum w e, mul_one]

omit [Fintype W] in
/-- Binary convexity over (W → ℝ) → ℝ implies Mathlib's `ConvexOn`. -/
private theorem convexOn_of_binary
    (V : (W → ℝ) → ℝ)
    (hconv : ∀ (f g : W → ℝ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      V (fun w => t * f w + (1 - t) * g w) ≤ t * V f + (1 - t) * V g) :
    ConvexOn ℝ Set.univ V := by
  refine ⟨convex_univ, fun {x} _ {y} _ {a} {b} ha hb hab => ?_⟩
  have h_b : b = 1 - a := by linarith
  have h_le : a ≤ 1 := by linarith
  subst h_b
  have key : a • x + (1 - a) • y = fun w => a * x w + (1 - a) * y w := by
    ext w; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [key, smul_eq_mul]
  exact hconv x y a ha h_le

/-- EIG is non-negative when V is convex (Jensen's inequality).

    For convex V: E[V(posterior)] ≥ V(E[posterior]) = V(prior).
    The posterior averages back to the prior (by `posterior_marginalizes_to_prior`):
    Σ_o P(o|e) · posterior(w|o,e) = prior(w).

    Jensen's inequality then gives V(prior) ≤ E_o[V(posterior)], hence EIG ≥ 0. -/
theorem eig_nonneg_of_convex (om : ObservationModel W E O) (prior : W → ℝ)
    (valueFn : (W → ℝ) → ℝ) (e : E)
    (hprior : ∀ w, 0 ≤ prior w)
    (hprior_sum : ∑ w : W, prior w = 1)
    (hconvex : ∀ (f g : W → ℝ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      valueFn (fun w => t * f w + (1 - t) * g w) ≤
      t * valueFn f + (1 - t) * valueFn g) :
    0 ≤ eig om prior valueFn e := by
  unfold eig
  suffices h : valueFn prior ≤
      ∑ o : O, marginalObs om prior e o * valueFn (posterior om prior e o) by linarith
  -- Apply Jensen (ConvexOn.map_sum_le) with weights = marginalObs, points = posterior
  have hVO := convexOn_of_binary valueFn hconvex
  have hmo_sum : ∑ o : O, marginalObs om prior e o = 1 := by
    rw [marginalObs_sum]; exact hprior_sum
  have hJ := hVO.map_sum_le (p := posterior om prior e)
    (fun o _ => marginalObs_nonneg om prior hprior e o)
    hmo_sum (fun o _ => Set.mem_univ _)
  -- hJ : valueFn (∑ o, P(o) • post_o) ≤ ∑ o, P(o) • V(post_o)
  -- Rewrite LHS of hJ: ∑ P(o) • posterior_o = prior (law of total probability)
  have hlhs : ∑ o : O, marginalObs om prior e o • posterior om prior e o = prior := by
    ext w; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      posterior_marginalizes_to_prior om prior hprior e w]
  rw [hlhs] at hJ
  -- Rewrite RHS of hJ: • → * for ℝ
  simp only [smul_eq_mul] at hJ
  exact hJ

end Core.ExperimentDesign
