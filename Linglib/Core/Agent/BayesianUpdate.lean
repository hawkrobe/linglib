import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Linglib.Core.Probability.PMFPosterior

/-!
# Bayesian Observation Models and Posterior Update

The ergonomic `ℝ`-typed interface for finite Bayesian inference with
explicit experiment indexing. Provides the same algorithm as mathlib's
canonical `PMF.posterior` (`Core/Probability/PMFPosterior.lean`):
`P(w|o,e) = prior(w) · P(o|w,e) / Σ_w' prior(w') · P(o|w',e)`.

## Relationship to `PMF.posterior`

`PMF.posterior` is the canonical mathlib probability-theoretic primitive
(`κ : α → PMF β`, `μ : PMF α`, observation `b`, returns `PMF α`). This
module's `posterior` is mathematically the same Bayes' rule formula but
with three ergonomic differences:

1. **`ℝ` instead of `ℝ≥0∞`** — keeps arithmetic in the reals so consumers
   can use signed value functions (`(W → ℝ) → ℝ` for utility / entropy
   theorems) without `ENNReal` coercions.
2. **Experiment indexing `E`** — `ObservationModel W E O` carries an
   explicit experiment-index parameter that PMF kernels lack. For each
   fixed `e : E`, an `ObservationModel` IS a kernel `W → PMF O` (see
   `ObservationModel.toPMFKernel`).
3. **Permissive prior** — accepts any `prior : W → ℝ` rather than
   requiring a `PMF W` (the formula gives 0 when the marginal is 0).

Use `PMF.posterior` for general probability work; use this module for
finite Bayesian inference where experiment indexing or `(W → ℝ)`-typed
value functions are needed (e.g., `ExperimentDesign.eig`).

## Key Results

- `posterior_nonneg`: posteriors inherit non-negativity from priors
- `posterior_sum_one`: posteriors sum to 1 (when marginal is nonzero)
- `posterior_marginalizes_to_prior`: the law of total probability —
  marginalized posteriors reconstruct the prior:
  `∑ o, P(o|e) · P(w|o,e) = prior(w)`
- `ObservationModel.toPMFKernel`: PMF-typed view of the likelihood at
  fixed experiment, enabling interop with `PMF.posterior`.

## Usage

This module is imported by `ExperimentDesign.lean` (for EIG computation)
and can be imported independently wherever Bayesian updating is needed.
-/

namespace Core

open BigOperators Finset

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

-- ============================================================================
-- §3. Basic Properties
-- ============================================================================

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

/-- Posterior sums to 1 when marginal is nonzero and prior is non-negative. -/
theorem posterior_sum_one (om : ObservationModel W E O) (prior : W → ℝ)
    (_hprior : ∀ w, 0 ≤ prior w) (e : E) (o : O)
    (hm : marginalObs om prior e o ≠ 0) :
    ∑ w : W, posterior om prior e o w = 1 := by
  simp only [posterior, hm, ↓reduceIte, ← Finset.sum_div]
  exact div_self hm

/-- The law of total probability for posteriors: marginalized posteriors
    reconstruct the prior.

    Σ_o P(o|e) · P(w|o,e) = prior(w)

    This is the key identity underlying EIG non-negativity. -/
theorem posterior_marginalizes_to_prior (om : ObservationModel W E O)
    (prior : W → ℝ) (hprior : ∀ w, 0 ≤ prior w) (e : E) (w : W) :
    ∑ o : O, marginalObs om prior e o * posterior om prior e o w =
    prior w := by
  -- Each summand equals prior(w) · lik(w,e,o), regardless of marginalObs = 0
  suffices key : ∀ o, marginalObs om prior e o * posterior om prior e o w =
      prior w * om.likelihood w e o by
    simp_rw [key, ← Finset.mul_sum, om.likelihood_sum w e, mul_one]
  intro o
  by_cases hm : marginalObs om prior e o = 0
  · -- marginalObs = 0: posterior is 0, and prior·lik is also 0 (nonneg sum = 0)
    have hp : posterior om prior e o w = 0 := by simp [posterior, hm]
    rw [hp, mul_zero]
    symm
    have h_le : prior w * om.likelihood w e o ≤ marginalObs om prior e o :=
      Finset.single_le_sum
        (fun w' _ => mul_nonneg (hprior w') (om.likelihood_nonneg w' e o))
        (Finset.mem_univ w)
    linarith [mul_nonneg (hprior w) (om.likelihood_nonneg w e o)]
  · -- marginalObs ≠ 0: m · (prior·lik / m) = prior·lik
    have hp : posterior om prior e o w =
        prior w * om.likelihood w e o / marginalObs om prior e o := by
      simp [posterior, hm]
    rw [hp, mul_comm, div_mul_cancel₀ _ hm]

-- ============================================================================
-- §4. Deterministic Observation Model
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

/-! ## PMF interop

Convert an `ObservationModel` at a fixed experiment to a mathlib
`PMF`-typed kernel `W → PMF O`. Bridges to `PMF.posterior` for any
downstream use that requires the canonical mathlib type. -/

/-- The PMF view of an `ObservationModel` at a fixed experiment `e`.
    For each world `w`, returns the `PMF O` whose mass at `o` is
    `om.likelihood w e o`. Bridges this module's ℝ-typed Bayesian
    machinery to mathlib's canonical `PMF.posterior`. -/
noncomputable def ObservationModel.toPMFKernel
    (om : ObservationModel W E O) (e : E) : W → PMF O := fun w =>
  PMF.ofFintype (fun o => ENNReal.ofReal (om.likelihood w e o)) (by
    rw [show (∑ o : O, ENNReal.ofReal (om.likelihood w e o)) =
         ENNReal.ofReal (∑ o : O, om.likelihood w e o) from
      (ENNReal.ofReal_sum_of_nonneg
        (fun o _ => om.likelihood_nonneg w e o)).symm]
    rw [om.likelihood_sum w e, ENNReal.ofReal_one])

end Core
