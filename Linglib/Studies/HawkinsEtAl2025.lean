/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Analysis.Convex.Function
import Linglib.Core.Probability.Choice.RationalAction
import Linglib.Core.Probability.Decision.Basic
import Linglib.Core.Probability.Posterior
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Hawkins et al. (2025): the questioner as experiment designer

[hawkins-etal-2025]'s PRIOR-PQ questioner selects a polar question by the expected
decision value of its answer. This file states that selection rule as
[lindley-1956]'s expected information gain of an experiment — an observation model
`P(o | w, e)`, the Bayesian posterior it induces, and a value of holding a belief —
and relates it to [van-rooy-2003]'s expected utility value of a question.

## Main definitions

* `ObservationModel`, `posterior`, `marginalObs` — finite Bayesian inference with an
  explicit experiment index, on real-valued weights.
* `eig` — the expected information gain of an experiment under a value function;
  `optimalExperiment` — the softmax questioner over experiments.

## Main results

* `eig_nonneg_of_convex` — expected information gain is nonnegative for a convex value
  of beliefs, and `eig_nonneg_dpValueR` for the decision value in particular.
* `eig_deterministicObs_eq_euv` — with deterministic observations (partition cells) the
  gain is [van-rooy-2003]'s expected utility value of the partition.
-/

namespace HawkinsEtAl2025

open Core Real BigOperators Finset

variable {W E O : Type*} [Fintype W] [Fintype O]

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

-- ============================================================================
-- §1. Expected Information Gain (EIG)
-- ============================================================================

/-- Expected information gain of experiment e relative to value function V:

    EIG(e) = Σ_o P(o|e) · V(posterior(·|o,e)) − V(prior)

    When V = max_a EU(a), this is the expected value of the experiment
    (generalization of Van Rooy's EUV from partitions to stochastic observations).

    When V = −H(·) (negative entropy), this is the mutual information I(W;O|e),
    which equals [lindley-1956]'s expected information gain. -/
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
    is the EU of the optimal action under those beliefs,
    `V(post) = maxₐ ∑_w post(w) · U(w,a)` (`0` if `actions` is empty).

    The exact ℝ analog of `DecisionTheory.DecisionProblem.value` — same `Finset.sup'` shape,
    so the deterministic-observation bridge (`eig_deterministicObs_eq_euv`)
    matches definitionally cell by cell. -/
noncomputable def dpValueR {A : Type*} (utility : W → A → ℝ)
    (actions : Finset A) : (W → ℝ) → ℝ :=
  fun post =>
    if h : actions.Nonempty then actions.sup' h (fun a => ∑ w : W, post w * utility w a)
    else 0

/-- **`dpValueR` is a support function, hence convex**: the decision value
`post ↦ maxₐ ∑_w post(w)·U(w,a)` is a finite supremum of linear functionals of
the belief vector (`convexOn_finset_sup'` over `LinearMap.proj`-sums). The
convexity that every value-of-information inequality in this directory runs
on. -/
theorem convexOn_dpValueR {A : Type*} (utility : W → A → ℝ) (actions : Finset A) :
    ConvexOn ℝ Set.univ (dpValueR utility actions) := by
  by_cases h : actions.Nonempty
  · have heq : dpValueR utility actions
        = fun post => actions.sup' h (fun a => ∑ w : W, post w * utility w a) :=
      funext (λ post => dif_pos h)
    rw [heq]
    refine ConvexOn.finset_sup'_apply h (λ a _ => ?_)
    have hlin : (fun post : W → ℝ => ∑ w : W, post w * utility w a)
        = ⇑(∑ w : W, utility w a • LinearMap.proj (R := ℝ) (φ := λ _ : W => ℝ) w) := by
      funext post
      simp [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
        smul_eq_mul, mul_comm]
    rw [hlin]
    exact LinearMap.convexOn _ convex_univ
  · have heq : dpValueR utility actions = fun _ => (0 : ℝ) :=
      funext (λ post => dif_neg h)
    rw [heq]
    exact convexOn_const 0 convex_univ

-- ============================================================================
-- §4. Bridge to DecisionTheory
-- ============================================================================

/-- With deterministic observations, the probability-weighted value of the
posterior at `o` equals the cast of the unnormalized best-action value of the
fiber of `o`: `P(o) · V(post_o) = maxₐ ∑_{w ∈ fiber o} P(w)·U(w,a)`. The
normalizing mass cancels; a zero-mass fiber makes both sides `0`. -/
private lemma marginalObs_mul_dpValueR {A : Type*} [DecidableEq O] [DecidableEq W]
    (classify : W → O) (dp : DecisionTheory.DecisionProblem ℚ W A)
    (acts : Finset A) (hacts : acts.Nonempty) (hprior : ∀ w, 0 ≤ dp.prior w) (o : O) :
    marginalObs (deterministicObs classify) (fun w => (dp.prior w : ℝ)) () o *
      dpValueR (fun w a => (dp.utility w a : ℝ)) acts
        (posterior (deterministicObs classify) (fun w => (dp.prior w : ℝ)) () o) =
    (acts.sup' hacts (fun a =>
      ∑ w ∈ Finset.univ.filter (fun w => classify w = o),
        dp.prior w * dp.utility w a) : ℚ) := by
  set fiber : Finset W := Finset.univ.filter (fun w => classify w = o) with hfiber
  set m : ℝ := marginalObs (deterministicObs classify) (fun w => (dp.prior w : ℝ)) () o
    with hm_def
  -- Compute m as the cast of prior mass on the fiber.
  have hm_eq : m = ((∑ w ∈ fiber, dp.prior w : ℚ) : ℝ) := by
    simp only [hm_def, marginalObs, deterministicObs, mul_ite, mul_one, mul_zero,
      ← Finset.sum_filter, ← hfiber]
    push_cast; rfl
  have hpriorR : ∀ w, (0 : ℝ) ≤ (dp.prior w : ℝ) := fun w => by exact_mod_cast hprior w
  have hm_nonneg : 0 ≤ m :=
    marginalObs_nonneg (deterministicObs classify) _ hpriorR () o
  -- Push the ℚ→ℝ cast out of the RHS sup'.
  have hcast_sup : ((acts.sup' hacts (fun a =>
        ∑ w ∈ fiber, dp.prior w * dp.utility w a) : ℚ) : ℝ) =
      acts.sup' hacts (fun a =>
        ((∑ w ∈ fiber, dp.prior w * dp.utility w a : ℚ) : ℝ)) :=
    Finset.apply_sup'_eq_sup'_comp hacts _ (fun x y => Rat.cast_max x y)
  rw [hcast_sup]
  -- Unfold dpValueR with hacts.
  simp only [dpValueR, dif_pos hacts]
  by_cases h0 : m = 0
  · -- Zero-mass fiber: both sides collapse to 0.
    rw [h0, zero_mul]
    rw [hm_eq] at h0
    have hp0 : ∑ w ∈ fiber, dp.prior w = 0 := by exact_mod_cast h0
    have hpw : ∀ w ∈ fiber, dp.prior w = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hprior w)).mp hp0
    symm
    refine Finset.sup'_eq_of_forall hacts _ (fun a _ => ?_)
    have hqzero : ∑ w ∈ fiber, dp.prior w * dp.utility w a = 0 :=
      Finset.sum_eq_zero (fun w hw => by rw [hpw w hw, zero_mul])
    exact_mod_cast hqzero
  · -- Positive-mass fiber: pull m into the sup' and cancel.
    rw [Finset.mul₀_sup' hm_nonneg _ acts hacts]
    refine Finset.sup'_congr hacts rfl (fun a _ => ?_)
    have hpost_eq : ∀ w : W,
        posterior (deterministicObs classify) (fun w' => (dp.prior w' : ℝ)) () o w
          = (dp.prior w : ℝ) * (if classify w = o then 1 else 0) / m := by
      intro w
      change (if m = 0 then (0 : ℝ)
              else (dp.prior w : ℝ) * (if classify w = o then 1 else 0) / m) = _
      rw [if_neg h0]
    simp_rw [hpost_eq]
    -- (∑ w, (prior · ite / m) * util) = (∑ w, prior · ite · util) / m; then m · (X/m) = X.
    rw [show (∑ w : W,
        ((dp.prior w : ℝ) * (if classify w = o then 1 else 0) / m) *
          ((dp.utility w a : ℝ))) =
             (∑ w : W, (dp.prior w : ℝ) * (if classify w = o then 1 else 0) *
              ((dp.utility w a : ℝ))) / m by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun w _ => ?_); ring]
    rw [mul_div_cancel₀ _ h0]
    -- Collapse the indicator to a sum over the fiber, then push the cast in.
    rw [show (∑ w : W, (dp.prior w : ℝ) * (if classify w = o then 1 else 0) *
              ((dp.utility w a : ℝ))) =
             ∑ w ∈ fiber, (dp.prior w : ℝ) * (dp.utility w a : ℝ) by
      simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
        ← Finset.sum_filter, ← hfiber]]
    push_cast; rfl

/-- **The deterministic-observation bridge, for real**: with observations given by a
classifier `classify : W → O` whose fibers are all nonempty, the expected information
gain of the (single) deterministic experiment under the decision-theoretic value
function equals [van-rooy-2003]'s expected utility value of the corresponding
partition question — `Core.DecisionTheory.DecisionProblem.questionUtility`, cast from ℚ to ℝ.

The fiber-nonemptiness hypothesis keeps the `Finset.image` indexing faithful: empty
fibers would collapse in the cell set while still contributing (zero) terms to the
observation sum. -/
theorem eig_deterministicObs_eq_euv {A : Type*} [DecidableEq O] [DecidableEq W]
    [DecidableEq A] (classify : W → O) (dp : DecisionTheory.DecisionProblem ℚ W A)
    (acts : Finset A) (hacts : acts.Nonempty)
    (hprior : ∀ w, 0 ≤ dp.prior w) (hsum : ∑ w : W, dp.prior w = 1)
    (hfib : ∀ o : O, (Finset.univ.filter (fun w => classify w = o)).Nonempty) :
    eig (deterministicObs classify) (fun w => (dp.prior w : ℝ))
        (dpValueR (fun w a => (dp.utility w a : ℝ)) acts) () =
    (DecisionTheory.DecisionProblem.questionUtility dp acts
      (Finset.univ.image (fun o : O =>
        Finset.univ.filter (fun w => classify w = o))) : ℚ) := by
  set fiberMap : O → Finset W := fun o => Finset.univ.filter (fun w => classify w = o)
    with hfiberMap
  -- The fiber map is injective on `Finset.univ` (uses nonemptiness of every fiber).
  have hinj : ∀ o₁ ∈ (Finset.univ : Finset O), ∀ o₂ ∈ (Finset.univ : Finset O),
      fiberMap o₁ = fiberMap o₂ → o₁ = o₂ := fun o₁ _ o₂ _ heq => by
    obtain ⟨w, hw⟩ := hfib o₁
    have hw₁ : classify w = o₁ := (Finset.mem_filter.mp hw).2
    have hw₂ : w ∈ fiberMap o₂ := heq ▸ hw
    exact hw₁.symm.trans (Finset.mem_filter.mp hw₂).2
  -- Fiber probabilities sum to the total prior mass = 1.
  have hcellSum : ∑ o : O, DecisionTheory.DecisionProblem.cellProbability dp (fiberMap o) = 1 := by
    simp only [DecisionTheory.DecisionProblem.cellProbability, hfiberMap]
    rw [Finset.sum_fiberwise_of_maps_to (fun w _ => Finset.mem_univ (classify w))]
    exact hsum
  -- Per-cell decision-theoretic identity (private lemma from Basic re-derived inline):
  -- P(cell) · V(D|cell) = sup'_a ∑_{w∈cell} P(w) · U(w,a).
  have hcell_val : ∀ cell : Finset W,
      DecisionTheory.DecisionProblem.cellProbability dp cell * DecisionTheory.DecisionProblem.condValue dp acts cell
        = acts.sup' hacts (fun a => ∑ w ∈ cell, dp.prior w * dp.utility w a) := by
    intro cell
    unfold DecisionTheory.DecisionProblem.cellProbability DecisionTheory.DecisionProblem.condValue
    rw [dif_pos hacts]
    have htp_nonneg : 0 ≤ cell.sum dp.prior :=
      Finset.sum_nonneg (fun w _ => hprior w)
    by_cases htp : cell.sum dp.prior = 0
    · rw [htp, zero_mul]
      have hpw : ∀ w ∈ cell, dp.prior w = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hprior w)).mp htp
      symm
      refine Finset.sup'_eq_of_forall hacts _ (fun a _ => ?_)
      exact Finset.sum_eq_zero (fun w hw => by rw [hpw w hw, zero_mul])
    · rw [Finset.mul₀_sup' htp_nonneg _ acts hacts]
      refine Finset.sup'_congr hacts rfl (fun a _ => ?_)
      have hcEU : DecisionTheory.DecisionProblem.condExpectedUtility dp cell a
          = cell.sum (fun w => dp.prior w / cell.sum dp.prior * dp.utility w a) := by
        show (if cell.sum dp.prior = 0 then (0 : ℚ) else _) = _
        rw [if_neg htp]
      rw [hcEU, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_div_cancel_left₀ _ htp]
  -- `dpValueR` on the ℝ-cast prior equals the cast of `DecisionProblem.value`.
  have hdpvR : dpValueR (fun w a => (dp.utility w a : ℝ)) acts (fun w => (dp.prior w : ℝ))
      = ((DecisionTheory.DecisionProblem.value dp acts : ℚ) : ℝ) := by
    simp only [dpValueR, DecisionTheory.DecisionProblem.value, dif_pos hacts]
    rw [show acts.sup' hacts (fun a => ∑ w : W, (dp.prior w : ℝ) * (dp.utility w a : ℝ))
         = acts.sup' hacts
             (fun a => ((DecisionTheory.DecisionProblem.expectedUtility dp a : ℚ) : ℝ)) from ?_]
    · exact (Finset.apply_sup'_eq_sup'_comp hacts _ (fun x y => Rat.cast_max x y)).symm
    · refine Finset.sup'_congr hacts rfl (fun a _ => ?_)
      simp only [DecisionTheory.DecisionProblem.expectedUtility]; push_cast; rfl
  -- Assemble.
  unfold eig
  rw [hdpvR]
  rw [show (∑ o : O, marginalObs (deterministicObs classify)
              (fun w => (dp.prior w : ℝ)) () o *
              dpValueR (fun w a => ((dp.utility w a : ℝ))) acts
                (posterior (deterministicObs classify)
                  (fun w => ((dp.prior w : ℝ))) () o))
          = ∑ o : O, ((acts.sup' hacts (fun a =>
              ∑ w ∈ fiberMap o, dp.prior w * dp.utility w a) : ℚ) : ℝ) from
      Finset.sum_congr rfl (fun o _ =>
        marginalObs_mul_dpValueR classify dp acts hacts hprior o)]
  rw [← Rat.cast_sum, ← Rat.cast_sub]
  -- Cast down: prove the ℚ identity.
  congr 1
  unfold DecisionTheory.DecisionProblem.questionUtility
  rw [Finset.sum_image hinj]
  simp only [DecisionTheory.DecisionProblem.utilityValue]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ o : O, DecisionTheory.DecisionProblem.cellProbability dp (fiberMap o) *
        DecisionTheory.DecisionProblem.condValue dp acts (fiberMap o))
        = ∑ o : O, acts.sup' hacts (fun a =>
            ∑ w ∈ fiberMap o, dp.prior w * dp.utility w a) from
      Finset.sum_congr rfl (fun o _ => hcell_val (fiberMap o))]
  rw [← Finset.sum_mul, hcellSum, one_mul]

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

/-- EIG is non-negative when V is convex (Jensen's inequality).

    For convex V: E[V(posterior)] ≥ V(E[posterior]) = V(prior).
    The posterior averages back to the prior (by `posterior_marginalizes_to_prior`):
    Σ_o P(o|e) · posterior(w|o,e) = prior(w).

    Jensen's inequality then gives V(prior) ≤ E_o[V(posterior)], hence EIG ≥ 0. -/
theorem eig_nonneg_of_convex (om : ObservationModel W E O) (prior : W → ℝ)
    (valueFn : (W → ℝ) → ℝ) (e : E)
    (hprior : ∀ w, 0 ≤ prior w)
    (hprior_sum : ∑ w : W, prior w = 1)
    (hVO : ConvexOn ℝ Set.univ valueFn) :
    0 ≤ eig om prior valueFn e := by
  unfold eig
  suffices h : valueFn prior ≤
      ∑ o : O, marginalObs om prior e o * valueFn (posterior om prior e o) by linarith
  -- Apply Jensen (ConvexOn.map_sum_le) with weights = marginalObs, points = posterior
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

/-- **EIG of the decision value function is non-negative** — Jensen applied to
the support function: information cannot hurt an expected-utility maximizer
([blackwell-1953]'s forward direction at the value level). -/
theorem eig_nonneg_dpValueR {A : Type*} (om : ObservationModel W E O)
    (prior : W → ℝ) (utility : W → A → ℝ) (actions : Finset A) (e : E)
    (hprior : ∀ w, 0 ≤ prior w) (hprior_sum : ∑ w : W, prior w = 1) :
    0 ≤ eig om prior (dpValueR utility actions) e :=
  eig_nonneg_of_convex om prior _ e hprior hprior_sum
    (convexOn_dpValueR utility actions)

end HawkinsEtAl2025
