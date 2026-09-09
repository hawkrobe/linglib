import Linglib.Core.Probability.Decision.Basic
import Linglib.Core.Analysis.Convex.Function
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

/-!
# Experiments, posteriors and the expected value of information

A finite statistical experiment on the real face: an `ObservationModel W E O` is a family of
observation likelihoods `P(o ∣ w, e)` indexed by experiments `e`, and from a belief `W → ℝ` over
worlds it yields the observation marginal, the Bayesian posterior, and [lindley-1956]'s expected
information gain of `e` under a value of beliefs `V`,
`EIG(e) = ∑ₒ P(o ∣ e) · V(P(· ∣ o, e)) − V(prior)`. Under the decision value
`decisionValue U actions`, the best expected utility a belief affords, the gain is the expected
value of the experiment to a decision maker, the stochastic-observation generalisation of
[van-rooy-2003]'s expected utility value of a question, which
`ObservationModel.eig_deterministic_eq_questionUtility` recovers on deterministic experiments.
Jensen's inequality on the convex decision value gives `ObservationModel.eig_nonneg_decisionValue`:
information cannot hurt an expected-utility maximiser, the value-level face of [blackwell-1953]'s
forward direction, whose kernel-level statement is `bayesRisk_deterministic_le_deterministic_comp`
in `Core.Probability.Decision.Blackwell`.

## Implementation notes

Beliefs are bare functions `W → ℝ`, so that priors and posteriors are terms of one type and
Jensen's inequality applies to the belief vector; normalisation and nonnegativity are hypotheses
of the theorems that need them. The posterior is `0` at observations of zero marginal
probability, which makes the law of total probability `sum_marginal_mul_posterior`
unconditional. `decisionValue` is the `Finset.sup'` of the linear functionals
`post ↦ ∑ w, post w * U w a`, `0` on an empty action set, the shape of
`Core.DecisionTheory.DecisionProblem.value`.

## References

* [lindley-1956]
* [van-rooy-2003]
* [blackwell-1953]
-/

namespace ProbabilityTheory

open Finset Core.DecisionTheory

variable {W E O : Type*} [Fintype W] [Fintype O]

/-- An observation model: the likelihood `P(o ∣ w, e)` of observing `o` when the world is `w`
and experiment `e` is run, a probability distribution over `O` for each world and experiment. -/
structure ObservationModel (W E O : Type*) [Fintype O] where
  /-- The likelihood `P(o ∣ w, e)`. -/
  likelihood : W → E → O → ℝ
  likelihood_nonneg : ∀ w e o, 0 ≤ likelihood w e o
  likelihood_sum : ∀ w e, ∑ o, likelihood w e o = 1

namespace ObservationModel

variable (om : ObservationModel W E O) (prior : W → ℝ)

/-- The marginal probability `P(o ∣ e) = ∑ w, prior w * P(o ∣ w, e)` of observing `o`. -/
noncomputable def marginal (e : E) (o : O) : ℝ := ∑ w, prior w * om.likelihood w e o

/-- The Bayesian posterior `P(w ∣ o, e) = prior w * P(o ∣ w, e) / P(o ∣ e)`, `0` where the
marginal vanishes. -/
noncomputable def posterior (e : E) (o : O) : W → ℝ := λ w =>
  if om.marginal prior e o = 0 then 0 else prior w * om.likelihood w e o / om.marginal prior e o

/-- [lindley-1956]'s expected information gain of experiment `e` under a value of beliefs `V`:
the expected value of the posterior less the value of the prior. -/
noncomputable def eig (V : (W → ℝ) → ℝ) (e : E) : ℝ :=
  ∑ o, om.marginal prior e o * V (om.posterior prior e o) - V prior

/-- The deterministic experiment of a classifier: each world yields its own class. -/
def deterministic [DecidableEq O] (classify : W → O) : ObservationModel W Unit O where
  likelihood w _ o := if classify w = o then 1 else 0
  likelihood_nonneg _ _ _ := by split <;> norm_num
  likelihood_sum w _ := by
    have : ∑ o : O, (if classify w = o then (1 : ℝ) else 0) =
        ∑ o : O, (if o = classify w then 1 else 0) := by
      congr 1; ext o; simp [eq_comm]
    rw [this, sum_ite_eq']; simp

/-- Marginal observation probabilities sum to the total prior mass. -/
theorem sum_marginal (e : E) : ∑ o, om.marginal prior e o = ∑ w, prior w := by
  simp only [marginal]
  rw [sum_comm]
  refine sum_congr rfl λ w _ => ?_
  rw [← mul_sum, om.likelihood_sum w e, mul_one]

/-- The expected information gain is homogeneous in the value of beliefs. -/
theorem eig_smul (V : (W → ℝ) → ℝ) (c : ℝ) (e : E) :
    om.eig prior (c • V) e = c * om.eig prior V e := by
  unfold eig
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, mul_sum]
  congr 1
  exact sum_congr rfl λ o _ => by ring

variable {prior}

theorem marginal_nonneg (hprior : ∀ w, 0 ≤ prior w) (e : E) (o : O) :
    0 ≤ om.marginal prior e o :=
  sum_nonneg λ w _ => mul_nonneg (hprior w) (om.likelihood_nonneg w e o)

theorem posterior_nonneg (hprior : ∀ w, 0 ≤ prior w) (e : E) (o : O) (w : W) :
    0 ≤ om.posterior prior e o w := by
  unfold posterior
  split
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (hprior w) (om.likelihood_nonneg w e o))
      (om.marginal_nonneg hprior e o)

theorem sum_posterior {e : E} {o : O} (hm : om.marginal prior e o ≠ 0) :
    ∑ w, om.posterior prior e o w = 1 := by
  simp only [posterior, hm, ↓reduceIte, ← sum_div]
  exact div_self hm

/-- The law of total probability: the posteriors, weighted by the marginals, average back to
the prior. -/
theorem sum_marginal_mul_posterior (hprior : ∀ w, 0 ≤ prior w) (e : E) (w : W) :
    ∑ o, om.marginal prior e o * om.posterior prior e o w = prior w := by
  suffices key : ∀ o, om.marginal prior e o * om.posterior prior e o w =
      prior w * om.likelihood w e o by
    simp_rw [key, ← mul_sum, om.likelihood_sum w e, mul_one]
  intro o
  by_cases hm : om.marginal prior e o = 0
  · have hle : prior w * om.likelihood w e o ≤ om.marginal prior e o :=
      single_le_sum (λ w' _ => mul_nonneg (hprior w') (om.likelihood_nonneg w' e o)) (mem_univ w)
    have := mul_nonneg (hprior w) (om.likelihood_nonneg w e o)
    simp only [posterior, hm, ↓reduceIte, mul_zero]
    linarith
  · simp only [posterior, hm, ↓reduceIte]
    rw [mul_comm, div_mul_cancel₀ _ hm]

/-- An experiment whose likelihood does not depend on the world is uninformative: its
posteriors are the prior and its expected information gain vanishes. -/
theorem eig_eq_zero_of_const (hsum : ∑ w, prior w = 1) (V : (W → ℝ) → ℝ) {e : E} {ℓ : O → ℝ}
    (hℓ : ∀ w, om.likelihood w e = ℓ) : om.eig prior V e = 0 := by
  have hm : ∀ o, om.marginal prior e o = ℓ o := λ o => by
    simp only [marginal, hℓ, ← sum_mul, hsum, one_mul]
  have hℓ1 : ∑ o, ℓ o = 1 := by
    obtain ⟨w⟩ : Nonempty W := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hsum
    have := om.likelihood_sum w e
    rwa [hℓ w] at this
  have hpost : ∀ o, ℓ o ≠ 0 → om.posterior prior e o = prior := λ o ho => by
    funext w
    simp only [posterior, hm, ho, ↓reduceIte, hℓ]
    rw [mul_div_assoc, div_self ho, mul_one]
  unfold eig
  rw [sub_eq_zero]
  calc ∑ o, om.marginal prior e o * V (om.posterior prior e o)
      = ∑ o, ℓ o * V prior := sum_congr rfl λ o _ => by
        by_cases ho : ℓ o = 0
        · rw [hm, ho, zero_mul, zero_mul]
        · rw [hm, hpost o ho]
    _ = V prior := by rw [← sum_mul, hℓ1, one_mul]

/-- The expected information gain is nonnegative under a convex value of beliefs: Jensen's
inequality, the posteriors averaging to the prior by `sum_marginal_mul_posterior`. -/
theorem eig_nonneg_of_convex (V : (W → ℝ) → ℝ) (e : E) (hprior : ∀ w, 0 ≤ prior w)
    (hsum : ∑ w, prior w = 1) (hV : ConvexOn ℝ Set.univ V) : 0 ≤ om.eig prior V e := by
  unfold eig
  suffices h : V prior ≤ ∑ o, om.marginal prior e o * V (om.posterior prior e o) by linarith
  have hmo : ∑ o, om.marginal prior e o = 1 := by rw [sum_marginal]; exact hsum
  have hJ := hV.map_sum_le (p := om.posterior prior e) (λ o _ => om.marginal_nonneg hprior e o)
    hmo (λ o _ => Set.mem_univ _)
  have hlhs : ∑ o, om.marginal prior e o • om.posterior prior e o = prior := by
    ext w
    simp [sum_apply, om.sum_marginal_mul_posterior hprior e w]
  rw [hlhs] at hJ
  simpa only [smul_eq_mul] using hJ

end ObservationModel

variable {A : Type*} (U : W → A → ℝ) (actions : Finset A)

/-- The decision value of a belief: the best expected utility over `actions`, `0` on an empty
action set. -/
noncomputable def decisionValue (post : W → ℝ) : ℝ :=
  if h : actions.Nonempty then actions.sup' h λ a => ∑ w, post w * U w a else 0

/-- The decision value is a support function, a finite supremum of linear functionals of the
belief vector, hence convex. -/
theorem convexOn_decisionValue : ConvexOn ℝ Set.univ (decisionValue U actions) := by
  by_cases h : actions.Nonempty
  · have heq : decisionValue U actions
        = λ post => actions.sup' h λ a => ∑ w, post w * U w a := funext λ post => dif_pos h
    rw [heq]
    refine ConvexOn.finset_sup'_apply h λ a _ => ?_
    have hlin : (λ post : W → ℝ => ∑ w, post w * U w a)
        = ⇑(∑ w, U w a • LinearMap.proj (R := ℝ) (φ := λ _ : W => ℝ) w) := by
      funext post
      simp [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
        mul_comm]
    rw [hlin]
    exact LinearMap.convexOn _ convex_univ
  · have heq : decisionValue U actions = λ _ => (0 : ℝ) := funext λ post => dif_neg h
    rw [heq]
    exact convexOn_const 0 convex_univ

/-- Scaling every utility by a nonnegative factor scales the decision value. -/
theorem decisionValue_smul {c : ℝ} (hc : 0 ≤ c) :
    decisionValue (c • U) actions = c • decisionValue U actions := by
  funext post
  simp only [decisionValue, Pi.smul_apply, smul_eq_mul]
  by_cases h : actions.Nonempty
  · rw [dif_pos h, dif_pos h, mul₀_sup' hc]
    exact sup'_congr h rfl λ a _ => by
      rw [mul_sum]
      exact sum_congr rfl λ w _ => by ring
  · rw [dif_neg h, dif_neg h, mul_zero]

namespace ObservationModel

variable (om : ObservationModel W E O) {prior : W → ℝ}

/-- Information cannot hurt an expected-utility maximiser: the expected information gain of
the decision value is nonnegative, [blackwell-1953]'s forward direction at the value level. -/
theorem eig_nonneg_decisionValue (e : E) (hprior : ∀ w, 0 ≤ prior w) (hsum : ∑ w, prior w = 1) :
    0 ≤ om.eig prior (decisionValue U actions) e :=
  om.eig_nonneg_of_convex _ e hprior hsum (convexOn_decisionValue U actions)

/-! ### Deterministic experiments and the utility value of a question -/

/-- With deterministic observations, the probability-weighted value of the posterior at `o` is
the unnormalised best-action value of the fibre of `o`: the normalising mass cancels, and a
zero-mass fibre makes both sides `0`. -/
private lemma marginal_mul_decisionValue [DecidableEq O] [DecidableEq W] (classify : W → O)
    (dp : DecisionProblem ℚ W A) (acts : Finset A) (hacts : acts.Nonempty)
    (hprior : ∀ w, 0 ≤ dp.prior w) (o : O) :
    (deterministic classify).marginal (λ w => (dp.prior w : ℝ)) () o *
      decisionValue (λ w a => (dp.utility w a : ℝ)) acts
        ((deterministic classify).posterior (λ w => (dp.prior w : ℝ)) () o) =
    (acts.sup' hacts (λ a =>
      ∑ w ∈ univ.filter (λ w => classify w = o), dp.prior w * dp.utility w a) : ℚ) := by
  set fiber : Finset W := univ.filter (λ w => classify w = o) with hfiber
  set m : ℝ := (deterministic classify).marginal (λ w => (dp.prior w : ℝ)) () o with hm_def
  have hm_eq : m = ((∑ w ∈ fiber, dp.prior w : ℚ) : ℝ) := by
    simp only [hm_def, marginal, deterministic, mul_ite, mul_one, mul_zero, ← sum_filter,
      ← hfiber]
    push_cast; rfl
  have hpriorR : ∀ w, (0 : ℝ) ≤ (dp.prior w : ℝ) := λ w => by exact_mod_cast hprior w
  have hm_nonneg : 0 ≤ m := (deterministic classify).marginal_nonneg hpriorR () o
  have hcast_sup : ((acts.sup' hacts (λ a => ∑ w ∈ fiber, dp.prior w * dp.utility w a) : ℚ) : ℝ) =
      acts.sup' hacts (λ a => ((∑ w ∈ fiber, dp.prior w * dp.utility w a : ℚ) : ℝ)) :=
    apply_sup'_eq_sup'_comp hacts _ (λ x y => Rat.cast_max x y)
  rw [hcast_sup]
  simp only [decisionValue, dif_pos hacts]
  by_cases h0 : m = 0
  · rw [h0, zero_mul]
    rw [hm_eq] at h0
    have hp0 : ∑ w ∈ fiber, dp.prior w = 0 := by exact_mod_cast h0
    have hpw : ∀ w ∈ fiber, dp.prior w = 0 :=
      (sum_eq_zero_iff_of_nonneg (λ w _ => hprior w)).mp hp0
    symm
    refine sup'_eq_of_forall hacts _ (λ a _ => ?_)
    have hqzero : ∑ w ∈ fiber, dp.prior w * dp.utility w a = 0 :=
      sum_eq_zero (λ w hw => by rw [hpw w hw, zero_mul])
    exact_mod_cast hqzero
  · rw [mul₀_sup' hm_nonneg _ acts hacts]
    refine sup'_congr hacts rfl (λ a _ => ?_)
    have hpost_eq : ∀ w : W,
        (deterministic classify).posterior (λ w' => (dp.prior w' : ℝ)) () o w
          = (dp.prior w : ℝ) * (if classify w = o then 1 else 0) / m := by
      intro w
      change (if m = 0 then (0 : ℝ)
              else (dp.prior w : ℝ) * (if classify w = o then 1 else 0) / m) = _
      rw [if_neg h0]
    simp_rw [hpost_eq]
    rw [show (∑ w : W, ((dp.prior w : ℝ) * (if classify w = o then 1 else 0) / m) *
          ((dp.utility w a : ℝ))) =
        (∑ w : W, (dp.prior w : ℝ) * (if classify w = o then 1 else 0) *
          ((dp.utility w a : ℝ))) / m by
      rw [sum_div]; refine sum_congr rfl (λ w _ => ?_); ring]
    rw [mul_div_cancel₀ _ h0]
    rw [show (∑ w : W, (dp.prior w : ℝ) * (if classify w = o then 1 else 0) *
          ((dp.utility w a : ℝ))) = ∑ w ∈ fiber, (dp.prior w : ℝ) * (dp.utility w a : ℝ) by
      simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, ← sum_filter, ← hfiber]]
    push_cast; rfl

/-- With observations given by a classifier whose fibres are all nonempty, the expected
information gain of the deterministic experiment under the decision value is
[van-rooy-2003]'s expected utility value of the corresponding partition question,
`Core.DecisionTheory.DecisionProblem.questionUtility`, cast from `ℚ`. Fibre nonemptiness keeps
the `Finset.image` indexing faithful: an empty fibre would collapse in the cell set while still
contributing a zero term to the observation sum. -/
theorem eig_deterministic_eq_questionUtility [DecidableEq O] [DecidableEq W] [DecidableEq A]
    (classify : W → O) (dp : DecisionProblem ℚ W A) (acts : Finset A) (hacts : acts.Nonempty)
    (hprior : ∀ w, 0 ≤ dp.prior w) (hsum : ∑ w, dp.prior w = 1)
    (hfib : ∀ o : O, (univ.filter (λ w => classify w = o)).Nonempty) :
    (deterministic classify).eig (λ w => (dp.prior w : ℝ))
        (decisionValue (λ w a => (dp.utility w a : ℝ)) acts) () =
    (DecisionProblem.questionUtility dp acts
      (univ.image (λ o : O => univ.filter (λ w => classify w = o))) : ℚ) := by
  set fiberMap : O → Finset W := λ o => univ.filter (λ w => classify w = o) with hfiberMap
  have hinj : ∀ o₁ ∈ (univ : Finset O), ∀ o₂ ∈ (univ : Finset O),
      fiberMap o₁ = fiberMap o₂ → o₁ = o₂ := λ o₁ _ o₂ _ heq => by
    obtain ⟨w, hw⟩ := hfib o₁
    have hw₁ : classify w = o₁ := (mem_filter.mp hw).2
    have hw₂ : w ∈ fiberMap o₂ := heq ▸ hw
    exact hw₁.symm.trans (mem_filter.mp hw₂).2
  have hcellSum : ∑ o : O, DecisionProblem.cellProbability dp (fiberMap o) = 1 := by
    simp only [DecisionProblem.cellProbability, hfiberMap]
    rw [sum_fiberwise_of_maps_to (λ w _ => mem_univ (classify w))]
    exact hsum
  have hcell_val : ∀ cell : Finset W,
      DecisionProblem.cellProbability dp cell * DecisionProblem.condValue dp acts cell
        = acts.sup' hacts (λ a => ∑ w ∈ cell, dp.prior w * dp.utility w a) := by
    intro cell
    unfold DecisionProblem.cellProbability DecisionProblem.condValue
    rw [dif_pos hacts]
    have htp_nonneg : 0 ≤ cell.sum dp.prior := sum_nonneg (λ w _ => hprior w)
    by_cases htp : cell.sum dp.prior = 0
    · rw [htp, zero_mul]
      have hpw : ∀ w ∈ cell, dp.prior w = 0 :=
        (sum_eq_zero_iff_of_nonneg (λ w _ => hprior w)).mp htp
      symm
      refine sup'_eq_of_forall hacts _ (λ a _ => ?_)
      exact sum_eq_zero (λ w hw => by rw [hpw w hw, zero_mul])
    · rw [mul₀_sup' htp_nonneg _ acts hacts]
      refine sup'_congr hacts rfl (λ a _ => ?_)
      have hcEU : DecisionProblem.condExpectedUtility dp cell a
          = cell.sum (λ w => dp.prior w / cell.sum dp.prior * dp.utility w a) := by
        show (if cell.sum dp.prior = 0 then (0 : ℚ) else _) = _
        rw [if_neg htp]
      rw [hcEU, mul_sum]
      refine sum_congr rfl (λ w _ => ?_)
      rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_div_cancel_left₀ _ htp]
  have hdpv : decisionValue (λ w a => (dp.utility w a : ℝ)) acts (λ w => (dp.prior w : ℝ))
      = ((DecisionProblem.value dp acts : ℚ) : ℝ) := by
    simp only [decisionValue, DecisionProblem.value, dif_pos hacts]
    rw [show acts.sup' hacts (λ a => ∑ w : W, (dp.prior w : ℝ) * (dp.utility w a : ℝ))
         = acts.sup' hacts (λ a => ((DecisionProblem.expectedUtility dp a : ℚ) : ℝ)) from ?_]
    · exact (apply_sup'_eq_sup'_comp hacts _ (λ x y => Rat.cast_max x y)).symm
    · refine sup'_congr hacts rfl (λ a _ => ?_)
      simp only [DecisionProblem.expectedUtility]; push_cast; rfl
  unfold eig
  rw [hdpv]
  rw [show (∑ o : O, (deterministic classify).marginal (λ w => (dp.prior w : ℝ)) () o *
          decisionValue (λ w a => ((dp.utility w a : ℝ))) acts
            ((deterministic classify).posterior (λ w => ((dp.prior w : ℝ))) () o))
        = ∑ o : O, ((acts.sup' hacts (λ a =>
            ∑ w ∈ fiberMap o, dp.prior w * dp.utility w a) : ℚ) : ℝ) from
      sum_congr rfl (λ o _ => marginal_mul_decisionValue classify dp acts hacts hprior o)]
  rw [← Rat.cast_sum, ← Rat.cast_sub]
  congr 1
  unfold DecisionProblem.questionUtility
  rw [sum_image hinj]
  simp only [DecisionProblem.utilityValue]
  simp_rw [mul_sub]
  rw [sum_sub_distrib]
  rw [show (∑ o : O, DecisionProblem.cellProbability dp (fiberMap o) *
        DecisionProblem.condValue dp acts (fiberMap o))
        = ∑ o : O, acts.sup' hacts (λ a => ∑ w ∈ fiberMap o, dp.prior w * dp.utility w a) from
      sum_congr rfl (λ o _ => hcell_val (fiberMap o))]
  rw [← sum_mul, hcellSum, one_mul]

end ObservationModel

end ProbabilityTheory
