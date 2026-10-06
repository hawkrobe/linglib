/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Kernel.Posterior
public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Decision.Risk.Basic
public import Mathlib.Probability.Decision.Risk.RiskIncrease

/-!
# The value of information of an experiment

An experiment is a Markov kernel `κ : Kernel Θ 𝓧` that draws an observation from a parameter.
An agent with prior `π` who values a belief `μ` at `V μ` expects, before observing, the value
of the posterior `κ†π`; the value of information `valueOfInformation V κ π` is that expectation
less the value of the prior. DeGroot calls it the information in the experiment when `V` is the
negative of an uncertainty function, and Lindley's measure of information is the case of
Shannon entropy.

The decision value `decisionValue U μ` of a belief is the best expected utility of an action.
For it, the value of information is the risk increase of mathlib's decision theory at the
regret loss `C − U`, so information never has negative value, and garbling an experiment never
raises its value, the forward direction of Blackwell's comparison of experiments.

## Main definitions

* `valueOfInformation V κ π`: the expected value of the posterior less the value of the prior.
* `decisionValue U μ`: the best expected utility of an action under the belief `μ`.

## Main statements

* `hasArgminEstimator_of_finite`: with countably many observations and finitely many actions,
  a pointwise minimizer of the posterior expected loss is an argmin estimator.
* `riskIncrease_ofReal_sub`: at the regret loss, the risk increase is the value of information
  of the decision value.
* `valueOfInformation_decisionValue_nonneg`: information has nonnegative value.
* `valueOfInformation_decisionValue_comp_le`: a garbled experiment is worth no more.
* `valueOfInformation_const`: an experiment whose law does not depend on the parameter is
  worth nothing.

## Implementation notes

The decision value is a supremum over the action type, `0` when there is no action. The
theorems about it assume finitely many parameters, observations and actions, and the regret
bound `C` stays inside the proofs of the inequalities.

## References

* [degroot-1962]
* [lindley-1956]
* [blackwell-1953]
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}

section ArgminEstimator

variable {m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace Θ] [Nonempty Θ] [Countable 𝓧]
  [MeasurableSingletonClass 𝓧] [Finite 𝓨] [Nonempty 𝓨]

/-- With countably many observations and finitely many estimates, choosing a minimizer of the
posterior expected loss at each observation gives an argmin estimator. -/
theorem hasArgminEstimator_of_finite (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] : HasArgminEstimator ℓ P π := by
  choose f hf using fun x ↦ Finite.exists_min fun y ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x
  exact ⟨f, ⟨measurable_of_countable f, ae_of_all _ fun x ↦
    le_antisymm (le_iInf (hf x)) (iInf_le _ _)⟩⟩

end ArgminEstimator

/-- The value of information of the experiment `κ` to an agent with prior `π` who values a
belief by `V` is the expected value of the posterior less the value of the prior. -/
noncomputable def valueOfInformation [StandardBorelSpace Θ] [Nonempty Θ] (V : Measure Θ → ℝ)
    (κ : Kernel Θ 𝓧) [IsFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π] : ℝ :=
  ∫ x, V ((κ†π) x) ∂(κ ∘ₘ π) - V π

/-- The decision value of a belief `μ` is the best expected utility of an action under `μ`. -/
noncomputable def decisionValue (U : Θ → 𝓨 → ℝ) (μ : Measure Θ) : ℝ := ⨆ a, ∫ θ, U θ a ∂μ

section Basic

variable [StandardBorelSpace Θ] [Nonempty Θ] (κ : Kernel Θ 𝓧) [IsFiniteKernel κ]
  (π : Measure Θ) [IsFiniteMeasure π]

theorem valueOfInformation_smul (V : Measure Θ → ℝ) (c : ℝ) :
    valueOfInformation (c • V) κ π = c * valueOfInformation V κ π := by
  simp only [valueOfInformation, Pi.smul_apply, smul_eq_mul, integral_const_mul, mul_sub]

omit [IsFiniteKernel κ] in
/-- An experiment whose law does not depend on the parameter is worth nothing. -/
theorem valueOfInformation_const (V : Measure Θ → ℝ) (ν : Measure 𝓧) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π] : valueOfInformation V (Kernel.const Θ ν) π = 0 := by
  rw [valueOfInformation, Measure.const_comp, measure_univ, one_smul, sub_eq_zero,
    integral_congr_ae ((posterior_const ν π).mono fun x hx ↦ congrArg V hx)]
  simp

end Basic

section DecisionValue

variable {U : Θ → 𝓨 → ℝ}

theorem decisionValue_smul {c : ℝ} (hc : 0 ≤ c) (μ : Measure Θ) :
    decisionValue (c • U) μ = c * decisionValue U μ := by
  simp only [decisionValue, Pi.smul_apply, smul_eq_mul, integral_const_mul,
    Real.mul_iSup_of_nonneg hc]

variable [Finite 𝓨]

theorem integral_le_decisionValue (μ : Measure Θ) (a : 𝓨) : ∫ θ, U θ a ∂μ ≤ decisionValue U μ :=
  le_ciSup (f := fun a ↦ ∫ θ, U θ a ∂μ) (Set.finite_range _).bddAbove a

end DecisionValue

/-! ### The decision value and the risk increase -/

section Regret

variable [Finite Θ] [MeasurableSingletonClass Θ] [Finite 𝓨] [Nonempty 𝓨] {U : Θ → 𝓨 → ℝ}
  {C : ℝ} (hC : ∀ θ a, U θ a ≤ C)
include hC

omit [Finite 𝓨] in
theorem decisionValue_le (μ : Measure Θ) [IsProbabilityMeasure μ] : decisionValue U μ ≤ C :=
  ciSup_le fun a ↦ (integral_mono .of_finite (integrable_const C) (hC · a)).trans (by simp)

/-- At a bound `C` on the utilities, the least expected regret `C − U` of an action is `C` less
the decision value. -/
theorem iInf_lintegral_ofReal_sub (μ : Measure Θ) [IsProbabilityMeasure μ] :
    ⨅ a, ∫⁻ θ, ENNReal.ofReal (C - U θ a) ∂μ = ENNReal.ofReal (C - decisionValue U μ) := by
  have h a : ∫⁻ θ, ENNReal.ofReal (C - U θ a) ∂μ = ENNReal.ofReal (C - ∫ θ, U θ a ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal .of_finite
        (ae_of_all _ fun θ ↦ sub_nonneg.2 (hC θ a)),
      integral_sub (integrable_const C) .of_finite, integral_const, probReal_univ, one_smul]
  simp_rw [h]
  obtain ⟨a, ha⟩ := Finite.exists_max fun a ↦ ∫ θ, U θ a ∂μ
  have hv : decisionValue U μ = ∫ θ, U θ a ∂μ :=
    le_antisymm (ciSup_le ha) (integral_le_decisionValue μ a)
  rw [hv]
  exact le_antisymm (iInf_le _ a) (le_iInf fun b ↦ ENNReal.ofReal_le_ofReal (by linarith [ha b]))

variable [StandardBorelSpace Θ] [Nonempty Θ] [Finite 𝓧] [MeasurableSingletonClass 𝓧]
  (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (π : Measure Θ) [IsProbabilityMeasure π]

omit [Finite 𝓨] in
private theorem integral_decisionValue_posterior_le :
    ∫ x, decisionValue U ((κ†π) x) ∂(κ ∘ₘ π) ≤ C :=
  (integral_mono .of_finite (integrable_const C) fun _ ↦ decisionValue_le hC _).trans (by simp)

variable [MeasurableSpace 𝓨] [MeasurableSingletonClass 𝓨]

/-- At the regret loss `C − U`, the Bayes risk of an experiment is `C` less the expected
decision value of the posterior. -/
theorem bayesRisk_ofReal_sub :
    bayesRisk (fun θ a ↦ ENNReal.ofReal (C - U θ a)) κ π =
      ENNReal.ofReal (C - ∫ x, decisionValue U ((κ†π) x) ∂(κ ∘ₘ π)) := by
  rw [(hasArgminEstimator_of_finite _ κ π).bayesRisk_eq (measurable_of_countable _)]
  simp_rw [iInf_lintegral_ofReal_sub hC]
  rw [← ofReal_integral_eq_lintegral_ofReal .of_finite
      (ae_of_all _ fun x ↦ sub_nonneg.2 (decisionValue_le hC _)),
    integral_sub (integrable_const C) .of_finite, integral_const, probReal_univ, one_smul]

/-- At the regret loss `C − U`, the risk increase of an experiment is the value of information
of the decision value. -/
theorem riskIncrease_ofReal_sub :
    riskIncrease (fun θ a ↦ ENNReal.ofReal (C - U θ a)) κ π =
      ENNReal.ofReal (valueOfInformation (decisionValue U) κ π) := by
  rw [riskIncrease_eq_iInf_sub (measurable_of_countable _), bayesRisk_ofReal_sub hC,
    iInf_lintegral_ofReal_sub hC,
    ← ENNReal.ofReal_sub _ (sub_nonneg.2 (integral_decisionValue_posterior_le hC κ π)),
    valueOfInformation]
  congr 1
  ring

end Regret

section Inequalities

variable [Finite Θ] [MeasurableSingletonClass Θ] [StandardBorelSpace Θ] [Nonempty Θ] [Finite 𝓧]
  [MeasurableSingletonClass 𝓧] [Finite 𝓨] (U : Θ → 𝓨 → ℝ) (κ : Kernel Θ 𝓧) [IsMarkovKernel κ]
  (π : Measure Θ) [IsProbabilityMeasure π]

/-- Information has nonnegative value to an expected-utility maximizer. -/
theorem valueOfInformation_decisionValue_nonneg : 0 ≤ valueOfInformation (decisionValue U) κ π := by
  rcases isEmpty_or_nonempty 𝓨 with h𝓨 | h𝓨
  · simp [valueOfInformation, decisionValue]
  let _ : MeasurableSpace 𝓨 := ⊤
  have : MeasurableSingletonClass 𝓨 := ⟨fun _ ↦ trivial⟩
  obtain ⟨C, hC⟩ := Finite.exists_le (Function.uncurry U)
  replace hC : ∀ θ a, U θ a ≤ C := fun θ a ↦ hC (θ, a)
  have h := bayesRisk_le_iInf (m𝓨 := inferInstance)
    (measurable_of_countable (Function.uncurry fun θ a ↦ ENNReal.ofReal (C - U θ a))) κ π
  rw [bayesRisk_ofReal_sub hC, iInf_lintegral_ofReal_sub hC,
    ENNReal.ofReal_le_ofReal_iff (sub_nonneg.2 (decisionValue_le hC π))] at h
  rw [valueOfInformation]
  linarith

/-- Garbling an experiment cannot raise its value to an expected-utility maximizer. -/
theorem valueOfInformation_decisionValue_comp_le {𝓧' : Type*} {m𝓧' : MeasurableSpace 𝓧'}
    [Finite 𝓧'] [MeasurableSingletonClass 𝓧'] (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    valueOfInformation (decisionValue U) (η ∘ₖ κ) π ≤ valueOfInformation (decisionValue U) κ π := by
  rcases isEmpty_or_nonempty 𝓨 with h𝓨 | h𝓨
  · simp [valueOfInformation, decisionValue]
  let _ : MeasurableSpace 𝓨 := ⊤
  have : MeasurableSingletonClass 𝓨 := ⟨fun _ ↦ trivial⟩
  obtain ⟨C, hC⟩ := Finite.exists_le (Function.uncurry U)
  replace hC : ∀ θ a, U θ a ≤ C := fun θ a ↦ hC (θ, a)
  have h := riskIncrease_comp_le (fun θ a ↦ ENNReal.ofReal (C - U θ a)) κ π η
  rwa [riskIncrease_ofReal_sub hC, riskIncrease_ofReal_sub hC,
    ENNReal.ofReal_le_ofReal_iff (valueOfInformation_decisionValue_nonneg U κ π)] at h

end Inequalities

end ProbabilityTheory
