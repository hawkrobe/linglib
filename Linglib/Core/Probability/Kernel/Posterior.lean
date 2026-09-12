import Linglib.Core.Algebra.Order.Chebyshev
import Linglib.Core.MeasureTheory.Measure.Prod
import Linglib.Core.Probability.UniformOn
import Linglib.Core.Data.ENNReal.NNRatCast
import Mathlib.Probability.Kernel.Posterior
import Mathlib.MeasureTheory.Measure.Real

/-!
# Exact Bayes for the posterior kernel at atoms

Mathlib characterizes the posterior kernel `κ†μ` almost everywhere. On discrete spaces an
ae-fact holds at every atom of positive mass (`MeasureTheory.ae_of_singleton_ne_zero`), which
gives Bayes' rule pointwise at any positive-mass observation — no Radon–Nikodym derivative —
and reduces comparisons of posterior masses over finite events, and over the marginals of a
product parameter space, to comparisons of prior-weighted likelihood sums.

## Main results

* `ProbabilityTheory.posterior_apply_singleton` — `(κ†μ) x {ω} = μ {ω} * κ ω {x} / (κ ∘ₘ μ) {x}`.
* `ProbabilityTheory.posterior_deterministic_eq_cond` — a deterministic observation's posterior
  is the prior conditioned on the observation's fibre.
* `ProbabilityTheory.posterior_real_finset_lt_iff` — event comparison of the posterior.
* `ProbabilityTheory.sum_real_mul_le_sum_posterior_real_mul` — conditioning on an observation
  raises the expectation of a statistic that monovaries with the observation's likelihood.
* `ProbabilityTheory.posterior_fst_real_lt_iff`, `posterior_snd_real_lt_iff` — marginal
  comparison over a product parameter space.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- An almost-everywhere property holds at any atom of positive mass. -/
theorem ae_of_singleton_ne_zero {ν : Measure α} {P : α → Prop}
    (h : ∀ᵐ x ∂ν, P x) {x : α} (hx : ν {x} ≠ 0) : P x := by
  by_contra hP
  exact hx (measure_mono_null (fun y hy => (Set.mem_singleton_iff.mp hy) ▸ hP) h)

end MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]
  [MeasurableSingletonClass Ω] [MeasurableSingletonClass 𝓧]
  [StandardBorelSpace Ω] [Nonempty Ω]
  (κ : Kernel Ω 𝓧) (μ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteKernel κ]

/-- Exact Bayes for the posterior kernel at a positive-mass observation:
evaluate the defining compProd identity on a singleton rectangle. -/
theorem posterior_apply_singleton {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (ω : Ω) :
    (κ†μ) x {ω} = μ {ω} * κ ω {x} / (κ ∘ₘ μ) {x} := by
  have hrect := congrArg (fun m => m ({x} ×ˢ {ω}))
    (compProd_posterior_eq_map_swap (κ := κ) (μ := μ))
  beta_reduce at hrect
  rw [Measure.compProd_apply_prod (.singleton x) (.singleton ω),
    Measure.map_apply measurable_swap ((MeasurableSet.singleton x).prod (.singleton ω)),
    Set.preimage_swap_prod,
    Measure.compProd_apply_prod (.singleton ω) (.singleton x),
    lintegral_singleton, lintegral_singleton] at hrect
  rw [ENNReal.eq_div_iff hx (measure_ne_top _ _), mul_comm]
  rw [hrect]
  ring

/-- The posterior is positive at a state exactly when the prior and the likelihood are. -/
theorem posterior_apply_singleton_ne_zero_iff {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (ω : Ω) :
    (κ†μ) x {ω} ≠ 0 ↔ μ {ω} ≠ 0 ∧ κ ω {x} ≠ 0 := by
  rw [posterior_apply_singleton κ μ hx, ne_eq, ENNReal.div_eq_zero_iff, mul_eq_zero, not_or,
    not_or]
  exact ⟨λ h => h.1, λ h => ⟨h, measure_ne_top _ _⟩⟩

/-- Two states with the same likelihood of the observation and the same prior mass have the
same posterior mass. -/
theorem posterior_apply_singleton_congr {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) {ω₁ ω₂ : Ω}
    (hrow : κ ω₁ {x} = κ ω₂ {x}) (hμ : μ {ω₁} = μ {ω₂}) : (κ†μ) x {ω₁} = (κ†μ) x {ω₂} := by
  rw [posterior_apply_singleton κ μ hx, posterior_apply_singleton κ μ hx, hrow, hμ]

/-- Comparing posterior masses of finite events reduces to comparing prior-weighted
likelihood sums; the observation marginal cancels. -/
theorem posterior_real_finset_lt_iff {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (E₁ E₂ : Finset Ω) :
    ((κ†μ) x).real ↑E₁ < ((κ†μ) x).real ↑E₂
      ↔ (∑ ω ∈ E₁, μ.real {ω} * (κ ω).real {x}) < ∑ ω ∈ E₂, μ.real {ω} * (κ ω).real {x} := by
  have hne : ∀ E : Finset Ω, (∑ ω ∈ E, μ {ω} * κ ω {x}) ≠ ∞ := fun E =>
    ENNReal.sum_ne_top.mpr fun ω _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, ← sum_measure_singleton, ← sum_measure_singleton]
  simp_rw [posterior_apply_singleton κ μ hx, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne E₁) hx) (ENNReal.div_ne_top (hne E₂) hx),
    ENNReal.div_lt_div_iff_left hx (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne E₁) (hne E₂),
    ENNReal.toReal_sum (fun ω _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun ω _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

/-- The posterior mass of a finite event: prior-weighted likelihoods over the event,
normalized by the observation marginal. -/
theorem posterior_apply_finset {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (E : Finset Ω) :
    (κ†μ) x ↑E = (∑ ω ∈ E, μ {ω} * κ ω {x}) / (κ ∘ₘ μ) {x} := by
  rw [← sum_measure_singleton]
  simp_rw [posterior_apply_singleton κ μ hx, div_eq_mul_inv]
  rw [Finset.sum_mul]

/-- A deterministic observation's posterior is the prior conditioned on the observation's
fibre. -/
theorem posterior_deterministic_eq_cond [Countable Ω] {f : Ω → 𝓧} (hf : Measurable f) {x : 𝓧}
    (hx : μ (f ⁻¹' {x}) ≠ 0) : ((Kernel.deterministic f hf)†μ) x = μ[|f ⁻¹' {x}] := by
  have hx' : (Kernel.deterministic f hf ∘ₘ μ) {x} ≠ 0 := by
    rwa [Measure.deterministic_comp_eq_map, Measure.map_apply hf (measurableSet_singleton x)]
  refine Measure.ext_of_singleton fun ω => ?_
  rw [posterior_apply_singleton _ _ hx', cond_apply (hf (measurableSet_singleton x)),
    Measure.deterministic_comp_eq_map, Measure.map_apply hf (measurableSet_singleton x),
    Kernel.deterministic_apply' hf ω (measurableSet_singleton x)]
  by_cases h : f ω = x
  · rw [Set.indicator_of_mem (Set.mem_singleton_iff.mpr h), mul_one, div_eq_mul_inv, mul_comm,
      Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr (show ω ∈ f ⁻¹' {x} from h))]
  · rw [Set.indicator_of_notMem (by simpa using h), mul_zero, ENNReal.zero_div,
      Set.inter_singleton_eq_empty.mpr (by simpa using h), measure_empty, mul_zero]

omit [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ] [IsFiniteKernel κ] in
/-- The observation marginal at an atom: prior mass times emission mass, summed over states. -/
theorem _root_.MeasureTheory.Measure.comp_apply_singleton [Fintype Ω] (x : 𝓧) :
    (κ ∘ₘ μ) {x} = ∑ ω, μ {ω} * κ ω {x} := by
  rw [Measure.bind_apply (.singleton x) (Kernel.aemeasurable _), lintegral_fintype]
  exact Finset.sum_congr rfl fun ω _ => mul_comm _ _

omit [StandardBorelSpace Ω] [Nonempty Ω] in
theorem _root_.MeasureTheory.Measure.comp_real_singleton [Fintype Ω] (x : 𝓧) :
    (κ ∘ₘ μ).real {x} = ∑ ω, μ.real {ω} * (κ ω).real {x} := by
  rw [measureReal_def, Measure.comp_apply_singleton,
    ENNReal.toReal_sum fun ω _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  simp_rw [ENNReal.toReal_mul, measureReal_def]

/-- Exact Bayes on reals at a positive-mass observation. -/
theorem posterior_real_singleton {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (ω : Ω) :
    ((κ†μ) x).real {ω} = μ.real {ω} * (κ ω).real {x} / (κ ∘ₘ μ).real {x} := by
  rw [measureReal_def, posterior_apply_singleton κ μ hx, ENNReal.toReal_div, ENNReal.toReal_mul,
    measureReal_def, measureReal_def, measureReal_def]

/-- The posterior exceeds the prior at a state exactly when the state's likelihood of the
observation exceeds the observation's marginal. -/
theorem real_lt_posterior_real_singleton_iff {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) {ω : Ω}
    (hω : μ {ω} ≠ 0) :
    μ.real {ω} < ((κ†μ) x).real {ω} ↔ (κ ∘ₘ μ).real {x} < (κ ω).real {x} := by
  have hm : 0 < (κ ∘ₘ μ).real {x} := ENNReal.toReal_pos hx (measure_ne_top _ _)
  have hμ : 0 < μ.real {ω} := ENNReal.toReal_pos hω (measure_ne_top _ _)
  rw [posterior_real_singleton κ μ hx, lt_div_iff₀ hm, mul_lt_mul_iff_of_pos_left hμ]

/-- The posterior falls below the prior at a state exactly when the state's likelihood of the
observation falls below the observation's marginal. -/
theorem posterior_real_singleton_lt_iff {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) {ω : Ω}
    (hω : μ {ω} ≠ 0) :
    ((κ†μ) x).real {ω} < μ.real {ω} ↔ (κ ω).real {x} < (κ ∘ₘ μ).real {x} := by
  have hm : 0 < (κ ∘ₘ μ).real {x} := ENNReal.toReal_pos hx (measure_ne_top _ _)
  have hμ : 0 < μ.real {ω} := ENNReal.toReal_pos hω (measure_ne_top _ _)
  rw [posterior_real_singleton κ μ hx, div_lt_iff₀ hm, mul_lt_mul_iff_of_pos_left hμ]

/-! ### Expectations under the posterior

Bayes' rule reweights the prior by the likelihood, so the posterior expectation of a statistic
compares with its prior expectation as the statistic's covariance with the likelihood: the
weighted Chebyshev sum inequality. -/

section Expectation

variable [Fintype Ω] [IsProbabilityMeasure μ] {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) {f : Ω → ℝ}
include hx

/-- Conditioning on an observation raises the expectation of a statistic that monovaries with
the observation's likelihood. -/
theorem sum_real_mul_le_sum_posterior_real_mul (hf : Monovary f λ ω => (κ ω).real {x}) :
    ∑ ω, μ.real {ω} * f ω ≤ ∑ ω, ((κ†μ) x).real {ω} * f ω := by
  have hm : 0 < (κ ∘ₘ μ).real {x} := ENNReal.toReal_pos hx (measure_ne_top _ _)
  have h1 : ∑ ω, μ.real {ω} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have h := hf.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul (w := λ ω => μ.real {ω})
    λ _ => measureReal_nonneg
  rw [h1, one_mul] at h
  simp_rw [posterior_real_singleton κ μ hx, div_mul_eq_mul_div, ← Finset.sum_div,
    le_div_iff₀ hm, Measure.comp_real_singleton]
  exact h.trans (le_of_eq (Finset.sum_congr rfl λ ω _ => by ring))

/-- Conditioning on an observation lowers the expectation of a statistic that antivaries with
the observation's likelihood. -/
theorem sum_posterior_real_mul_le_sum_real_mul (hf : Antivary f λ ω => (κ ω).real {x}) :
    ∑ ω, ((κ†μ) x).real {ω} * f ω ≤ ∑ ω, μ.real {ω} * f ω := by
  have hm : 0 < (κ ∘ₘ μ).real {x} := ENNReal.toReal_pos hx (measure_ne_top _ _)
  have h1 : ∑ ω, μ.real {ω} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have h := hf.sum_mul_sum_mul_mul_le_sum_mul_mul_sum_mul (w := λ ω => μ.real {ω})
    λ _ => measureReal_nonneg
  rw [h1, one_mul] at h
  simp_rw [posterior_real_singleton κ μ hx, div_mul_eq_mul_div, ← Finset.sum_div,
    div_le_iff₀ hm, Measure.comp_real_singleton]
  exact (le_of_eq (Finset.sum_congr rfl λ ω _ => by ring)).trans h

end Expectation

/-! ### Priors carried by two atoms

The `_of_pair` lemmas assume the prior's support lies in a pair `{ω, ω'}`, so that the
observation's marginal has two terms and the comparison of the posterior with the prior at
one atom is the comparison of the two likelihoods. -/

section Pair

variable [Fintype Ω] {ω ω' : Ω} (hne : ω ≠ ω') (hsupp : ∀ ω'', μ {ω''} ≠ 0 → ω'' = ω ∨ ω'' = ω')
include hne hsupp

omit [StandardBorelSpace Ω] [Nonempty Ω] in
/-- Under a prior carried by two atoms, the observation's marginal is the prior-weighted sum
of the two likelihoods. -/
theorem _root_.MeasureTheory.Measure.comp_real_singleton_of_pair (x : 𝓧) :
    (κ ∘ₘ μ).real {x} = μ.real {ω} * (κ ω).real {x} + μ.real {ω'} * (κ ω').real {x} := by
  rw [Measure.comp_real_singleton]
  exact Fintype.sum_eq_add ω ω' hne λ c hc => by
    rw [measureReal_def, of_not_not (mt (hsupp c) (not_or.mpr hc)), ENNReal.toReal_zero, zero_mul]

omit [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteKernel κ] in
/-- A probability measure carried by two atoms puts mass one on them together. -/
theorem _root_.MeasureTheory.measureReal_singleton_add_singleton_of_pair
    [IsProbabilityMeasure μ] : μ.real {ω} + μ.real {ω'} = 1 := by
  have h := measure_univ (μ := μ)
  rw [← Finset.coe_univ, ← sum_measure_singleton,
    Fintype.sum_eq_add ω ω' hne (λ c hc => of_not_not (mt (hsupp c) (not_or.mpr hc)))] at h
  rw [measureReal_def, measureReal_def,
    ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h, ENNReal.toReal_one]

variable [IsProbabilityMeasure μ] {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (hω : μ {ω} ≠ 0)
  (hω' : μ {ω'} ≠ 0)
include hx hω hω'

/-- Under a prior carried by two atoms, the posterior exceeds the prior at one of them exactly
when its likelihood of the observation exceeds the other's. -/
theorem real_lt_posterior_real_singleton_iff_of_pair :
    μ.real {ω} < ((κ†μ) x).real {ω} ↔ (κ ω').real {x} < (κ ω).real {x} := by
  have h1 := measureReal_singleton_add_singleton_of_pair μ hne hsupp
  have h2 : 0 < μ.real {ω'} := ENNReal.toReal_pos hω' (measure_ne_top _ _)
  rw [real_lt_posterior_real_singleton_iff κ μ hx hω,
    Measure.comp_real_singleton_of_pair κ μ hne hsupp,
    show μ.real {ω} = 1 - μ.real {ω'} by linarith]
  constructor <;> intro h <;> nlinarith

/-- Under a prior carried by two atoms, the posterior falls below the prior at one of them
exactly when its likelihood of the observation falls below the other's. -/
theorem posterior_real_singleton_lt_iff_of_pair :
    ((κ†μ) x).real {ω} < μ.real {ω} ↔ (κ ω).real {x} < (κ ω').real {x} := by
  have h1 := measureReal_singleton_add_singleton_of_pair μ hne hsupp
  have h2 : 0 < μ.real {ω'} := ENNReal.toReal_pos hω' (measure_ne_top _ _)
  rw [posterior_real_singleton_lt_iff κ μ hx hω,
    Measure.comp_real_singleton_of_pair κ μ hne hsupp,
    show μ.real {ω} = 1 - μ.real {ω'} by linarith]
  constructor <;> intro h <;> nlinarith

end Pair

/-- A single state of positive prior mass and positive emission witnesses a
positive observation marginal. -/
theorem comp_apply_singleton_ne_zero {Ω' 𝓧' : Type*} [MeasurableSpace Ω']
    [MeasurableSpace 𝓧'] [MeasurableSingletonClass 𝓧'] (κ : Kernel Ω' 𝓧')
    (μ : Measure Ω') {w : Ω'} {x : 𝓧'} (hμ : μ {w} ≠ 0) (hκ : κ w {x} ≠ 0) :
    (κ ∘ₘ μ) {x} ≠ 0 := by
  rw [Measure.bind_apply (.singleton x) (Kernel.aemeasurable _),
    ← pos_iff_ne_zero, lintegral_pos_iff_support (Kernel.measurable_coe _ (.singleton x))]
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hμ)
    (measure_mono (Set.singleton_subset_iff.mpr hκ))

end ProbabilityTheory

namespace MeasureTheory.Measure

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
  [MeasurableSingletonClass Ω] [MeasurableSingletonClass Θ]

/-- A prior-times-kernel joint at an atom is the prior mass times the kernel's mass. -/
theorem compProd_apply_singleton (μ : Measure Ω) [SFinite μ] (κ : Kernel Ω Θ)
    [IsSFiniteKernel κ] (ω : Ω) (θ : Θ) : (μ ⊗ₘ κ) {(ω, θ)} = μ {ω} * κ ω {θ} := by
  rw [← Set.singleton_prod_singleton, compProd_apply_prod (.singleton ω) (.singleton θ),
    lintegral_singleton, mul_comm]

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {𝓧 : Type*} [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧]

section Prod

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A]
  [MeasurableSingletonClass B] [StandardBorelSpace A] [Nonempty A] [StandardBorelSpace B]
  [Nonempty B] (κ : Kernel (A × B) 𝓧) (μ : Measure (A × B)) [IsFiniteMeasure μ]
  [IsFiniteKernel κ] {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0)
include hx

/-- The state marginal of the posterior over a product parameter space, on reals:
prior-weighted likelihoods pooled over the latent, normalized by the observation marginal. -/
theorem posterior_fst_real_singleton [Fintype B] (a : A) :
    ((κ†μ) x).fst.real {a}
      = (∑ b, μ.real {(a, b)} * (κ (a, b)).real {x}) / (κ ∘ₘ μ).real {x} := by
  rw [Measure.fst_real_singleton_eq_sum, Finset.sum_div]
  exact Finset.sum_congr rfl λ b _ => posterior_real_singleton κ μ hx (a, b)

/-- The latent marginal of the posterior over a product parameter space, on reals:
prior-weighted likelihoods pooled over the states, normalized by the observation marginal. -/
theorem posterior_snd_real_singleton [Fintype A] (b : B) :
    ((κ†μ) x).snd.real {b}
      = (∑ a, μ.real {(a, b)} * (κ (a, b)).real {x}) / (κ ∘ₘ μ).real {x} := by
  rw [Measure.snd_real_singleton_eq_sum, Finset.sum_div]
  exact Finset.sum_congr rfl λ a _ => posterior_real_singleton κ μ hx (a, b)

/-- Marginal listener preference over a product parameter space, on reals:
for latent-in-the-state models, the observation's marginal cancels and the
latent pools. -/
theorem posterior_fst_real_lt_iff [Fintype B] (a₁ a₂ : A) :
    ((κ†μ) x).fst.real {a₁} < ((κ†μ) x).fst.real {a₂}
      ↔ (∑ b, μ.real {(a₁, b)} * (κ (a₁, b)).real {x})
          < ∑ b, μ.real {(a₂, b)} * (κ (a₂, b)).real {x} := by
  have hne : ∀ a : A, (∑ b, μ {(a, b)} * κ (a, b) {x}) ≠ ∞ := fun a =>
    ENNReal.sum_ne_top.mpr fun b _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, Measure.fst_apply_singleton,
    Measure.fst_apply_singleton]
  simp_rw [posterior_apply_singleton κ μ hx, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne a₁) hx)
      (ENNReal.div_ne_top (hne a₂) hx),
    ENNReal.div_lt_div_iff_left hx (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne a₁) (hne a₂),
    ENNReal.toReal_sum (fun b _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun b _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

/-- Marginal listener preference over the latent component of a product
parameter space, on reals: the states pool. -/
theorem posterior_snd_real_lt_iff [Fintype A] (b₁ b₂ : B) :
    ((κ†μ) x).snd.real {b₁} < ((κ†μ) x).snd.real {b₂}
      ↔ (∑ a, μ.real {(a, b₁)} * (κ (a, b₁)).real {x})
          < ∑ a, μ.real {(a, b₂)} * (κ (a, b₂)).real {x} := by
  have hne : ∀ b : B, (∑ a, μ {(a, b)} * κ (a, b) {x}) ≠ ∞ := fun b =>
    ENNReal.sum_ne_top.mpr fun a _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_def, measureReal_def, Measure.snd_apply_singleton,
    Measure.snd_apply_singleton]
  simp_rw [posterior_apply_singleton κ μ hx, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (hne b₁) hx)
      (ENNReal.div_ne_top (hne b₂) hx),
    ENNReal.div_lt_div_iff_left hx (measure_ne_top _ _),
    ← ENNReal.toReal_lt_toReal (hne b₁) (hne b₂),
    ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul]
  exact Iff.rfl

end Prod

section UniformPrior

variable {W : Type*} [MeasurableSpace W] [MeasurableSingletonClass W] [StandardBorelSpace W]
  [Fintype W] [Nonempty W] (κ : Kernel W 𝓧) [IsFiniteKernel κ]

omit [StandardBorelSpace W] [Nonempty W] [IsFiniteKernel κ] in
/-- The observation marginal of a kernel against the uniform prior: the mean likelihood. -/
theorem comp_uniformOn_univ_apply_singleton (x : 𝓧) :
    (κ ∘ₘ uniformOn (Set.univ : Set W)) {x} = (Fintype.card W : ℝ≥0∞)⁻¹ * ∑ w, κ w {x} := by
  rw [Measure.comp_apply_singleton, Finset.mul_sum]
  exact Finset.sum_congr rfl λ w _ => by rw [uniformOn_univ_apply_singleton]

/-- Bayes against the uniform prior: the posterior at a state is its likelihood of the
observation normalized over the states, the prior cancelling. -/
theorem posterior_uniformOn_univ_apply_singleton {x : 𝓧} (hx : ∑ w, κ w {x} ≠ 0) (w : W) :
    (κ†(uniformOn (Set.univ : Set W))) x {w} = κ w {x} / ∑ w', κ w' {x} := by
  have hc : (Fintype.card W : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hct : (Fintype.card W : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hsum : (κ ∘ₘ uniformOn (Set.univ : Set W)) {x} ≠ 0 := by
    rw [comp_uniformOn_univ_apply_singleton]; exact mul_ne_zero hc hx
  rw [posterior_apply_singleton _ _ hsum, uniformOn_univ_apply_singleton,
    comp_uniformOn_univ_apply_singleton, ENNReal.mul_div_mul_left _ _ hc hct]

open scoped NNRat in
/-- The exact register: a kernel with rational rows has, against the uniform prior, the
rational posterior that is the state's share of the observation's column. -/
theorem posterior_uniformOn_univ_nnratCast_apply_singleton (q : W → 𝓧 → ℚ≥0)
    (hκ : ∀ w x, κ w {x} = q w x) {x : 𝓧} (hx : ∑ w, q w x ≠ 0) (w : W) :
    (κ†(uniformOn (Set.univ : Set W))) x {w} = ((q w x / ∑ w', q w' x : ℚ≥0) : ℝ≥0∞) := by
  rw [posterior_uniformOn_univ_apply_singleton κ (by
      simp only [hκ, ← ENNReal.nnratCast_sum, ne_eq, ENNReal.nnratCast_eq_zero]; exact hx),
    ENNReal.nnratCast_div _ _ hx, ENNReal.nnratCast_sum]
  simp only [hκ]

end UniformPrior

end ProbabilityTheory
