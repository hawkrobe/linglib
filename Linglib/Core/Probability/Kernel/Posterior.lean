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

theorem fst_apply_singleton [Fintype Θ] (m : Measure (Ω × Θ)) (ω : Ω) :
    m.fst {ω} = ∑ θ : Θ, m {(ω, θ)} := by
  rw [Measure.fst_apply (.singleton ω),
    show Prod.fst ⁻¹' ({ω} : Set Ω) = ↑(({ω} : Finset Ω) ×ˢ (Finset.univ : Finset Θ)) from by
      ext ⟨a, θ⟩; simp [eq_comm],
    ← sum_measure_singleton, Finset.sum_product, Finset.sum_singleton]

theorem snd_apply_singleton [Fintype Ω] (m : Measure (Ω × Θ)) (θ : Θ) :
    m.snd {θ} = ∑ ω : Ω, m {(ω, θ)} := by
  rw [Measure.snd_apply (.singleton θ),
    show Prod.snd ⁻¹' ({θ} : Set Θ) = ↑((Finset.univ : Finset Ω) ×ˢ ({θ} : Finset Θ)) from by
      ext ⟨a, b⟩; simp [eq_comm],
    ← sum_measure_singleton, Finset.sum_product]
  exact Finset.sum_congr rfl fun ω _ => Finset.sum_singleton _ _

/-- The state marginal at a singleton is the mass of the corresponding product event. -/
theorem fst_real_singleton [Fintype Θ] (m : Measure (Ω × Θ)) (ω : Ω) :
    m.fst.real {ω} = m.real ↑(({ω} : Finset Ω) ×ˢ (Finset.univ : Finset Θ)) := by
  rw [measureReal_def, measureReal_def, fst_apply_singleton, ← sum_measure_singleton,
    Finset.sum_product, Finset.sum_singleton]

/-- The latent marginal at a singleton is the mass of the corresponding product event. -/
theorem snd_real_singleton [Fintype Ω] (m : Measure (Ω × Θ)) (θ : Θ) :
    m.snd.real {θ} = m.real ↑((Finset.univ : Finset Ω) ×ˢ ({θ} : Finset Θ)) := by
  rw [measureReal_def, measureReal_def, snd_apply_singleton, ← sum_measure_singleton,
    Finset.sum_product]
  exact congrArg _ (Finset.sum_congr rfl fun ω _ => (Finset.sum_singleton _ _).symm)

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {𝓧 : Type*} [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧]

/-- Marginal listener preference over a product parameter space, on reals:
for latent-in-the-state models, the observation's marginal cancels and the
latent pools. -/
theorem posterior_fst_real_lt_iff {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [Fintype B]
    [StandardBorelSpace A] [Nonempty A] [StandardBorelSpace B] [Nonempty B]
    (κ : Kernel (A × B) 𝓧) (μ : Measure (A × B)) [IsFiniteMeasure μ] [IsFiniteKernel κ]
    {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (a₁ a₂ : A) :
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
theorem posterior_snd_real_lt_iff {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [Fintype A]
    [StandardBorelSpace A] [Nonempty A] [StandardBorelSpace B] [Nonempty B]
    (κ : Kernel (A × B) 𝓧) (μ : Measure (A × B)) [IsFiniteMeasure μ] [IsFiniteKernel κ]
    {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (b₁ b₂ : B) :
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

end ProbabilityTheory
