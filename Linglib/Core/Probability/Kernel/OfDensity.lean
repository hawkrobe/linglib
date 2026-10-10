module

public import Linglib.Core.MeasureTheory.Measure.WithDensity
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Core.Probability.Kernel.Posterior

/-!
# Kernels from a density against a base measure

This file defines `ProbabilityTheory.Kernel.ofDensity`, the kernel whose row at `a` reweights a
base measure by the density `f a` and normalizes. It is Bayes' rule for a likelihood given as a
function: with the prior as base and the likelihood of an observation as density, the row is the
posterior. A row whose density has zero or infinite total mass collapses to the zero measure, so
the kernel is always finite.

## Main definitions

* `ProbabilityTheory.Kernel.ofDensity`: row `a` is proportional to `μ.withDensity (f a)`.

## Main results

* `ProbabilityTheory.Kernel.ofDensity_apply_singleton`: the mass of an atom is its density times
  its base mass, over the total.
* `ProbabilityTheory.Kernel.ofDensity_indicator_one_apply`: at an indicator density the row is the
  base measure conditioned on the set.
* `ProbabilityTheory.Kernel.ofDensity_count`: against the counting measure the density kernel is
  the weight kernel `Kernel.ofWeights`.
* `ProbabilityTheory.Kernel.ofDensity_apply_eq_posterior`: with a kernel's likelihood as density
  the row is the posterior, at every observation of positive marginal.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable α]
  [MeasurableSingletonClass α]

/-- The kernel that reweights a base measure by a density and normalizes. Row `a` is the
probability measure proportional to `μ.withDensity (f a)`, and the zero measure when the density
has zero or infinite total mass. -/
noncomputable def ofDensity (μ : Measure β) (f : α → β → ℝ≥0∞) : Kernel α β :=
  ofFunOfCountable fun a ↦ (μ.withDensity (f a))[|Set.univ]

theorem ofDensity_apply (μ : Measure β) (f : α → β → ℝ≥0∞) (a : α) :
    ofDensity μ f a = (μ.withDensity (f a))[|Set.univ] := rfl

instance (μ : Measure β) (f : α → β → ℝ≥0∞) (a : α) :
    IsZeroOrProbabilityMeasure (ofDensity μ f a) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (μ.withDensity (f a))[|Set.univ])

instance (μ : Measure β) (f : α → β → ℝ≥0∞) : IsFiniteKernel (ofDensity μ f) :=
  ⟨⟨1, ENNReal.one_lt_top, fun a ↦ by rw [ofDensity_apply]; exact prob_le_one⟩⟩

/-- At the indicator of a measurable set the row is the base measure conditioned on the set. -/
theorem ofDensity_indicator_one_apply (μ : Measure β) (s : α → Set β) (a : α)
    (hs : MeasurableSet (s a)) : ofDensity μ (fun a ↦ (s a).indicator 1) a = μ[|s a] := by
  rw [ofDensity_apply, withDensity_indicator_one hs]
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.restrict_apply_univ]

/-- A row depends on its density only up to a positive finite scalar, which the normalization
absorbs. -/
theorem ofDensity_apply_eq_of_eq_mul (μ : Measure β) {f f' : α → β → ℝ≥0∞} {a : α} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ∞) (h : ∀ b, f' a b = c * f a b) :
    ofDensity μ f' a = ofDensity μ f a := by
  rw [ofDensity_apply, ofDensity_apply,
    show μ.withDensity (f' a) = c • μ.withDensity (f a) by
      rw [show f' a = fun b ↦ c * f a b from funext h]; exact withDensity_smul' c (f a) hc]
  ext s hs
  rw [cond_apply MeasurableSet.univ, cond_apply MeasurableSet.univ, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hc),
    mul_mul_mul_comm, ENNReal.inv_mul_cancel hc0 hc, one_mul]

/-- The kernel depends on the density only up to a positive finite scalar. -/
theorem ofDensity_const_mul (μ : Measure β) (f : α → β → ℝ≥0∞) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ∞) : ofDensity μ (fun a b ↦ c * f a b) = ofDensity μ f :=
  Kernel.ext fun _ ↦ ofDensity_apply_eq_of_eq_mul μ hc0 hc fun _ ↦ rfl

/-- Every finite measure on a countable discrete space is a row of the density kernel at a base
of positive mass everywhere, with the measure's density against the base as the density. -/
theorem ofDensity_div [Countable β] [MeasurableSingletonClass β] (μ : Measure β)
    [IsFiniteMeasure μ] (hμ : ∀ b, μ {b} ≠ 0) (ν : α → Measure β) (a : α) :
    ofDensity μ (fun a b ↦ ν a {b} / μ {b}) a = (ν a)[|Set.univ] := by
  rw [ofDensity_apply]
  congr 1
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [withDensity_apply _ (.singleton b), lintegral_singleton,
    ENNReal.div_mul_cancel (hμ b) (measure_ne_top μ _)]

theorem ofDensity_apply_singleton' [MeasurableSingletonClass β] (μ : Measure β)
    (f : α → β → ℝ≥0∞) (a : α) (b : β) :
    ofDensity μ f a {b} = f a b * μ {b} / ∫⁻ b', f a b' ∂μ := by
  rw [ofDensity_apply, cond_apply MeasurableSet.univ, Set.univ_inter,
    withDensity_apply _ (.singleton b), lintegral_singleton, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ENNReal.div_eq_inv_mul]

theorem ofDensity_apply_singleton [Fintype β] [MeasurableSingletonClass β] (μ : Measure β)
    (f : α → β → ℝ≥0∞) (a : α) (b : β) :
    ofDensity μ f a {b} = f a b * μ {b} / ∑ b', f a b' * μ {b'} := by
  rw [ofDensity_apply_singleton', lintegral_fintype]

/-- A relabelling of the target that carries one base and density to another carries the density
kernel along. -/
theorem ofDensity_apply_singleton_of_equiv {α' β' : Type*} [MeasurableSpace α']
    [MeasurableSpace β'] [Countable α'] [MeasurableSingletonClass α'] [Fintype β]
    [MeasurableSingletonClass β] [Fintype β'] [MeasurableSingletonClass β'] (e : β ≃ β')
    {μ : Measure β} {μ' : Measure β'} {f : α → β → ℝ≥0∞} {f' : α' → β' → ℝ≥0∞} {a : α} {a' : α'}
    (hμ : ∀ b, μ' {e b} = μ {b}) (hf : ∀ b, f' a' (e b) = f a b) (b : β) :
    ofDensity μ' f' a' {e b} = ofDensity μ f a {b} := by
  rw [ofDensity_apply_singleton, ofDensity_apply_singleton, hf, hμ, ← e.sum_comp]
  simp only [hf, hμ]

/-- A row whose density has positive finite mass under the base is a probability measure. -/
theorem isProbabilityMeasure_ofDensity (μ : Measure β) (f : α → β → ℝ≥0∞) (a : α)
    (h0 : ∫⁻ b, f a b ∂μ ≠ 0) (htop : ∫⁻ b, f a b ∂μ ≠ ∞) :
    IsProbabilityMeasure (ofDensity μ f a) := by
  rw [ofDensity_apply]
  refine cond_isProbabilityMeasure_of_finite ?_ ?_ <;>
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- Marginalizing a row over a product whose density depends on the first coordinate alone gives
the row on the marginal base, since the density carries no information about the second
coordinate. -/
theorem ofDensity_map_fst {γ : Type*} [MeasurableSpace γ] (μ : Measure (β × γ))
    (f : α → β → ℝ≥0∞) (hf : ∀ a, Measurable (f a)) (a : α) :
    (ofDensity μ (fun a p ↦ f a p.1) a).map Prod.fst = ofDensity (μ.map Prod.fst) f a := by
  have key : (μ.withDensity fun p ↦ f a p.1).map Prod.fst = (μ.map Prod.fst).withDensity (f a) :=
    Measure.map_withDensity_comp (hf a) measurable_fst
  have huniv : (μ.withDensity fun p ↦ f a p.1) Set.univ =
      (μ.map Prod.fst).withDensity (f a) Set.univ := by
    rw [← key, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  simp only [ofDensity_apply, ProbabilityTheory.cond, Measure.restrict_univ,
    Measure.map_smul _ measurable_fst.aemeasurable, key, huniv]

/-- On natural-number weights and densities the mass of an atom is its weighted density over the
total. -/
theorem ofDensity_natCast_real_singleton [Fintype β] [MeasurableSingletonClass β]
    (w : β → ℕ) (lik : α → β → ℕ) (a : α) (x : β) :
    (ofDensity (Measure.ofWeights (w ·)) (fun a x ↦ (lik a x : ℝ≥0∞)) a).real {x}
      = (lik a x * w x : ℝ) / ∑ x', (lik a x' * w x' : ℝ) := by
  rw [measureReal_def, ofDensity_apply_singleton, ENNReal.toReal_div,
    ENNReal.toReal_sum fun _ _ ↦ ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)]
  simp [ENNReal.toReal_mul]

/-- Against the uniform measure a density normalizes to its share of the row sum, since the base
cancels. -/
theorem ofDensity_uniformOn_apply_singleton [Fintype β] [MeasurableSingletonClass β] [Nonempty β]
    (f : α → β → ℝ≥0∞) (a : α) (b : β) :
    ofDensity (uniformOn Set.univ) f a {b} = f a b / ∑ b', f a b' := by
  rw [ofDensity_apply_singleton]
  have hc : ((Fintype.card β : ℝ≥0∞))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hc' : ((Fintype.card β : ℝ≥0∞))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero)
  simp_rw [uniformOn_univ_apply_singleton, ← Finset.sum_mul]
  exact ENNReal.mul_div_mul_right _ _ hc hc'

/-- With a real-valued density the share is the real ratio of the row. -/
theorem ofDensity_uniformOn_ofReal_apply_singleton [Fintype β] [MeasurableSingletonClass β]
    [Nonempty β] (f : α → β → ℝ) (a : α) (b : β) (hf : ∀ b', 0 ≤ f a b')
    (hpos : 0 < ∑ b', f a b') :
    ofDensity (uniformOn Set.univ) (fun a b ↦ ENNReal.ofReal (f a b)) a {b} =
      ENNReal.ofReal (f a b / ∑ b', f a b') := by
  rw [ofDensity_uniformOn_apply_singleton, ← ENNReal.ofReal_sum_of_nonneg fun b' _ ↦ hf b',
    ← ENNReal.ofReal_div_of_pos hpos]

/-- Against the counting measure the density kernel is the weight kernel. -/
theorem ofDensity_count [Fintype β] [MeasurableSingletonClass β] (w : α → β → ℝ≥0∞) :
    ofDensity Measure.count w = ofWeights w := by
  ext a : 1
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [ofDensity_apply_singleton, ofWeights_apply_singleton]
  simp

/-- Bayes' rule. With a kernel's likelihood of the observation as density against the prior, the
row at an observation of positive marginal is the posterior. -/
theorem ofDensity_apply_eq_posterior [Countable β] [MeasurableSingletonClass β]
    [StandardBorelSpace β] [Nonempty β] (κ : Kernel β α) [IsFiniteKernel κ] (μ : Measure β)
    [IsFiniteMeasure μ] {a : α} (ha : (κ ∘ₘ μ) {a} ≠ 0) :
    ofDensity μ (fun a b ↦ κ b {a}) a = (κ†μ) a := by
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [ofDensity_apply_singleton', posterior_apply_singleton κ μ ha,
    Measure.bind_apply (.singleton a) (Kernel.aemeasurable _), mul_comm]

end ProbabilityTheory.Kernel
