/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ConditionalProbability

/-!
# Measures on a product at atoms

The marginals `Measure.fst` and `Measure.snd` at a singleton, as sums over the other
coordinate when it ranges over a finite type, in `ℝ≥0∞` and on reals; the product measure at
a rectangle on reals; absolute continuity of a joint with respect to the product of its
marginals; and a product measure, conditioned on an event of the first coordinate, at a set
given by its fibers over a finite second coordinate. `[UPSTREAM]` candidate for
`Mathlib/MeasureTheory/Measure/Prod.lean`.
-/

open ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem measureReal_prod_prod (μ : Measure α) (ν : Measure β) [SFinite ν] (s : Set α)
    (t : Set β) : (μ.prod ν).real (s ×ˢ t) = μ.real s * ν.real t := by
  simp [measureReal_def, prod_prod]

theorem prod_real_singleton (μ : Measure α) (ν : Measure β) [SFinite ν] (a : α) (b : β) :
    (μ.prod ν).real {(a, b)} = μ.real {a} * ν.real {b} := by
  rw [← Set.singleton_prod_singleton, measureReal_prod_prod]

variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

theorem fst_apply_singleton [Fintype β] (ρ : Measure (α × β)) (a : α) :
    ρ.fst {a} = ∑ b, ρ {(a, b)} := by
  rw [fst_apply (.singleton a),
    show Prod.fst ⁻¹' ({a} : Set α) = ↑(({a} : Finset α) ×ˢ (Finset.univ : Finset β)) from by
      ext ⟨_, _⟩; simp [eq_comm],
    ← sum_measure_singleton, Finset.sum_product, Finset.sum_singleton]

theorem snd_apply_singleton [Fintype α] (ρ : Measure (α × β)) (b : β) :
    ρ.snd {b} = ∑ a, ρ {(a, b)} := by
  rw [snd_apply (.singleton b),
    show Prod.snd ⁻¹' ({b} : Set β) = ↑((Finset.univ : Finset α) ×ˢ ({b} : Finset β)) from by
      ext ⟨_, _⟩; simp [eq_comm],
    ← sum_measure_singleton, Finset.sum_product]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_singleton _ _

/-- The first marginal at a singleton is the mass of the corresponding product event. -/
theorem fst_real_singleton [Fintype β] (ρ : Measure (α × β)) (a : α) :
    ρ.fst.real {a} = ρ.real ↑(({a} : Finset α) ×ˢ (Finset.univ : Finset β)) := by
  rw [measureReal_def, measureReal_def, fst_apply_singleton, ← sum_measure_singleton,
    Finset.sum_product, Finset.sum_singleton]

/-- The second marginal at a singleton is the mass of the corresponding product event. -/
theorem snd_real_singleton [Fintype α] (ρ : Measure (α × β)) (b : β) :
    ρ.snd.real {b} = ρ.real ↑((Finset.univ : Finset α) ×ˢ ({b} : Finset β)) := by
  rw [measureReal_def, measureReal_def, snd_apply_singleton, ← sum_measure_singleton,
    Finset.sum_product]
  exact congrArg _ (Finset.sum_congr rfl fun _ _ => (Finset.sum_singleton _ _).symm)

theorem fst_real_singleton_eq_sum [Fintype β] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (a : α) : ρ.fst.real {a} = ∑ b, ρ.real {(a, b)} := by
  simp [measureReal_def, fst_apply_singleton, ENNReal.toReal_sum, measure_ne_top]

theorem snd_real_singleton_eq_sum [Fintype α] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (b : β) : ρ.snd.real {b} = ∑ a, ρ.real {(a, b)} := by
  simp [measureReal_def, snd_apply_singleton, ENNReal.toReal_sum, measure_ne_top]

/-- A joint on a countable product is absolutely continuous with respect to the product of
its marginals. -/
theorem absolutelyContinuous_fst_prod_snd [Countable α] [Countable β] (ρ : Measure (α × β))
    [SFinite ρ] : ρ ≪ ρ.fst.prod ρ.snd := by
  refine absolutelyContinuous_of_forall_singleton fun ⟨a, b⟩ h => ?_
  rw [← Set.singleton_prod_singleton, prod_prod, mul_eq_zero, fst_apply (.singleton a),
    snd_apply (.singleton b)] at h
  exact h.elim (measure_mono_null (Set.singleton_subset_iff.mpr rfl))
    (measure_mono_null (Set.singleton_subset_iff.mpr rfl))

/-! ### Sets given by their fibers over a finite coordinate -/

section Fibers

omit [MeasurableSingletonClass α]

variable [Fintype β] (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν] {f : β → Set α}

/-- The product measure at a set given by its fibers over a finite second coordinate. -/
theorem prod_apply_fibers (hf : ∀ b, MeasurableSet (f b)) :
    (μ.prod ν) {p | p.1 ∈ f p.2} = ∑ b, μ (f b) * ν {b} := by
  have hm : MeasurableSet {p : α × β | p.1 ∈ f p.2} := by
    rw [show {p : α × β | p.1 ∈ f p.2} = ⋃ b, f b ×ˢ {b} from by ext ⟨a, b⟩; simp]
    exact .iUnion λ b => (hf b).prod (.singleton b)
  rw [prod_apply_symm hm, lintegral_fintype]
  rfl

/-- Conditioning a product on an event of the first coordinate, at a set given by its fibers
over a finite second coordinate: the fibers' conditional masses, mixed by the second factor. -/
theorem cond_prod_fst_apply_fibers [IsProbabilityMeasure ν] {s : Set α} (hs : MeasurableSet s)
    (hf : ∀ b, MeasurableSet (f b)) :
    (μ.prod ν)[|Prod.fst ⁻¹' s] {p | p.1 ∈ f p.2} = ∑ b, μ[|s] (f b) * ν {b} := by
  rw [cond_apply (measurable_fst hs), ← Set.prod_univ, prod_prod, measure_univ, mul_one,
    show s ×ˢ Set.univ ∩ {p : α × β | p.1 ∈ f p.2} = {p | p.1 ∈ s ∩ f p.2} from by
      ext ⟨a, b⟩; simp,
    prod_apply_fibers μ ν (λ b => hs.inter (hf b)), Finset.mul_sum]
  simp only [cond_apply hs, mul_assoc]

/-- `cond_prod_fst_apply_fibers` on reals. -/
theorem cond_prod_fst_real_fibers [IsProbabilityMeasure ν] {s : Set α} (hs : MeasurableSet s)
    (hf : ∀ b, MeasurableSet (f b)) :
    ((μ.prod ν)[|Prod.fst ⁻¹' s]).real {p | p.1 ∈ f p.2} =
      ∑ b, (μ[|s]).real (f b) * ν.real {b} := by
  rw [measureReal_def, cond_prod_fst_apply_fibers μ ν hs hf,
    ENNReal.toReal_sum λ b _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top ν _)]
  simp only [ENNReal.toReal_mul, measureReal_def]

end Fibers

end MeasureTheory.Measure
