/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Marginals of a joint pushed through a parallel composition

Pushing a product measure through `η ∥ₖ η'` pushes each factor through its kernel. Pushing a
joint measure on `α × β` through `Kernel.id ∥ₖ η` keeps the first marginal and composes the
second with `η`. The joint is disintegrated as `ρ.fst ⊗ₘ ρ.condKernel`. On finite types, a
composition-product and a joint pushed through `Kernel.id ∥ₖ η` are computed at atoms.
`[UPSTREAM]` candidate for `Mathlib/Probability/Kernel/Composition/Lemmas.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

/-- Pushing a product measure through a parallel composition pushes each factor through its
kernel: Fubini for the Giry monad. -/
theorem parallelComp_comp_prod (η : Kernel α γ) [IsSFiniteKernel η] (η' : Kernel β δ)
    [IsSFiniteKernel η'] (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν] :
    (η ∥ₖ η') ∘ₘ (μ.prod ν) = (η ∘ₘ μ).prod (η' ∘ₘ ν) := by
  calc (η ∥ₖ η') ∘ₘ (μ.prod ν)
      = ((η ∥ₖ η') ∘ₖ (Kernel.const Unit μ ×ₖ Kernel.const Unit ν)) () := by
        rw [Kernel.comp_apply, Kernel.prod_apply, Kernel.const_apply, Kernel.const_apply]
    _ = (η ∘ₘ μ).prod (η' ∘ₘ ν) := by
        rw [Kernel.parallelComp_comp_prod, Kernel.prod_apply, Kernel.comp_apply,
          Kernel.comp_apply, Kernel.const_apply, Kernel.const_apply]

section Marginals

variable (η : Kernel β γ) [IsMarkovKernel η]

theorem parallelComp_id_comp_prod (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν] :
    (Kernel.id ∥ₖ η) ∘ₘ (μ.prod ν) = μ.prod (η ∘ₘ ν) := by
  rw [parallelComp_comp_prod, id_comp]

variable [StandardBorelSpace β] [Nonempty β] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]

theorem fst_parallelComp_id_comp : ((Kernel.id ∥ₖ η) ∘ₘ ρ).fst = ρ.fst := by
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [parallelComp_comp_compProd, fst_compProd]

theorem snd_parallelComp_id_comp : ((Kernel.id ∥ₖ η) ∘ₘ ρ).snd = η ∘ₘ ρ.snd := by
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [parallelComp_comp_compProd, snd_compProd, ← comp_assoc, ← snd_compProd ρ.fst ρ.condKernel,
    ρ.disintegrate ρ.condKernel]

end Marginals

/-! ### Atoms -/

section Atoms

variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- A composition-product at an atom. -/
theorem compProd_apply_singleton (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsSFiniteKernel κ] (a : α) (b : β) : (μ ⊗ₘ κ) {(a, b)} = μ {a} * κ a {b} := by
  rw [compProd_apply (.singleton _)]
  have h : (λ a' => κ a' (Prod.mk a' ⁻¹' {(a, b)})) = ({a} : Set α).indicator λ _ => κ a {b} := by
    ext a'
    by_cases ha : a' = a
    · subst ha
      simp [Set.preimage]
    · simp [Set.preimage, ha]
  rw [h, lintegral_indicator (.singleton a), setLIntegral_const, mul_comm]

theorem compProd_real_singleton (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β)
    [IsFiniteKernel κ] (a : α) (b : β) : (μ ⊗ₘ κ).real {(a, b)} = μ.real {a} * (κ a).real {b} := by
  simp [measureReal_def, compProd_apply_singleton]

variable [Fintype α] [Fintype β] [MeasurableSingletonClass γ]

/-- A joint pushed through `Kernel.id ∥ₖ η`, at an atom: the second coordinate is summed out
through the kernel. -/
theorem parallelComp_id_comp_apply_singleton (ρ : Measure (α × β)) (η : Kernel β γ)
    [IsSFiniteKernel η] (a : α) (c : γ) :
    (((Kernel.id : Kernel α α) ∥ₖ η) ∘ₘ ρ) {(a, c)} = ∑ b, ρ {(a, b)} * η b {c} := by
  classical
  rw [comp_eq_sum_of_countable, sum_apply _ (.singleton _), tsum_fintype, Fintype.sum_prod_type]
  simp only [smul_apply, Kernel.parallelComp_apply, Kernel.id_apply, ← Set.singleton_prod_singleton,
    prod_prod, dirac_apply' _ (.singleton _), smul_eq_mul, Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

theorem parallelComp_id_comp_real_singleton (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (η : Kernel β γ) [IsFiniteKernel η] (a : α) (c : γ) :
    (((Kernel.id : Kernel α α) ∥ₖ η) ∘ₘ ρ).real {(a, c)}
      = ∑ b, ρ.real {(a, b)} * (η b).real {c} := by
  rw [measureReal_def, parallelComp_id_comp_apply_singleton,
    ENNReal.toReal_sum λ b _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  simp only [ENNReal.toReal_mul, measureReal_def]

end Atoms

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- A composition of kernels at an atom, over a finite middle type. -/
theorem comp_apply_singleton [Fintype β] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] (η : Kernel β γ) (κ : Kernel α β) (a : α) (c : γ) :
    (η ∘ₖ κ) a {c} = ∑ b, κ a {b} * η b {c} := by
  rw [comp_apply' _ _ _ (.singleton c), lintegral_fintype]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

end ProbabilityTheory.Kernel
