/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Marginals of a joint pushed through a parallel composition

Pushing a product measure through `η ∥ₖ η'` pushes each factor through its kernel. Pushing a
joint measure on `α × β` through `Kernel.id ∥ₖ η` keeps the first marginal and composes the
second with `η`. The joint is
disintegrated as `ρ.fst ⊗ₘ ρ.condKernel`. `[UPSTREAM]` candidate for
`Mathlib/Probability/Kernel/Composition/Lemmas.lean`.
-/

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

end MeasureTheory.Measure
