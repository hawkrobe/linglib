/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Marginals of a joint pushed through a parallel composition

Pushing a joint measure on `α × β` through `Kernel.id ∥ₖ η` keeps the first marginal and
composes the second with `η`; on a product measure it acts factorwise. The joint is
disintegrated as `ρ.fst ⊗ₘ ρ.condKernel`. `[UPSTREAM]` candidate for
`Mathlib/Probability/Kernel/Composition/Lemmas.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (η : Kernel β γ) [IsMarkovKernel η]

theorem parallelComp_id_comp_prod (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν] :
    (Kernel.id ∥ₖ η) ∘ₘ (μ.prod ν) = μ.prod (η ∘ₘ ν) := by
  rw [← compProd_const, ← compProd_const, parallelComp_comp_compProd, Kernel.comp_const]

variable [StandardBorelSpace β] [Nonempty β] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]

theorem fst_parallelComp_id_comp : ((Kernel.id ∥ₖ η) ∘ₘ ρ).fst = ρ.fst := by
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [parallelComp_comp_compProd, fst_compProd]

theorem snd_parallelComp_id_comp : ((Kernel.id ∥ₖ η) ∘ₘ ρ).snd = η ∘ₘ ρ.snd := by
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [parallelComp_comp_compProd, snd_compProd, ← comp_assoc, ← snd_compProd ρ.fst ρ.condKernel,
    ρ.disintegrate ρ.condKernel]

end MeasureTheory.Measure
