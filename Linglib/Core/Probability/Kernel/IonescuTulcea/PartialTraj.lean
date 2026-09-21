/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Partial trajectories at the next time

Evaluating a partial trajectory from time `a` at time `a + 1` recovers the step kernel `κ a`,
however far the trajectory runs, and the one-step trajectory from `x` is the step kernel at `x`
pushed forward by appending its value to `x`. `[UPSTREAM]` candidate for
`Mathlib/Probability/Kernel/IonescuTulcea/PartialTraj.lean`.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory Preorder

namespace ProbabilityTheory.Kernel

variable {X : ℕ → Type*} {mX : ∀ n, MeasurableSpace (X n)}
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]

/-- The pushforward of `partialTraj κ a b` along the point at time `a + 1` is `κ a`. -/
theorem map_partialTraj_eval_succ {a b : ℕ} (hab : a + 1 ≤ b) :
    (partialTraj κ a b).map (fun x ↦ x ⟨a + 1, mem_Iic.2 hab⟩) = κ a := by
  rw [show (fun x : Π i : Iic b, X i ↦ x ⟨a + 1, mem_Iic.2 hab⟩)
      = (fun x : Π i : Iic (a + 1), X i ↦ x ⟨a + 1, mem_Iic.2 le_rfl⟩) ∘ frestrictLe₂ hab from rfl,
    map_comp_right _ (by fun_prop) (by fun_prop), partialTraj_map_frestrictLe₂ _ hab,
    map_partialTraj_succ_self]

/-- The one-step trajectory from `x` is `κ a x` pushed forward by appending its value to `x`. -/
theorem partialTraj_succ_self_apply (a : ℕ) (x : Π i : Iic a, X i) :
    partialTraj κ a (a + 1) x
      = (κ a x).map fun y ↦ IicProdIoc a (a + 1) (x, MeasurableEquiv.piSingleton a y) := by
  rw [partialTraj_succ_self, map_apply _ (by fun_prop), prod_apply, id_apply,
    map_apply _ (by fun_prop), Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end ProbabilityTheory.Kernel
