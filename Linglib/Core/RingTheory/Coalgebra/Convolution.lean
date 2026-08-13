/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.Algebra.Ring.Commute

/-!
# Commutator bracket through a Sweedler representation

Evaluation of the ring commutator `⁅f, g⁆` of the convolution algebra
`WithConv (C →ₗ[R] A)` through a Sweedler representation. `[UPSTREAM]`
candidate for `Mathlib.RingTheory.Coalgebra.Convolution`, beside
`Coalgebra.Repr.convMul_apply`.
-/

namespace Coalgebra.Repr

open WithConv

variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C]
  [Coalgebra R C] {ι : Type*} {a : C}

/-- The ring commutator bracket on the convolution algebra, evaluated through a
Sweedler representation. -/
theorem lie_apply {A : Type*} [Ring A] [Algebra R A] (𝓡 : Repr R a ι)
    (f g : WithConv (C →ₗ[R] A)) :
    ⁅f, g⁆ a =
      ∑ i ∈ 𝓡.index, (f (𝓡.left i) * g (𝓡.right i) - g (𝓡.left i) * f (𝓡.right i)) := by
  rw [Ring.lie_def]
  show (f * g) a - (g * f) a = _
  rw [𝓡.convMul_apply, 𝓡.convMul_apply, Finset.sum_sub_distrib]

end Coalgebra.Repr
