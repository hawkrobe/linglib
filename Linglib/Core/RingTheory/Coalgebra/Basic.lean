/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Counit collapse through a Sweedler representation

Applying `L ⊗ ε` or `ε ⊗ L` to a Sweedler representation of `a` recovers
`L a`, for any linear functional `L`. `[UPSTREAM]` candidates for
`Mathlib.RingTheory.Coalgebra.Basic`, beside `Coalgebra.sum_counit_smul`.
-/

namespace Coalgebra.Repr

variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C]
  [Coalgebra R C] {ι : Type*} {a : C}

/-- Applying `L ⊗ ε` to a Sweedler representation of `a` recovers `L a`. -/
theorem sum_apply_mul_counit (𝓡 : Repr R a ι) (L : C →ₗ[R] R) :
    ∑ i ∈ 𝓡.index, L (𝓡.left i) * counit (𝓡.right i) = L a := by
  simpa only [map_sum, LinearMap.mul'_apply, mul_one] using
    congrArg (LinearMap.mul' R R) (sum_map_tmul_counit_eq L a (repr := 𝓡))

/-- Applying `ε ⊗ L` to a Sweedler representation of `a` recovers `L a`. -/
theorem sum_counit_mul_apply (𝓡 : Repr R a ι) (L : C →ₗ[R] R) :
    ∑ i ∈ 𝓡.index, counit (𝓡.left i) * L (𝓡.right i) = L a := by
  simpa only [map_sum, LinearMap.mul'_apply, one_mul] using
    congrArg (LinearMap.mul' R R) (sum_counit_tmul_map_eq L a (repr := 𝓡))

end Coalgebra.Repr
