/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Sweedler representation of a product

In a bialgebra, `comul (x * y) = comul x * comul y`, so Sweedler
representations of `x` and `y` multiply to one of `x * y`. `[UPSTREAM]`
candidate for `Mathlib.RingTheory.Bialgebra.Basic`, beside
`Bialgebra.comul_mul`.
-/

namespace Coalgebra.Repr

variable {R : Type*} [CommSemiring R]

/-- Sweedler representation of a product `x * y` in a bialgebra, indexed by
pairs: `left (i, j) = left i * left j` and `right (i, j) = right i * right j`. -/
@[simps]
noncomputable def mul {H : Type*} [Semiring H] [Bialgebra R H] {x y : H}
    {ιx ιy : Type*} (𝓡x : Repr R x ιx) (𝓡y : Repr R y ιy) :
    Repr R (x * y) (ιx × ιy) where
  index := 𝓡x.index ×ˢ 𝓡y.index
  left p := 𝓡x.left p.1 * 𝓡y.left p.2
  right p := 𝓡x.right p.1 * 𝓡y.right p.2
  eq := by
    rw [Bialgebra.comul_mul, ← 𝓡x.eq, ← 𝓡y.eq, Finset.sum_product, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

end Coalgebra.Repr
