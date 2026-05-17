/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.RingTheory.Coalgebra.Convolution

set_option autoImplicit false

/-!
# `R`-algebra structure on the convolution semiring `WithConv (C →ₗ[R] A)`

Mathlib's `Mathlib.RingTheory.Coalgebra.Convolution` provides the
convolution `Semiring` / `CommSemiring` / `Ring` / `CommRing` structures
on `WithConv (C →ₗ[R] A)` (for `C` a coalgebra and `A` an algebra, with
appropriate hypotheses). It does *not* provide an `Algebra R` instance,
even though one exists naturally: scalars act on linear maps in a way
that commutes with convolution (because both the convolution and the
scalar action factor through `mul'` on `A`, which is `R`-linear).

This file supplies the missing `Algebra R (WithConv (C →ₗ[R] A))`
instance via `Algebra.ofModule`. The two compatibility hypotheses
reduce to `TensorProduct.map_smul_left` / `map_smul_right` plus the
`R`-linearity of `mul' R A` and `comul`.

## `[UPSTREAM]` candidate

Natural home is `Mathlib/RingTheory/Coalgebra/Convolution.lean`,
immediately after `convSemiring`.
-/

namespace LinearMap

open Coalgebra TensorProduct WithConv

variable {R C A : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- Convolution `R`-algebra structure on `WithConv (C →ₗ[R] A)`. -/
noncomputable instance convAlgebra : Algebra R (WithConv (C →ₗ[R] A)) :=
  Algebra.ofModule
    (fun r x y => by
      apply WithConv.ofConv_injective
      simp only [convMul_def, WithConv.ofConv_toConv, WithConv.ofConv_smul,
                 TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul])
    (fun r x y => by
      apply WithConv.ofConv_injective
      simp only [convMul_def, WithConv.ofConv_toConv, WithConv.ofConv_smul,
                 TensorProduct.map_smul_right, LinearMap.smul_comp, LinearMap.comp_smul])

@[simp]
lemma convAlgebraMap_apply (r : R) (c : C) :
    (algebraMap R (WithConv (C →ₗ[R] A)) r : WithConv (C →ₗ[R] A)) c =
      r • algebraMap R A (counit (R := R) c) := by
  -- algebraMap r = r • 1; (1 : WithConv) = toConv (Algebra.linearMap R A ∘ₗ counit).
  rw [Algebra.algebraMap_eq_smul_one, convOne_def]
  -- Goal: (r • toConv (Algebra.linearMap R A ∘ₗ counit)) c = r • algebraMap R A (counit c)
  show (r • (toConv (Algebra.linearMap R A ∘ₗ counit (R := R)))).ofConv c = _
  simp [WithConv.ofConv_smul, Algebra.linearMap]

end LinearMap
