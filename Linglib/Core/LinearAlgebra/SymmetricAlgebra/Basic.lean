/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Generators of the symmetric algebra

`SymmetricAlgebra R M` is generated as an algebra by the image of `ι R M`, and the range of a
lift is the subalgebra its generators' images generate. [UPSTREAM] Both belong in
`Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean`.
-/

public section

namespace SymmetricAlgebra

variable {R M A : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [CommSemiring A] [Algebra R A] {f : M →ₗ[R] A}

@[simp]
theorem adjoin_range_ι : Algebra.adjoin R (Set.range (ι R M)) = ⊤ := by
  refine top_unique fun x hx => ?_; clear hx
  induction x using induction with
  | algebraMap => exact algebraMap_mem _ _
  | ι x => exact Algebra.subset_adjoin (Set.mem_range_self _)
  | mul x y hx hy => exact mul_mem hx hy
  | add x y hx hy => exact add_mem hx hy

@[simp]
theorem range_lift : (lift f).range = Algebra.adjoin R (Set.range f) := by
  simp_rw [← Algebra.map_top, ← adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, lift_ι_apply]

end SymmetricAlgebra
