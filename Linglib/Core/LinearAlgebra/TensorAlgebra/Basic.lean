/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# Products of `TensorAlgebra.tprod`

`TensorAlgebra.tprod_mul_tprod` multiplies two products of generators by appending their factors,
and `TensorAlgebra.span_tprod_eq_top` says these products span the tensor algebra, with the
linear induction principle `TensorAlgebra.induction_tprod`. They are the tensor algebra siblings
of `ExteriorAlgebra.ιMulti_mul_ιMulti` and `ExteriorAlgebra.ιMulti_span`. [UPSTREAM] All belong
in `Mathlib/LinearAlgebra/TensorAlgebra/Basic.lean`.
-/

@[expose] public section

namespace TensorAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem tprod_mul_tprod {m n : ℕ} (a : Fin m → M) (b : Fin n → M) :
    tprod R M m a * tprod R M n b = tprod R M (m + n) (Fin.append a b) := by
  simp only [tprod_apply, ← List.prod_append, ← List.ofFn_fin_append]
  congr 2
  ext i
  cases i using Fin.addCases <;> simp

variable (R M) in
/-- The products `tprod R M n x` of generators span the tensor algebra. -/
theorem span_tprod_eq_top : Submodule.span R (⋃ n, Set.range (tprod R M n)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun a ↦ ?_
  induction a using TensorAlgebra.induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ r (Submodule.subset_span (Set.mem_iUnion.2 ⟨0, ![], ?_⟩))
    simp [tprod_apply]
  | ι x => exact Submodule.subset_span (Set.mem_iUnion.2 ⟨1, ![x], by simp [tprod_apply]⟩)
  | mul a b ha hb =>
    have := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨_, ⟨m, rfl⟩, x, rfl⟩, _, ⟨_, ⟨n, rfl⟩, y, rfl⟩, rfl⟩
    exact Set.mem_iUnion.2 ⟨m + n, _, (tprod_mul_tprod x y).symm⟩
  | add a b ha hb => exact add_mem ha hb

@[elab_as_elim]
theorem induction_tprod {motive : TensorAlgebra R M → Prop}
    (tprod : ∀ (n : ℕ) (x : Fin n → M), motive (tprod R M n x))
    (smul : ∀ (r : R) (a : TensorAlgebra R M), motive a → motive (r • a))
    (add : ∀ a b, motive a → motive b → motive (a + b)) (a : TensorAlgebra R M) : motive a := by
  induction (span_tprod_eq_top R M ▸ Submodule.mem_top : a ∈ _) using Submodule.span_induction with
  | mem _ h => obtain ⟨n, x, rfl⟩ := Set.mem_iUnion.1 h; exact tprod n x
  | zero => simpa using smul 0 _ (tprod 0 ![])
  | add _ _ _ _ ha hb => exact add _ _ ha hb
  | smul r _ _ ha => exact smul r _ ha

end TensorAlgebra
