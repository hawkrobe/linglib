/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Generators and products of generators of the symmetric algebra

`SymmetricAlgebra R M` is generated as an algebra by the image of `ι R M`, and the range of a
lift is the subalgebra its generators' images generate. `TensorAlgebra.symRingCon_le` identifies
the ring congruences containing `TensorAlgebra.symRingCon`, and
`TensorAlgebra.symRingCon_toAddCon_le_ker` says which additive maps out of the tensor algebra
descend to the symmetric algebra. `SymmetricAlgebra.ιMulti R M κ` multiplies `κ`-indexed
generators; its span is the `Fintype.card κ`-th power of the submodule `LinearMap.range (ι R M)`
(`SymmetricAlgebra.span_range_ιMulti`), as for `ExteriorAlgebra.ιMulti`. [UPSTREAM] All belong in
`Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean`.

## Implementation notes

The body of `TensorAlgebra.symRingCon` is not exposed, so `TensorAlgebra.symRingCon_le`, which
upstream is `RingCon.ringConGen_le` applied to that body, goes through `SymmetricAlgebra.lift`
into the quotient by the congruence. That quotient is shown commutative by the argument of
mathlib's `CommSemiring (SymmetricAlgebra R M)` instance.
-/

@[expose] public section

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace SymmetricAlgebra

variable {A : Type*} [CommSemiring A] [Algebra R A] {f : M →ₗ[R] A}

@[simp]
theorem adjoin_range_ι : Algebra.adjoin R (Set.range (ι R M)) = ⊤ := by
  refine top_unique fun x hx ↦ ?_; clear hx
  induction x using induction with
  | algebraMap => exact algebraMap_mem _ _
  | ι x => exact Algebra.subset_adjoin (Set.mem_range_self _)
  | mul x y hx hy => exact mul_mem hx hy
  | add x y hx hy => exact add_mem hx hy

@[simp]
theorem range_lift : (lift f).range = Algebra.adjoin R (Set.range f) := by
  simp_rw [← Algebra.map_top, ← adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, lift_ι_apply]

theorem algHom_ι (x : M) : algHom R M (TensorAlgebra.ι R x) = ι R M x :=
  rfl

end SymmetricAlgebra

namespace TensorAlgebra

/-- A ring congruence on the tensor algebra contains `symRingCon` exactly when it identifies
`ι R x * ι R y` with `ι R y * ι R x`. -/
theorem symRingCon_le {c : RingCon (TensorAlgebra R M)} :
    symRingCon R M ≤ c ↔ ∀ x y : M, c (ι R x * ι R y) (ι R y * ι R x) := by
  refine ⟨fun h x y ↦ h <| (RingCon.eq _).1 ?_, fun h ↦ ?_⟩
  · change SymmetricAlgebra.algHom R M _ = SymmetricAlgebra.algHom R M _
    rw [map_mul, map_mul, SymmetricAlgebra.algHom_ι, SymmetricAlgebra.algHom_ι, mul_comm]
  let : CommSemiring c.Quotient :=
    { (inferInstance : Semiring c.Quotient) with
      mul_comm a b := by
        obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := R) c a
        obtain ⟨b, rfl⟩ := RingCon.mkₐ_surjective (α := R) c b
        change Commute (RingCon.mkₐ R c a) (RingCon.mkₐ R c b)
        induction b using TensorAlgebra.induction with
        | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_right _ _
        | ι y =>
          induction a using TensorAlgebra.induction with
          | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_left _ _
          | ι x => simpa [commute_iff_eq, ← map_mul] using (RingCon.eq c).2 (h x y)
          | mul a₁ a₂ h₁ h₂ => rw [map_mul]; exact h₁.mul_left h₂
          | add a₁ a₂ h₁ h₂ => rw [map_add]; exact h₁.add_left h₂
        | mul b₁ b₂ h₁ h₂ => rw [map_mul]; exact h₁.mul_right h₂
        | add b₁ b₂ h₁ h₂ => rw [map_add]; exact h₁.add_right h₂ }
  have hφ : (SymmetricAlgebra.lift ((RingCon.mkₐ R c).toLinearMap ∘ₗ ι R)).comp
      (SymmetricAlgebra.algHom R M) = RingCon.mkₐ R c :=
    TensorAlgebra.hom_ext <| LinearMap.ext fun x ↦
      (SymmetricAlgebra.lift_ι_apply _ x : SymmetricAlgebra.lift _ (SymmetricAlgebra.ι R M x) = _)
  intro a b hab
  have hab' : SymmetricAlgebra.algHom R M a = SymmetricAlgebra.algHom R M b := (RingCon.eq _).2 hab
  refine (RingCon.eq c).1 ?_
  change RingCon.mkₐ R c a = RingCon.mkₐ R c b
  rw [← AlgHom.congr_fun hφ a, ← AlgHom.congr_fun hφ b, AlgHom.comp_apply, AlgHom.comp_apply, hab']

/-- An additive map out of the tensor algebra is constant on the classes of `symRingCon` exactly
when it cannot see the order of two adjacent generators in any two-sided context. -/
theorem symRingCon_toAddCon_le_ker {N : Type*} [AddZeroClass N] (f : TensorAlgebra R M →+ N) :
    (symRingCon R M).toAddCon ≤ AddCon.ker f ↔ ∀ (a b : TensorAlgebra R M) (x y : M),
      f (a * (ι R x * ι R y) * b) = f (a * (ι R y * ι R x) * b) := by
  refine ⟨fun h a b x y ↦ h <| (symRingCon R M).mul ((symRingCon R M).mul
    ((symRingCon R M).refl a) (symRingCon_le.1 le_rfl x y)) ((symRingCon R M).refl b), fun h ↦ ?_⟩
  let c : RingCon (TensorAlgebra R M) :=
    { r a b := ∀ x y, f (x * a * y) = f (x * b * y)
      iseqv := ⟨fun _ _ _ ↦ rfl, fun h x y ↦ (h x y).symm, fun h₁ h₂ x y ↦ (h₁ x y).trans (h₂ x y)⟩
      add' h₁ h₂ x y := by simp only [mul_add, add_mul, map_add, h₁ x y, h₂ x y]
      mul' {a b c d} h₁ h₂ x y :=
        calc f (x * (a * c) * y)
            _ = f (x * a * (c * y)) := by simp only [mul_assoc]
            _ = f (x * b * c * y) := by rw [h₁, mul_assoc (x * b)]
            _ = f (x * (b * d) * y) := by rw [h₂, mul_assoc x] }
  exact fun a b hab ↦ by simpa using (symRingCon_le (c := c)).2 (fun x y a b ↦ h a b x y) hab 1 1

end TensorAlgebra

namespace SymmetricAlgebra

variable (R M) (κ : Type*) [Fintype κ]

/-- The product of `κ`-indexed generators, `x ↦ ∏ i, ι R M (x i)`, as a multilinear map. It is
symmetric (`SymmetricAlgebra.ιMulti_perm`); the symmetric algebra sibling of
`ExteriorAlgebra.ιMulti` and `TensorAlgebra.tprod`. -/
def ιMulti : MultilinearMap R (fun _ : κ ↦ M) (SymmetricAlgebra R M) :=
  (MultilinearMap.mkPiAlgebra R κ (SymmetricAlgebra R M)).compLinearMap fun _ ↦ ι R M

variable {R M κ}

theorem ιMulti_apply (x : κ → M) : ιMulti R M κ x = ∏ i, ι R M (x i) :=
  rfl

theorem ιMulti_perm (x : κ → M) (σ : Equiv.Perm κ) :
    (ιMulti R M κ fun i ↦ x (σ i)) = ιMulti R M κ x :=
  Equiv.prod_comp σ fun i ↦ ι R M (x i)

theorem ιMulti_mul_ιMulti {κ' : Type*} [Fintype κ'] (x : κ → M) (y : κ' → M) :
    ιMulti R M κ x * ιMulti R M κ' y = ιMulti R M (κ ⊕ κ') (Sum.elim x y) := by
  simp [ιMulti_apply, Fintype.prod_sum_type]

theorem algHom_tprod {n : ℕ} (x : Fin n → M) :
    algHom R M (TensorAlgebra.tprod R M n x) = ιMulti R M (Fin n) x := by
  simp only [TensorAlgebra.tprod_apply, map_list_prod, List.map_ofFn, Function.comp_def, algHom_ι,
    List.prod_ofFn, ιMulti_apply]

variable (R M κ)

theorem ιMulti_range :
    Set.range (ιMulti R M κ) ⊆ ↑(LinearMap.range (ι R M) ^ Fintype.card κ) := by
  rintro _ ⟨x, rfl⟩
  refine Submodule.pow_subset_pow _ (Set.mem_pow.2 ⟨fun j ↦
    ⟨ι R M (x ((Fintype.equivFin κ).symm j)), LinearMap.mem_range_self _ _⟩, ?_⟩)
  rw [List.prod_ofFn, ιMulti_apply]
  exact (Fintype.prod_equiv (Fintype.equivFin κ) _ _ fun _ ↦ by simp).symm

/-- The products of `Fintype.card κ` generators span the corresponding power of the submodule
`LinearMap.range (ι R M)`; the sibling of `ExteriorAlgebra.ιMulti_span_fixedDegree`. -/
theorem span_range_ιMulti :
    Submodule.span R (Set.range (ιMulti R M κ)) = LinearMap.range (ι R M) ^ Fintype.card κ := by
  refine le_antisymm (Submodule.span_le.2 (ιMulti_range R M κ)) ?_
  rw [Submodule.pow_eq_span_pow_set, Submodule.span_le]
  intro u hu
  obtain ⟨f, rfl⟩ := Set.mem_pow.1 hu
  choose v hv using fun j ↦ (f j).2
  refine Submodule.subset_span ⟨fun i ↦ v (Fintype.equivFin κ i), ?_⟩
  rw [List.prod_ofFn, ιMulti_apply]
  exact Fintype.prod_equiv (Fintype.equivFin κ) _ _ fun _ ↦ hv _

end SymmetricAlgebra
