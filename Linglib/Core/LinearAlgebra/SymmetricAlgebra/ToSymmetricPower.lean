/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Fin.Tuple.Basic
public import Linglib.Core.LinearAlgebra.SymmetricAlgebra.Basic
public import Linglib.Core.LinearAlgebra.TensorAlgebra.Basic
public import Linglib.Core.LinearAlgebra.TensorPower.Symmetric
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
# The symmetric algebra as a direct sum of symmetric powers

`SymmetricPower.toSymmetricAlgebra : Sym[R] κ M →ₗ[R] SymmetricAlgebra R M` sends `⨂ₛ[R] i, x i` to
`∏ i, ι R M (x i)`. It is the symmetric sibling of `TensorPower.toTensorAlgebra`, and its range is
the `Fintype.card κ`-th power of the submodule `LinearMap.range (ι R M)`. The decomposition
`TensorAlgebra.toDirectSum` descends to the symmetric algebra, so that
`SymmetricAlgebra R M ≃ₗ[R] ⨁ n, Sym[R]^n M` as for the tensor algebra, and
`toSymmetricAlgebra` is injective on `Sym[R]^n M`. Together these identify the quotient
`Sym[R]^n M` of the tensor power with the `n`-th power of the generating submodule of the symmetric
algebra, the degree-`n` part of its grading. [UPSTREAM] Natural home
`Mathlib/LinearAlgebra/SymmetricAlgebra/ToSymmetricPower.lean`, beside
`Mathlib/LinearAlgebra/TensorAlgebra/ToTensorPower.lean`.

## Main definitions

* `SymmetricPower.toSymmetricAlgebra`: the map `Sym[R] κ M →ₗ[R] SymmetricAlgebra R M`.
* `SymmetricAlgebra.toDirectSum`, `SymmetricAlgebra.ofDirectSum`: the maps between
  `SymmetricAlgebra R M` and `⨁ n, Sym[R]^n M`.
* `SymmetricAlgebra.equivDirectSum`: the linear equivalence they form.

## Main statements

* `SymmetricPower.range_toSymmetricAlgebra`
* `SymmetricAlgebra.toDirectSum_comp_toSymmetricAlgebra`
* `SymmetricPower.toSymmetricAlgebra_injective`

## Implementation notes

`SymmetricAlgebra.toDirectSum` is `TensorAlgebra.toDirectSum` followed by the quotient maps
`⨂[R]^n M → Sym[R]^n M`, descended along `TensorAlgebra.symRingCon_toAddCon_le_ker`: swapping two
adjacent generators of a product of generators permutes the factors of one pure tensor. The
statements about `Sym[R]^n M` take `R : Type` because mathlib's `SymmetricPower R ι M` puts `R`
and `ι` in one universe.

## TODO

* Upgrade `SymmetricAlgebra.equivDirectSum` to an algebra isomorphism once `n ↦ Sym[R]^n M`
  carries its graded commutative multiplication, a TODO of
  `Mathlib/LinearAlgebra/TensorPower/Symmetric.lean`.
-/

@[expose] public section

open scoped TensorProduct DirectSum

namespace SymmetricPower

section Fintype

universe u
variable {R κ : Type u} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype κ]

/-- The linear map `Sym[R] κ M →ₗ[R] SymmetricAlgebra R M` sending `⨂ₛ[R] i, x i` to
`∏ i, ι R M (x i)`. -/
def toSymmetricAlgebra : Sym[R] κ M →ₗ[R] SymmetricAlgebra R M :=
  lift (SymmetricAlgebra.ιMulti R M κ) SymmetricAlgebra.ιMulti_perm

@[simp]
theorem toSymmetricAlgebra_tprod (x : κ → M) :
    toSymmetricAlgebra (tprod R x) = SymmetricAlgebra.ιMulti R M κ x :=
  lift_tprod x

variable (R M κ) in
theorem range_toSymmetricAlgebra :
    LinearMap.range (toSymmetricAlgebra (R := R) (M := M) (κ := κ)) =
      LinearMap.range (SymmetricAlgebra.ι R M) ^ Fintype.card κ := by
  rw [LinearMap.range_eq_map, ← span_tprod_eq_top, Submodule.map_span, ← Set.range_comp,
    ← SymmetricAlgebra.span_range_ιMulti]
  congr 2
  ext x
  simp

end Fintype

variable {R : Type} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem toSymmetricAlgebra_comp_mk (n : ℕ) :
    toSymmetricAlgebra ∘ₗ mk R (Fin n) M =
      (SymmetricAlgebra.algHom R M).toLinearMap ∘ₗ TensorPower.toTensorAlgebra := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, mk_tprod,
    toSymmetricAlgebra_tprod, AlgHom.toLinearMap_apply, TensorPower.toTensorAlgebra_tprod,
    SymmetricAlgebra.algHom_tprod]

private theorem lmap_mk_toDirectSum_tprod (n : ℕ) (x : Fin n → M) :
    DirectSum.lmap (fun n ↦ mk R (Fin n) M)
      (TensorAlgebra.toDirectSum (TensorAlgebra.tprod R M n x)) = DirectSum.of _ n (tprod R x) := by
  simp [TensorAlgebra.toDirectSum_tensorPower_tprod, -TensorAlgebra.tprod_apply]

/-- Decomposing the tensor algebra into symmetric powers forgets the order of two adjacent
generators, in any two-sided context. -/
theorem lmap_mk_toDirectSum_mul_ι_mul_ι_mul (a b : TensorAlgebra R M) (x y : M) :
    DirectSum.lmap (fun n ↦ mk R (Fin n) M)
        (TensorAlgebra.toDirectSum (a * (TensorAlgebra.ι R x * TensorAlgebra.ι R y) * b)) =
      DirectSum.lmap (fun n ↦ mk R (Fin n) M)
        (TensorAlgebra.toDirectSum (a * (TensorAlgebra.ι R y * TensorAlgebra.ι R x) * b)) := by
  have hι (u v : M) :
      TensorAlgebra.ι R u * TensorAlgebra.ι R v = TensorAlgebra.tprod R M 2 ![u, v] := by
    simp [TensorAlgebra.tprod_apply]
  induction a using TensorAlgebra.induction_tprod with
  | smul r a h => simp only [smul_mul_assoc, map_smul, h]
  | add a₁ a₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]
  | tprod p f =>
  induction b using TensorAlgebra.induction_tprod with
  | smul r b h => simp only [mul_smul_comm, map_smul, h]
  | add b₁ b₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
  | tprod q g =>
  have hswap : Fin.append (Fin.append f ![y, x]) g =
      Fin.append (Fin.append f ![x, y]) g ∘ Fin.permAdd (Fin.permAdd 1 (Equiv.swap 0 1)) 1 := by
    rw [Fin.append_comp_permAdd, Fin.append_comp_permAdd]
    congr 2
    ext i
    fin_cases i <;> rfl
  simp only [hι, TensorAlgebra.tprod_mul_tprod, lmap_mk_toDirectSum_tprod, hswap]
  exact congrArg _ (tprod_equiv _ _).symm

end SymmetricPower

namespace SymmetricAlgebra

open SymmetricPower

variable {R : Type} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The decomposition of `SymmetricAlgebra R M` into the symmetric powers of `M`: the descent of
`TensorAlgebra.toDirectSum` followed by the quotient maps `⨂[R]^n M → Sym[R]^n M`. -/
noncomputable def toDirectSum : SymmetricAlgebra R M →ₗ[R] ⨁ n, Sym[R]^n M :=
  let g := DirectSum.lmap (fun n ↦ mk R (Fin n) M) ∘ₗ TensorAlgebra.toDirectSum.toLinearMap
  { toFun := AddCon.lift _ g.toAddMonoidHom <|
      (TensorAlgebra.symRingCon_toAddCon_le_ker _).2 lmap_mk_toDirectSum_mul_ι_mul_ι_mul
    map_add' := map_add _
    map_smul' r x := by
      obtain ⟨a, rfl⟩ := algHom_surjective R M x
      exact map_smul g r a }

theorem toDirectSum_algHom (a : TensorAlgebra R M) :
    toDirectSum (algHom R M a) =
      DirectSum.lmap (fun n ↦ mk R (Fin n) M) (TensorAlgebra.toDirectSum a) :=
  rfl

@[simp]
theorem toDirectSum_ιMulti {n : ℕ} (x : Fin n → M) :
    toDirectSum (ιMulti R M (Fin n) x) = DirectSum.of _ n (tprod R x) := by
  rw [← algHom_tprod, toDirectSum_algHom, lmap_mk_toDirectSum_tprod]

theorem toDirectSum_comp_toSymmetricAlgebra (n : ℕ) :
    toDirectSum ∘ₗ toSymmetricAlgebra = DirectSum.lof R ℕ (fun n ↦ Sym[R]^n M) n :=
  SymmetricPower.ext <| MultilinearMap.ext fun x ↦ by simp [DirectSum.lof_eq_of]

/-- The sum of the maps `SymmetricPower.toSymmetricAlgebra`. -/
noncomputable def ofDirectSum : (⨁ n, Sym[R]^n M) →ₗ[R] SymmetricAlgebra R M :=
  DirectSum.toModule R ℕ _ fun _ ↦ toSymmetricAlgebra

@[simp]
theorem ofDirectSum_of {n : ℕ} (x : Sym[R]^n M) :
    ofDirectSum (DirectSum.of _ n x) = toSymmetricAlgebra x := by
  simp [ofDirectSum, ← DirectSum.lof_eq_of R]

theorem toDirectSum_comp_ofDirectSum :
    toDirectSum ∘ₗ ofDirectSum = (LinearMap.id : (⨁ n, Sym[R]^n M) →ₗ[R] _) :=
  DirectSum.linearMap_ext _ fun n ↦ SymmetricPower.ext <| MultilinearMap.ext fun x ↦ by
    simp [DirectSum.lof_eq_of]

@[simp]
theorem toDirectSum_ofDirectSum (x : ⨁ n, Sym[R]^n M) : toDirectSum (ofDirectSum x) = x :=
  LinearMap.congr_fun toDirectSum_comp_ofDirectSum x

theorem ofDirectSum_comp_toDirectSum :
    ofDirectSum ∘ₗ toDirectSum = (LinearMap.id : SymmetricAlgebra R M →ₗ[R] _) := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := algHom_surjective R M x
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  induction a using TensorAlgebra.induction_tprod with
  | tprod n x => rw [algHom_tprod, toDirectSum_ιMulti, ofDirectSum_of, toSymmetricAlgebra_tprod]
  | smul r a h => simp only [map_smul, h]
  | add a b ha hb => simp only [map_add, ha, hb]

@[simp]
theorem ofDirectSum_toDirectSum (x : SymmetricAlgebra R M) : ofDirectSum (toDirectSum x) = x :=
  LinearMap.congr_fun ofDirectSum_comp_toDirectSum x

variable (R M) in
/-- The symmetric algebra is the direct sum of the symmetric powers, as a module. -/
@[simps!]
noncomputable def equivDirectSum : SymmetricAlgebra R M ≃ₗ[R] ⨁ n, Sym[R]^n M :=
  .ofLinearMap toDirectSum ofDirectSum toDirectSum_comp_ofDirectSum ofDirectSum_comp_toDirectSum

end SymmetricAlgebra

namespace SymmetricPower

variable {R : Type} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem toSymmetricAlgebra_injective (n : ℕ) :
    Function.Injective (toSymmetricAlgebra (R := R) (M := M) (κ := Fin n)) := by
  refine .of_comp (f := SymmetricAlgebra.toDirectSum) ?_
  rw [← LinearMap.coe_comp, SymmetricAlgebra.toDirectSum_comp_toSymmetricAlgebra]
  exact DirectSum.of_injective n

end SymmetricPower
