/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.ConnesKreimer.Shuffle
import Mathlib.RingTheory.Bialgebra.Basic

set_option autoImplicit false

/-!
# Bialgebra structure on `ConnesKreimer R T` via shuffle Δ

Registers `Coalgebra R (ConnesKreimer R T)` and `Bialgebra R (ConnesKreimer R T)`
instances using `comulShuffle` (the shuffle/polynomial coproduct, where each
tree is primitive: `Δ(of' {t}) = of' {t} ⊗ 1 + 1 ⊗ of' {t}`) and the existing
`counit` (empty-forest coefficient extractor).

This is **distinct** from mathlib's default `AddMonoidAlgebra.instBialgebra`
(which uses the group-like coproduct `single g r ↦ single g r ⊗ single g r`).
The one-field structure wrapper on `ConnesKreimer R T` keeps the two
unambiguous: typeclass synthesis on `ConnesKreimer R T` finds the shuffle
Bialgebra instance, while `AddMonoidAlgebra R (Forest T)` retains the
group-like one.

## Status

Phase A2 of Path A-honest (convolution route to GL associativity).
`[UPSTREAM]` candidate (the parametric construction is mathlib-generic).
-/

namespace RootedTree

namespace ConnesKreimer

universe u v
variable {R : Type u} [CommSemiring R] {T : Type v}

open scoped TensorProduct

/-! ### §1: Counit laws

`(ε ⊗ id) ∘ Δ = mk R 1` and `(id ⊗ ε) ∘ Δ = (mk R).flip 1`. Proved by
LinearMap-extensionality reduction to basis `of' F₀`, then induction on
the multiset `F₀` via multiplicativity (`comulShuffle_mul` +
`Algebra.TensorProduct` algebra-hom structure on the targets). -/

/-- Helper: `(ε ⊗ id)` packaged as an `AlgHom` agrees with
    `counit.toLinearMap.rTensor _` on simple tensors, hence as `LinearMap`s. -/
private theorem map_counit_id_eq_rTensor [DecidableEq T] :
    (Algebra.TensorProduct.map (counit (R := R) (T := T))
        (AlgHom.id R (ConnesKreimer R T))).toLinearMap =
      (counit (R := R) (T := T)).toLinearMap.rTensor (ConnesKreimer R T) := by
  ext x y
  show (Algebra.TensorProduct.map (counit (R := R) (T := T))
          (AlgHom.id R (ConnesKreimer R T))) (x ⊗ₜ[R] y) =
       (counit (R := R) (T := T)).toLinearMap.rTensor (ConnesKreimer R T) (x ⊗ₜ[R] y)
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.rTensor_tmul]
  rfl

/-- Helper: `(id ⊗ ε)` packaged as an `AlgHom` agrees with
    `counit.toLinearMap.lTensor _` on simple tensors. -/
private theorem map_id_counit_eq_lTensor [DecidableEq T] :
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R T))
        (counit (R := R) (T := T))).toLinearMap =
      (counit (R := R) (T := T)).toLinearMap.lTensor (ConnesKreimer R T) := by
  ext x y
  show (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R T))
          (counit (R := R) (T := T))) (x ⊗ₜ[R] y) =
       (counit (R := R) (T := T)).toLinearMap.lTensor (ConnesKreimer R T) (x ⊗ₜ[R] y)
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.lTensor_tmul]
  rfl

/-- Pointwise left counit law on basis multisets: by induction on `F₀`,
    using multiplicativity of `(ε ⊗ id)` and `comulShuffle`. -/
private theorem rTensor_counit_comulShuffle_basis [DecidableEq T] (F₀ : Forest T) :
    (counit (R := R)).toLinearMap.rTensor (ConnesKreimer R T)
        (comulShuffle (R := R) (of' F₀)) =
      (1 : R) ⊗ₜ[R] (of' (R := R) F₀ : ConnesKreimer R T) := by
  -- Repackage RHS via map AlgHom.
  rw [← map_counit_id_eq_rTensor (R := R)]
  show (Algebra.TensorProduct.map (counit (R := R))
          (AlgHom.id R (ConnesKreimer R T)))
        (comulShuffle (R := R) (of' F₀)) =
      (1 : R) ⊗ₜ[R] (of' (R := R) F₀)
  induction F₀ using Multiset.induction with
  | empty =>
    rw [of'_zero, comulShuffle_one, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, map_one]
  | cons a s ih =>
    -- `of' (a ::ₘ s) = of' {a} * of' s`.
    rw [show (a ::ₘ s : Forest T) = ({a} : Forest T) + s from
          (Multiset.singleton_add a s).symm,
        of'_add, of'_singleton, comulShuffle_mul, map_mul]
    -- Singleton: Δ(of' {a}) = of' {a} ⊗ 1 + 1 ⊗ of' {a};
    -- then (ε ⊗ id) collapses the first summand to 0 (counit of card-1 forest).
    have h_single : (Algebra.TensorProduct.map (counit (R := R))
            (AlgHom.id R (ConnesKreimer R T)))
          (comulShuffle (R := R) (ofTree a : ConnesKreimer R T)) =
        (1 : R) ⊗ₜ[R] (ofTree a : ConnesKreimer R T) := by
      show (Algebra.TensorProduct.map (counit (R := R))
              (AlgHom.id R (ConnesKreimer R T)))
            (comulShuffle (R := R) (of' (R := R) ({a} : Forest T))) = _
      rw [comulShuffle_of']
      -- ({a} : Multiset T).powerset = {0, {a}}.
      rw [show ({a} : Multiset T).powerset =
            ((0 : Multiset T) ::ₘ {({a} : Multiset T)}) from by
            rw [show ({a} : Multiset T) = a ::ₘ 0 from rfl,
                Multiset.powerset_cons, Multiset.powerset_zero]
            rfl]
      rw [Multiset.map_cons, Multiset.sum_cons,
          Multiset.map_singleton, Multiset.sum_singleton]
      -- Two summands: (of' 0 ⊗ of' {a}) and (of' {a} ⊗ of' 0).
      rw [Multiset.sub_zero, of'_zero,
          show ({a} : Multiset T) - ({a} : Multiset T) = (0 : Multiset T) from
            tsub_self _, of'_zero]
      rw [map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, AlgHom.id_apply, map_one, of'_singleton]
      -- counit (ofTree a) = 0; ofTree a is on the right of the second tmul.
      rw [counit_ofTree, TensorProduct.zero_tmul, add_zero]
    rw [h_single, ih]
    -- Combine: (1 ⊗ ofTree a) * (1 ⊗ of' s) = 1 ⊗ (ofTree a * of' s).
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- Pointwise right counit law on basis multisets. Mirror of
    `rTensor_counit_comulShuffle_basis`. -/
private theorem lTensor_counit_comulShuffle_basis [DecidableEq T] (F₀ : Forest T) :
    (counit (R := R)).toLinearMap.lTensor (ConnesKreimer R T)
        (comulShuffle (R := R) (of' F₀)) =
      (of' (R := R) F₀ : ConnesKreimer R T) ⊗ₜ[R] (1 : R) := by
  rw [← map_id_counit_eq_lTensor (R := R)]
  show (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R T))
          (counit (R := R)))
        (comulShuffle (R := R) (of' F₀)) =
      (of' (R := R) F₀) ⊗ₜ[R] (1 : R)
  induction F₀ using Multiset.induction with
  | empty =>
    rw [of'_zero, comulShuffle_one, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, map_one]
  | cons a s ih =>
    rw [show (a ::ₘ s : Forest T) = ({a} : Forest T) + s from
          (Multiset.singleton_add a s).symm,
        of'_add, of'_singleton, comulShuffle_mul, map_mul]
    have h_single : (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R T))
            (counit (R := R)))
          (comulShuffle (R := R) (ofTree a : ConnesKreimer R T)) =
        (ofTree a : ConnesKreimer R T) ⊗ₜ[R] (1 : R) := by
      show (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R T))
              (counit (R := R)))
            (comulShuffle (R := R) (of' (R := R) ({a} : Forest T))) = _
      rw [comulShuffle_of']
      rw [show ({a} : Multiset T).powerset =
            ((0 : Multiset T) ::ₘ {({a} : Multiset T)}) from by
            rw [show ({a} : Multiset T) = a ::ₘ 0 from rfl,
                Multiset.powerset_cons, Multiset.powerset_zero]
            rfl]
      rw [Multiset.map_cons, Multiset.sum_cons,
          Multiset.map_singleton, Multiset.sum_singleton]
      rw [Multiset.sub_zero, of'_zero,
          show ({a} : Multiset T) - ({a} : Multiset T) = (0 : Multiset T) from
            tsub_self _, of'_zero]
      rw [map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, AlgHom.id_apply, map_one, of'_singleton]
      rw [counit_ofTree, TensorProduct.tmul_zero, zero_add]
    rw [h_single, ih]
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- LinearMap form of the left counit law: `(ε ⊗ id) ∘ Δ = mk R 1`. -/
theorem rTensor_counit_comulShuffle [DecidableEq T] :
    (counit (R := R)).toLinearMap.rTensor (ConnesKreimer R T) ∘ₗ
        (comulShuffle (R := R)) =
      TensorProduct.mk R R (ConnesKreimer R T) 1 := by
  -- Reduce arbitrary `x` to basis singleton via `addHom_ext`.
  ext x
  show (counit (R := R)).toLinearMap.rTensor (ConnesKreimer R T)
        (comulShuffle (R := R) x) =
       TensorProduct.mk R R (ConnesKreimer R T) 1 x
  have h : (((counit (R := R)).toLinearMap.rTensor (ConnesKreimer R T)).comp
              (comulShuffle (R := R))).toAddMonoidHom =
           (TensorProduct.mk R R (ConnesKreimer R T) 1 :
              ConnesKreimer R T →ₗ[R] R ⊗[R] ConnesKreimer R T).toAddMonoidHom := by
    refine addHom_ext fun F₀ r => ?_
    set sF : ConnesKreimer R T := single F₀ r with sF_def
    show (counit (R := R)).toLinearMap.rTensor (ConnesKreimer R T)
          (comulShuffle (R := R) sF) =
         TensorProduct.mk R R (ConnesKreimer R T) 1 sF
    rw [show sF = r • of' (R := R) F₀ from smul_single_one F₀ r]
    rw [LinearMap.map_smul, LinearMap.map_smul,
        rTensor_counit_comulShuffle_basis (R := R) F₀]
    show r • ((1 : R) ⊗ₜ[R] of' (R := R) F₀) =
         TensorProduct.mk R R (ConnesKreimer R T) 1 (r • of' (R := R) F₀)
    rw [LinearMap.map_smul]
    rfl
  exact DFunLike.congr_fun h x

/-- LinearMap form of the right counit law: `(id ⊗ ε) ∘ Δ = (mk R).flip 1`. -/
theorem lTensor_counit_comulShuffle [DecidableEq T] :
    (counit (R := R)).toLinearMap.lTensor (ConnesKreimer R T) ∘ₗ
        (comulShuffle (R := R)) =
      (TensorProduct.mk R (ConnesKreimer R T) R).flip 1 := by
  ext x
  show (counit (R := R)).toLinearMap.lTensor (ConnesKreimer R T)
        (comulShuffle (R := R) x) =
       (TensorProduct.mk R (ConnesKreimer R T) R).flip 1 x
  have h : (((counit (R := R)).toLinearMap.lTensor (ConnesKreimer R T)).comp
              (comulShuffle (R := R))).toAddMonoidHom =
           ((TensorProduct.mk R (ConnesKreimer R T) R).flip 1 :
              ConnesKreimer R T →ₗ[R] ConnesKreimer R T ⊗[R] R).toAddMonoidHom := by
    refine addHom_ext fun F₀ r => ?_
    set sF : ConnesKreimer R T := single F₀ r with sF_def
    show (counit (R := R)).toLinearMap.lTensor (ConnesKreimer R T)
          (comulShuffle (R := R) sF) =
         (TensorProduct.mk R (ConnesKreimer R T) R).flip 1 sF
    rw [show sF = r • of' (R := R) F₀ from smul_single_one F₀ r]
    rw [LinearMap.map_smul, LinearMap.map_smul,
        lTensor_counit_comulShuffle_basis (R := R) F₀]
    show r • (of' (R := R) F₀ ⊗ₜ[R] (1 : R)) =
         (TensorProduct.mk R (ConnesKreimer R T) R).flip 1 (r • of' (R := R) F₀)
    rw [LinearMap.map_smul]
    rfl
  exact DFunLike.congr_fun h x

/-! ### §2: Coalgebra and Bialgebra instances -/

/-- Underlying `CoalgebraStruct` data. -/
noncomputable instance instCoalgebraStruct [DecidableEq T] :
    CoalgebraStruct R (ConnesKreimer R T) where
  comul := comulShuffle (R := R)
  counit := (counit (R := R) : ConnesKreimer R T →ₐ[R] R).toLinearMap

/-- The Coalgebra structure on `ConnesKreimer R T` with shuffle Δ. -/
noncomputable instance instCoalgebra [DecidableEq T] :
    Coalgebra R (ConnesKreimer R T) where
  coassoc := comulShuffle_coassoc
  rTensor_counit_comp_comul := rTensor_counit_comulShuffle
  lTensor_counit_comp_comul := lTensor_counit_comulShuffle

/-- The Bialgebra structure on `ConnesKreimer R T` with shuffle Δ. -/
noncomputable instance instBialgebra [DecidableEq T] :
    Bialgebra R (ConnesKreimer R T) where
  counit_one := by
    show (counit (R := R) : ConnesKreimer R T →ₐ[R] R) 1 = 1
    exact map_one _
  mul_compr₂_counit := by
    ext a b
    show (counit (R := R) : ConnesKreimer R T →ₐ[R] R) (a * b) =
         (counit (R := R) : ConnesKreimer R T →ₐ[R] R) a *
           (counit (R := R) : ConnesKreimer R T →ₐ[R] R) b
    exact map_mul _ a b
  comul_one := comulShuffle_one
  mul_compr₂_comul := by
    ext a b
    show comulShuffle (R := R) (a * b) =
         comulShuffle (R := R) a * comulShuffle (R := R) b
    exact comulShuffle_mul a b

end ConnesKreimer

end RootedTree
