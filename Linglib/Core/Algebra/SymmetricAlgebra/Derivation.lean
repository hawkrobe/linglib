/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic

set_option autoImplicit false

/-!
# Derivations on the symmetric algebra

The universal property of `SymmetricAlgebra R M` for derivations: an
`R`-linear map `f : M → SymmetricAlgebra R M` extends uniquely to a
self-derivation `D : SymmetricAlgebra R M → SymmetricAlgebra R M` with
`D ∘ ι = f`. Packaged as a linear equivalence
`SymmetricAlgebra.liftDerivation` between `R`-linear maps and self-derivations.

Sibling of `Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean`'s `lift`
(which gives the algebra-hom universal property). This file fills the
mathlib gap for the derivation universal property — candidate for upstream.

## Main definitions

* `SymmetricAlgebra.liftDerivation` — the linear equivalence between
  `M →ₗ[R] SymmetricAlgebra R M` and `Derivation R (SymmetricAlgebra R M)
  (SymmetricAlgebra R M)`.

## Main results

* `SymmetricAlgebra.derivation_ext` — derivation extensionality on the
  generators `ι R M`. Two self-derivations of `SymmetricAlgebra R M` are
  equal iff they agree on `ι R M y` for all `y : M`.
* `SymmetricAlgebra.liftDerivation_ι` — the forward direction:
  `liftDerivation f (ι R M y) = f y`.

## Construction

The forward direction uses the **dual-number trick** (Cartan-Eilenberg):
the trivial square-zero extension `tsze (S(M)) (S(M)) = S(M) ⊕ S(M) ε`
(with `ε² = 0`) carries an algebra structure such that an algebra hom
`φ : S(M) → tsze (S(M)) (S(M))` of the form `s ↦ (s, D s)` corresponds
exactly to a derivation `D`. We construct `φ` via `SymmetricAlgebra.lift`
applied to `y ↦ (ι R M y, f y)`, then extract `D s := (φ s).snd`.
-/

namespace SymmetricAlgebra

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-! ### Derivation extensionality on generators -/

/-- A self-derivation of `SymmetricAlgebra R M` is determined by its
values on the canonical generators `ι R M y`. The standard universal
property of derivations on a free commutative algebra. -/
@[ext]
theorem derivation_ext
    {D₁ D₂ : Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M)}
    (h : ∀ y : M, D₁ (ι R M y) = D₂ (ι R M y)) :
    D₁ = D₂ := by
  ext s
  induction s using SymmetricAlgebra.induction with
  | algebraMap r => simp only [Derivation.map_algebraMap]
  | ι y => exact h y
  | mul a b ha hb =>
    rw [Derivation.leibniz, Derivation.leibniz, ha, hb]
  | add a b ha hb =>
    rw [Derivation.map_add, Derivation.map_add, ha, hb]

/-! ### Construction via the dual-number trick

The forward map `liftDerivation : (M →ₗ[R] S(M)) → Derivation R (S(M)) (S(M))`,
extended to a linear equivalence below. -/

/-- The `R`-linear inclusion `M →ₗ[R] tsze (S(M)) (S(M))` sending `y` to
`(ι y, f y)`. Helper for `liftDerivation`. -/
private noncomputable def liftDerivationInclusion
    (f : M →ₗ[R] SymmetricAlgebra R M) :
    M →ₗ[R] TrivSqZeroExt (SymmetricAlgebra R M) (SymmetricAlgebra R M) :=
  (TrivSqZeroExt.inrHom (R := SymmetricAlgebra R M) (M := SymmetricAlgebra R M)).restrictScalars R
    ∘ₗ f
  + (TrivSqZeroExt.inlAlgHom R (SymmetricAlgebra R M) (SymmetricAlgebra R M)).toLinearMap
    ∘ₗ (ι R M)

/-- The algebra hom `S(M) →ₐ[R] tsze (S(M)) (S(M))` extending
`liftDerivationInclusion f`. The corresponding derivation is the second
projection of this map. Helper for `liftDerivation`. -/
private noncomputable def liftDerivationAlgHom
    (f : M →ₗ[R] SymmetricAlgebra R M) :
    SymmetricAlgebra R M →ₐ[R]
      TrivSqZeroExt (SymmetricAlgebra R M) (SymmetricAlgebra R M) :=
  SymmetricAlgebra.lift (liftDerivationInclusion f)

private theorem liftDerivationAlgHom_apply_ι
    (f : M →ₗ[R] SymmetricAlgebra R M) (y : M) :
    liftDerivationAlgHom f (ι R M y) =
      TrivSqZeroExt.inr (f y) + TrivSqZeroExt.inl (ι R M y) := by
  unfold liftDerivationAlgHom liftDerivationInclusion
  rw [SymmetricAlgebra.lift_ι_apply]
  simp [TrivSqZeroExt.inrHom, TrivSqZeroExt.inlAlgHom]

/-- The first projection of `liftDerivationAlgHom f` is the identity:
`(liftDerivationAlgHom f s).fst = s` for all `s`. By the uniqueness of
the algebra-hom lift. -/
private theorem liftDerivationAlgHom_fst
    (f : M →ₗ[R] SymmetricAlgebra R M) (s : SymmetricAlgebra R M) :
    (liftDerivationAlgHom f s).fst = s := by
  have heq : (TrivSqZeroExt.fstHom R (SymmetricAlgebra R M) (SymmetricAlgebra R M)).comp
                (liftDerivationAlgHom f) =
              AlgHom.id R (SymmetricAlgebra R M) := by
    apply SymmetricAlgebra.algHom_ext
    ext y
    show (TrivSqZeroExt.fstHom R _ _) (liftDerivationAlgHom f (ι R M y)) = ι R M y
    rw [liftDerivationAlgHom_apply_ι]
    simp [TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_inl]
  exact AlgHom.congr_fun heq s

/-- The forward direction of `liftDerivation`: extract a derivation from
the second projection of the dual-number lift. -/
private noncomputable def liftDerivationFun
    (f : M →ₗ[R] SymmetricAlgebra R M) :
    Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M) where
  toFun := fun s => (liftDerivationAlgHom f s).snd
  map_add' a b := by
    show (liftDerivationAlgHom f (a + b)).snd =
         (liftDerivationAlgHom f a).snd + (liftDerivationAlgHom f b).snd
    simp only [map_add, TrivSqZeroExt.snd_add]
  map_smul' r a := by
    show (liftDerivationAlgHom f (r • a)).snd = r • (liftDerivationAlgHom f a).snd
    simp only [map_smul, TrivSqZeroExt.snd_smul]
  map_one_eq_zero' := by
    show (liftDerivationAlgHom f 1).snd = 0
    simp only [map_one, TrivSqZeroExt.snd_one]
  leibniz' a b := by
    show (liftDerivationAlgHom f (a * b)).snd =
         a • (liftDerivationAlgHom f b).snd + b • (liftDerivationAlgHom f a).snd
    simp only [map_mul, TrivSqZeroExt.snd_mul, liftDerivationAlgHom_fst]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

private theorem liftDerivationFun_ι
    (f : M →ₗ[R] SymmetricAlgebra R M) (y : M) :
    liftDerivationFun f (ι R M y) = f y := by
  show (liftDerivationAlgHom f (ι R M y)).snd = f y
  rw [liftDerivationAlgHom_apply_ι]
  simp [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_inl]

/-! ### Linearity in the input map

The forward map `f ↦ liftDerivationFun f` is `R`-linear, packaged via
`derivation_ext`. -/

private theorem liftDerivationFun_add
    (f g : M →ₗ[R] SymmetricAlgebra R M) :
    liftDerivationFun (f + g) = liftDerivationFun f + liftDerivationFun g := by
  apply derivation_ext
  intro y
  rw [Derivation.add_apply, liftDerivationFun_ι, liftDerivationFun_ι,
      liftDerivationFun_ι]
  rfl

private theorem liftDerivationFun_smul
    (r : R) (f : M →ₗ[R] SymmetricAlgebra R M) :
    liftDerivationFun (r • f) = r • liftDerivationFun f := by
  apply derivation_ext
  intro y
  rw [Derivation.smul_apply, liftDerivationFun_ι, liftDerivationFun_ι]
  rfl

/-! ### The bundled `LinearEquiv` -/

/-- The **derivation universal property** of `SymmetricAlgebra R M`: an
`R`-linear map `f : M → SymmetricAlgebra R M` extends uniquely to a
self-derivation `D : SymmetricAlgebra R M → SymmetricAlgebra R M`. The
correspondence is an `R`-linear equivalence.

The forward direction is constructed via the dual-number trick (see file
docstring). The inverse is restriction-to-`ι`: `D ↦ D.toLinearMap ∘ ι R M`. -/
@[simps! apply_apply]
noncomputable def liftDerivation :
    (M →ₗ[R] SymmetricAlgebra R M) ≃ₗ[R]
      Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M) where
  toFun := liftDerivationFun
  map_add' := liftDerivationFun_add
  map_smul' := liftDerivationFun_smul
  invFun := fun D => D.toLinearMap ∘ₗ (ι R M)
  left_inv f := by
    ext y
    show liftDerivationFun f (ι R M y) = f y
    exact liftDerivationFun_ι f y
  right_inv D := by
    apply derivation_ext
    intro y
    show liftDerivationFun _ (ι R M y) = D (ι R M y)
    rw [liftDerivationFun_ι]
    rfl

@[simp]
theorem liftDerivation_apply_ι (f : M →ₗ[R] SymmetricAlgebra R M) (y : M) :
    liftDerivation f (ι R M y) = f y :=
  liftDerivationFun_ι f y

@[simp]
theorem liftDerivation_symm_apply
    (D : Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M)) :
    liftDerivation.symm D = D.toLinearMap ∘ₗ (ι R M) :=
  rfl

end SymmetricAlgebra
