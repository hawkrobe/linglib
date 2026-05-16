/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.LinearAlgebra.TensorPower.Symmetric

set_option autoImplicit false

/-!
# Universal property of `SymmetricPower R ι M`

For an `R`-module `M` and an indexing type `ι`, the symmetric tensor
power `Sym[R] ι M` (mathlib's `SymmetricPower`) is universal for
**symmetric multilinear maps** out of `ι → M`: any multilinear map
`f : (ι → M) → N` that is invariant under permutation of arguments
factors uniquely through `Sym[R] ι M`.

This closes the universal property TODO in
`Mathlib/LinearAlgebra/TensorPower/Symmetric.lean`.

## Main definitions

* `SymmetricPower.lift`: given a multilinear map `f : (ι → M) → N` with
  `f.domDomCongr σ = f` for every permutation `σ : Equiv.Perm ι`, returns
  the unique linear map `Sym[R] ι M →ₗ[R] N` factoring `f` through
  `tprod`.
* `SymmetricPower.lift_tprod`: characterization that `lift f` composed
  with `tprod` recovers `f`.

## References

* @cite{oudom-guin-2008} §2 (Lemma 2.5) — symmetric multilinear lift on
  rank-n symmetric power.

## `[UPSTREAM]` status

Natural home in
`Mathlib/LinearAlgebra/TensorPower/Symmetric.lean` (or sibling file).
Closes the documented "Universal property" TODO listed in that file's
preamble.
-/

namespace SymmetricPower

open TensorProduct Equiv

universe u v w
variable {R : Type u} {ι : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-! ## §1: The lift of a symmetric multilinear map

Given a multilinear map `f : (ι → M) → N` that is invariant under
permutation of arguments (`f.domDomCongr σ = f` for all `σ`), we lift
to a linear map `Sym[R] ι M →ₗ[R] N`.

Construction: lift `f` to a linear map `g : (⨂[R] M) →ₗ[R] N` via
`PiTensorProduct.lift`. Verify that `g` respects the symmetric quotient
relation `SymmetricPower.Rel`. Descend to `Sym[R] ι M →ₗ[R] N` via
`AddCon.lift` plus R-action compatibility. -/

/-- Auxiliary: `PiTensorProduct.lift` of a symmetric multilinear map
    respects the permutation relation. -/
private theorem liftAux_rel (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (hsym : ∀ (σ : Perm ι), f.domDomCongr σ = f) :
    ∀ x y, Rel R ι M x y →
      (PiTensorProduct.lift f : (⨂[R] _ : ι, M) →ₗ[R] N) x =
      (PiTensorProduct.lift f : (⨂[R] _ : ι, M) →ₗ[R] N) y := by
  intro x y h
  cases h with
  | perm e g =>
    show (PiTensorProduct.lift f) (PiTensorProduct.tprod R g) =
         (PiTensorProduct.lift f) (PiTensorProduct.tprod R (g ∘ e))
    rw [PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
    -- Goal: f g = f (g ∘ e). Use hsym e: f.domDomCongr e = f, i.e., f (g ∘ e) = f g.
    have := MultilinearMap.ext_iff.mp (hsym e) g
    exact this.symm

/-- Auxiliary: extend the symmetry to `addConGen Rel` by induction. -/
private theorem liftAux_addConGen (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (hsym : ∀ (σ : Perm ι), f.domDomCongr σ = f) :
    ∀ x y, (addConGen (Rel R ι M)) x y →
      (PiTensorProduct.lift f : (⨂[R] _ : ι, M) →ₗ[R] N) x =
      (PiTensorProduct.lift f : (⨂[R] _ : ι, M) →ₗ[R] N) y := by
  intro x y h
  induction h with
  | of x y hxy => exact liftAux_rel f hsym x y hxy
  | refl x => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | add _ _ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]

/-- **Universal property** of `SymmetricPower R ι M`: a multilinear
    map `(ι → M) → N` invariant under permutation lifts uniquely to a
    linear map `Sym[R] ι M →ₗ[R] N`.

    Closes the universal-property TODO in
    `Mathlib/LinearAlgebra/TensorPower/Symmetric.lean`. -/
noncomputable def lift (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (hsym : ∀ (σ : Perm ι), f.domDomCongr σ = f) :
    Sym[R] ι M →ₗ[R] N where
  toFun :=
    AddCon.lift (addConGen (Rel R ι M))
      ((PiTensorProduct.lift f : (⨂[R] _ : ι, M) →ₗ[R] N).toAddMonoidHom)
      (liftAux_addConGen f hsym)
  map_add' := map_add _
  map_smul' r x := by
    -- Use induction on `x : Sym[R] ι M = (addConGen Rel).Quotient`.
    -- For x = mk' y (where y : ⨂[R] M), both sides reduce to
    -- PiTensorProduct.lift f (r • y) = r • PiTensorProduct.lift f y by
    -- linearity of PiTensorProduct.lift f.
    induction x using AddCon.induction_on with
    | H y =>
      show AddCon.lift _ _ _ ((r • (mk R ι M y) : Sym[R] ι M) : Sym[R] ι M) =
           ((r : R) • AddCon.lift _ _ _ (mk R ι M y) : N)
      -- After unfolding mk, AddCon.lift's behavior on mk', and module instances,
      -- both sides reduce to linearity of `PiTensorProduct.lift f`.
      show (PiTensorProduct.lift f) (r • y) = r • (PiTensorProduct.lift f) y
      exact map_smul _ _ _

@[simp]
theorem lift_tprod (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (hsym : ∀ (σ : Perm ι), f.domDomCongr σ = f) (g : ι → M) :
    lift f hsym (tprod R g) = f g := by
  -- `tprod R g = mk R ι M (PiTensorProduct.tprod R g)` by `tprod` definition.
  -- `lift f hsym (mk y) = PiTensorProduct.lift f y` by AddCon.lift's behavior.
  -- `(PiTensorProduct.lift f) (PiTensorProduct.tprod R g) = f g` by `lift.tprod`.
  show ((PiTensorProduct.lift f : (⨂[R] _ : ι, M) →ₗ[R] N).toAddMonoidHom
          (PiTensorProduct.tprod R g) : N) = f g
  rw [LinearMap.toAddMonoidHom_coe, PiTensorProduct.lift.tprod]

@[simp]
theorem lift_comp_tprod (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (hsym : ∀ (σ : Perm ι), f.domDomCongr σ = f) :
    (lift f hsym).compMultilinearMap (tprod R) = f := by
  ext g
  exact lift_tprod f hsym g

/-- Uniqueness of the lift: any linear map `Sym[R] ι M →ₗ N` that
    agrees with `f` on the image of `tprod` equals `lift f hsym`. -/
theorem lift_unique (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (hsym : ∀ (σ : Perm ι), f.domDomCongr σ = f)
    {g : Sym[R] ι M →ₗ[R] N}
    (hg : g.compMultilinearMap (tprod R) = f) :
    g = lift f hsym := by
  -- Reduce to agreement on the image of tprod, which spans Sym[R] ι M.
  apply LinearMap.ext_on (span_tprod_eq_top (R := R) (ι := ι) (M := M)) ?_
  rintro _ ⟨g₀, rfl⟩
  rw [lift_tprod]
  exact MultilinearMap.ext_iff.mp hg g₀

end SymmetricPower
