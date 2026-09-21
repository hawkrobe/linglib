/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Symmetric

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

* [oudom-guin-2008] §2 (Lemma 2.5) — symmetric multilinear lift on
  rank-n symmetric power.

## `[UPSTREAM]` status

Natural home in
`Mathlib/LinearAlgebra/TensorPower/Symmetric.lean` (or sibling file).
Closes the documented "Universal property" TODO listed in that file's
preamble.
-/

@[expose] public section

namespace SymmetricPower

open TensorProduct Equiv

universe u v w
variable {R : Type u} {ι : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- The universal property of `Sym[R] ι M`: a multilinear map `(ι → M) → N` invariant under
permutation of its arguments descends to a linear map `Sym[R] ι M →ₗ[R] N`. It descends because
the kernel congruence of `PiTensorProduct.lift f` contains the generating relation. -/
def lift (f : MultilinearMap R (fun _ : ι ↦ M) N) (hsym : ∀ σ : Perm ι, f.domDomCongr σ = f) :
    Sym[R] ι M →ₗ[R] N where
  toFun := AddCon.lift _ (PiTensorProduct.lift f).toAddMonoidHom <| AddCon.addConGen_le.2 <| by
    rintro _ _ ⟨e, g⟩
    simpa [AddCon.ker_rel] using (DFunLike.congr_fun (hsym e) g).symm
  map_add' := map_add _
  map_smul' r x := by
    induction x using AddCon.induction_on with
    | H y => exact map_smul (PiTensorProduct.lift f) r y

@[simp]
theorem lift_tprod (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (hsym : ∀ σ : Perm ι, f.domDomCongr σ = f) (g : ι → M) : lift f hsym (tprod R g) = f g :=
  PiTensorProduct.lift.tprod g

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
