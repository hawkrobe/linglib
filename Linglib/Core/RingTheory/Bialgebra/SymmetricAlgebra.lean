/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebra structure on `SymmetricAlgebra R M`

The symmetric algebra `S(M)` over an `R`-module `M` is the universal
cocommutative graded connected commutative `R`-bialgebra on `M`: there
is a unique bialgebra map from `S(M)` to any cocommutative graded
connected commutative bialgebra extending a given linear map out of
`M`. The coproduct is determined by the **shuffle** condition that each
generator `ι x` is *primitive*:

* `Δ(ι x) = ι x ⊗ 1 + 1 ⊗ ι x`,
* `ε(ι x) = 0`.

The counit is `SymmetricAlgebra.algebraMapInv`, the canonical algebra
left-inverse of `algebraMap R (S(M))`. Cocommutativity follows from
the symmetry of `ι x ⊗ 1 + 1 ⊗ ι x` under swap.

The Hopf algebra extension (antipode `ι x ↦ −ι x`, requiring
`CommRing R`) lives in `Linglib/Core/RingTheory/HopfAlgebra/SymmetricAlgebra.lean`.

## Main definitions

* `SymmetricAlgebra.instBialgebra` — the `Bialgebra R (SymmetricAlgebra R M)`
  instance, built via `Bialgebra.ofAlgHom`. Provides `Coalgebra`,
  `Bialgebra` instances; downstream code gets `Bialgebra.comulAlgHom`,
  `Bialgebra.counitAlgHom`, `comul_algebraMap`, `comul_natCast`,
  `comul_pow`, `counit_*` analogs via typeclass projection.
* `SymmetricAlgebra.instIsCocomm` — cocommutativity.
* Simp lemmas `algebraMapInv_ι`, `comul_ι`, `counit_ι` on generators.

## Status

**`[UPSTREAM]` candidate.** Natural home is
`Mathlib/RingTheory/Bialgebra/SymmetricAlgebra.lean`. Mathlib currently
has no coproduct on `SymmetricAlgebra`, `TensorAlgebra`, `ExteriorAlgebra`,
or `FreeAlgebra`.

This file follows the **`Bialgebra.ofAlgHom` route**: build the
comultiplication and counit as algebra homomorphisms, check coassoc
+ counit laws at AlgHom level, hand off to mathlib's
`Bialgebra.ofAlgHom` constructor (which builds the `Coalgebra` instance
internally and registers `Bialgebra`). This is the simplest path for
from-scratch constructions; cf. `Mathlib/RingTheory/HopfAlgebra/TensorProduct.lean`
using the analogous `HopfAlgebra.ofAlgHom`.

When upstreaming, replace the three `import` lines with
```
module
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
```
and prepend `@[expose] public section` to the docstring; the
file-level `noncomputable section` and `Type*` style already match
mathlib convention. The `set_option autoImplicit false` line becomes
redundant under the module system.

## References

* Sweedler, *Hopf Algebras* (1969) — primitive elements in cocommutative
  graded connected Hopf algebras, of which `S(M)` is the universal
  example.
-/

set_option autoImplicit false

namespace SymmetricAlgebra

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]

open scoped TensorProduct

noncomputable section

/-! ### Apply lemma for `algebraMapInv` on generators -/

/-- Evaluating `algebraMapInv` (the canonical algebra hom
    `S(M) →ₐ[R] R` sending generators to zero) on `ι x` yields `0`. -/
@[simp]
theorem algebraMapInv_ι (x : M) : algebraMapInv (ι R M x) = (0 : R) := by
  simp [algebraMapInv]

/-! ### Comultiplication

`Δ : S(M) →ₐ[R] S(M) ⊗[R] S(M)` is the unique algebra homomorphism
extending `x ↦ ι x ⊗ 1 + 1 ⊗ ι x` on `M`. The target is a commutative
`R`-algebra, so the universal property `SymmetricAlgebra.lift` applies.

`comulAlgHom` is kept `private`: downstream code uses `Bialgebra.comulAlgHom`
once the instance registers, avoiding namespace collision. -/

private def comulAlgHom : SymmetricAlgebra R M →ₐ[R]
    (SymmetricAlgebra R M ⊗[R] SymmetricAlgebra R M) :=
  lift <|
    (TensorProduct.mk R _ _).flip (1 : SymmetricAlgebra R M) ∘ₗ ι R M +
    TensorProduct.mk R _ _ (1 : SymmetricAlgebra R M) ∘ₗ ι R M

private theorem comulAlgHom_ι (x : M) :
    comulAlgHom R M (ι R M x) = ι R M x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R M x := by
  simp [comulAlgHom, lift_ι_apply]

/-! ### Coalgebra axioms at AlgHom level

Proved on generators via `SymmetricAlgebra.algHom_ext`; transferred to
the LinearMap-level fields of `Coalgebra` inside `Bialgebra.ofAlgHom`. -/

private theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R
        (SymmetricAlgebra R M) (SymmetricAlgebra R M)
        (SymmetricAlgebra R M)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHom R M)
          (.id R (SymmetricAlgebra R M))).comp (comulAlgHom R M)) =
    (Algebra.TensorProduct.map (.id R (SymmetricAlgebra R M))
        (comulAlgHom R M)).comp (comulAlgHom R M) := by
  ext x
  show (Algebra.TensorProduct.assoc R R R _ _ _).toAlgHom
        (Algebra.TensorProduct.map (comulAlgHom R M) (.id R _)
          (comulAlgHom R M (ι R M x))) =
       Algebra.TensorProduct.map (.id R _) (comulAlgHom R M)
          (comulAlgHom R M (ι R M x))
  rw [comulAlgHom_ι]
  simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
             map_one, comulAlgHom_ι, TensorProduct.add_tmul, TensorProduct.tmul_add,
             Algebra.TensorProduct.one_def]
  abel

private theorem rTensor_counit_comp_comul :
    (Algebra.TensorProduct.map (algebraMapInv (R := R) (M := M))
        (.id R (SymmetricAlgebra R M))).comp (comulAlgHom R M) =
      (Algebra.TensorProduct.lid R (SymmetricAlgebra R M)).symm.toAlgHom := by
  ext x
  show Algebra.TensorProduct.map (algebraMapInv (R := R) (M := M))
        (.id R _) (comulAlgHom R M (ι R M x)) =
       (Algebra.TensorProduct.lid R _).symm (ι R M x)
  rw [comulAlgHom_ι]
  simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
             algebraMapInv_ι, map_one, Algebra.TensorProduct.lid_symm_apply,
             TensorProduct.zero_tmul, zero_add]

private theorem lTensor_counit_comp_comul :
    (Algebra.TensorProduct.map (.id R (SymmetricAlgebra R M))
        (algebraMapInv (R := R) (M := M))).comp (comulAlgHom R M) =
      (Algebra.TensorProduct.rid R R (SymmetricAlgebra R M)).symm.toAlgHom := by
  ext x
  show Algebra.TensorProduct.map (.id R _)
        (algebraMapInv (R := R) (M := M)) (comulAlgHom R M (ι R M x)) =
       (Algebra.TensorProduct.rid R R _).symm (ι R M x)
  rw [comulAlgHom_ι]
  simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
             algebraMapInv_ι, map_one, Algebra.TensorProduct.rid_symm_apply,
             TensorProduct.tmul_zero, add_zero]

/-! ### Bialgebra instance

`Bialgebra.ofAlgHom` consumes the AlgHom-level coassoc/counit identities
above and builds both the `Coalgebra` and `Bialgebra` instances in one
shot. -/

/-- The canonical **Bialgebra** structure on `SymmetricAlgebra R M`. -/
instance instBialgebra : Bialgebra R (SymmetricAlgebra R M) :=
  Bialgebra.ofAlgHom (comulAlgHom R M) (algebraMapInv (R := R) (M := M))
    (comul_coassoc R M)
    (rTensor_counit_comp_comul R M)
    (lTensor_counit_comp_comul R M)

/-! ### Public simp lemmas on `Coalgebra.comul` / `Coalgebra.counit`

User-facing forms: simp on `Coalgebra.comul (ι R M x)` reduces to
`ι x ⊗ 1 + 1 ⊗ ι x`. -/

@[simp]
theorem comul_ι (x : M) :
    Coalgebra.comul (R := R) (ι R M x) = ι R M x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R M x :=
  comulAlgHom_ι R M x

@[simp]
theorem counit_ι (x : M) :
    Coalgebra.counit (R := R) (A := SymmetricAlgebra R M) (ι R M x) = 0 :=
  algebraMapInv_ι R M x

/-! ### Cocommutativity -/

private theorem comm_algHom_comp_comul :
    (Algebra.TensorProduct.comm R (SymmetricAlgebra R M)
        (SymmetricAlgebra R M)).toAlgHom.comp (comulAlgHom R M) = comulAlgHom R M := by
  apply algHom_ext
  ext x
  show (Algebra.TensorProduct.comm R _ _) ((comulAlgHom R M) (ι R M x)) =
       (comulAlgHom R M) (ι R M x)
  rw [comulAlgHom_ι]
  simp only [map_add, Algebra.TensorProduct.comm_tmul]
  abel

end

instance instIsCocomm : Coalgebra.IsCocomm R (SymmetricAlgebra R M) where
  comm_comp_comul := by
    ext a
    show (TensorProduct.comm R _ _) ((comulAlgHom R M).toLinearMap a) =
         (comulAlgHom R M).toLinearMap a
    exact AlgHom.ext_iff.mp (comm_algHom_comp_comul R M) a

end SymmetricAlgebra
