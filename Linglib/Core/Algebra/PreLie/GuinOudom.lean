/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.LinearAlgebra.SymmetricAlgebra.Derivation
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.NonAssoc.PreLie.Basic
import Mathlib.Algebra.NonAssoc.LieAdmissible.Defs

set_option autoImplicit false

/-!
# The Guin-Oudom isomorphism for pre-Lie algebras
@cite{oudom-guin-2008}
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{chapoton-livernet-2001}
@cite{manchon-2011}

Let `(L, ▷)` be a (right) pre-Lie algebra over a commutative ring `R`. The
**Guin-Oudom theorem** (Oudom-Guin 2008) states that the symmetric algebra
`S(L)` carries a canonical non-commutative product `★` such that
`(S(L), ★)` is associative and isomorphic as an `R`-algebra to the
universal enveloping algebra `U(L_Lie)` of the Lie algebra obtained from
`L` by antisymmetrization.

This file builds the abstract substrate. Specialization to
`InsertionAlgebra α` (the pre-Lie algebra on nonplanar rooted trees,
Foissy 2018 Prop 2.2) is in `Linglib/Core/Algebra/RootedTree/PreLie/`,
and the Grossman-Larson product on
`ConnesKreimer ℤ (Nonplanar α) ≅ S(InsertionAlgebra α)` is in R.5.

## Convention

We use the **right pre-Lie** convention `associator x y z = associator x z y`
throughout, matching `RightPreLieRing`/`RightPreLieAlgebra`. Foissy 2018
uses the LEFT pre-Lie convention; the conversion is the `Lᵐᵒᵖ` opposite
multiplication and is mediated by mathlib's
`RightPreLieRing.instLeftPreLieRingMop`. Foissy formulas can be cited
after the convention swap.

## Mathematical structure (forward look)

For a `RightPreLieAlgebra R L`:

1. **Lie bracket** (free from mathlib): `[x, y] := x * y - y * x` via
   `RightPreLieRing → LieAdmissibleRing → LieRing` instance chain.
2. **Pre-Lie action `▷` on `S(L)`** (R.4.1, this file): for each `x : L`,
   a derivation `δ_x : S(L) → S(L)` extending `δ_x (ι y) = ι (x * y)`
   via `SymmetricAlgebra.liftDerivation`.
3. **Guin-Oudom product `★`** (R.4.2): defined by recursion
   `(ι x * s) ★ t = ι x * (s ★ t) - (x ▷ s) ★ t` and bilinear extension.
4. **Associativity of `★`** (R.4.3): the deep step. Foissy 2018 Prop 2.7.
5. **Iso `(S(L), ★) ≃ₐ[R] U(L_Lie)`** (R.4.4): via universal property
   of `SymmetricAlgebra.lift` and `UniversalEnvelopingAlgebra.lift`.

## Implementation status (R.4 C1)

§1 (the pre-Lie action `▷`) is sorry-free. The `★` product, associativity,
and iso are introduced in subsequent commits.

## Note on the substrate

The mathlib-gap `SymmetricAlgebra.liftDerivation` (universal property of
derivations on `S(M)`) is in the sibling file
`Linglib/Core/Algebra/SymmetricAlgebra/Derivation.lean`, kept separate as
an upstream-PR candidate. -/

/-! ### Sanity tests: Lie instances are inferable from `RightPreLieRing`

Mathlib's instance chain `RightPreLieRing → LieAdmissibleRing → LieRing`
(`Mathlib/Algebra/NonAssoc/LieAdmissible/Defs.lean`, Tapia 2025) makes
the Lie bracket `[x, y] := x * y - y * x` automatic. Same for the
algebra version. We don't need any manual derivation in linglib. -/

section LieInstanceTests

variable {R : Type*} [CommRing R]
variable {L : Type*} [RightPreLieRing L] [RightPreLieAlgebra R L]

example : LieRing L := inferInstance
example : LieAlgebra R L := inferInstance

end LieInstanceTests

/-! ## §1: The pre-Lie action `▷ : L × S(L) → S(L)`

For a `RightPreLieAlgebra R L`, the pre-Lie product `· : L × L → L` extends
canonically to an `R`-linear "action" `▷ : L → S(L) → S(L)` via Leibniz,
using the substrate `SymmetricAlgebra.liftDerivation`. Specifically, for
fixed `x : L`, the function `y ↦ ι (x * y) : L → S(L)` lifts to a
self-derivation `δ_x` of `S(L)`. The collection `{δ_x}_{x : L}` packages
as a linear map from `L` to `Derivation R (S(L)) (S(L))`. -/

namespace PreLie

namespace GuinOudom

variable {R : Type*} [CommRing R]
variable {L : Type*} [RightPreLieRing L] [RightPreLieAlgebra R L]

/-- The per-x linear map `L →ₗ[R] S(L)`: `y ↦ ι (x * y)`. Composition of
mathlib's `LinearMap.mulLeft x : L →ₗ[R] L` (the `R`-linear left
multiplication-by-x, available since `RightPreLieAlgebra` provides
`SMulCommClass R L L`) with the canonical inclusion `SymmetricAlgebra.ι`. -/
private noncomputable def actionLinearMap (x : L) :
    L →ₗ[R] SymmetricAlgebra R L :=
  (SymmetricAlgebra.ι R L).comp (LinearMap.mulLeft R x)

@[simp]
private theorem actionLinearMap_apply (x y : L) :
    actionLinearMap (R := R) x y = SymmetricAlgebra.ι R L (x * y) :=
  rfl

/-- The per-x linear map `actionLinearMap` is `R`-linear in `x`. Bundled
as a linear map for use in `preLieAction`. -/
private noncomputable def actionLinearMapBundled :
    L →ₗ[R] L →ₗ[R] SymmetricAlgebra R L where
  toFun x := actionLinearMap x
  map_add' x y := by
    ext z
    simp only [actionLinearMap_apply, add_mul, map_add, LinearMap.add_apply]
  map_smul' r x := by
    ext z
    simp only [actionLinearMap_apply, smul_mul_assoc, map_smul, RingHom.id_apply,
               LinearMap.smul_apply]

/-- The **pre-Lie action** of `L` on `SymmetricAlgebra R L`, as a linear
map `L →ₗ[R] Derivation R (S(L)) (S(L))`: for each `x : L`, the unique
self-derivation extending `y ↦ ι (x * y)`. Composition of
`actionLinearMapBundled` with the substrate equivalence
`SymmetricAlgebra.liftDerivation`. -/
noncomputable def preLieAction :
    L →ₗ[R] Derivation R (SymmetricAlgebra R L) (SymmetricAlgebra R L) :=
  (SymmetricAlgebra.liftDerivation : _ ≃ₗ[R] _).toLinearMap.comp
    actionLinearMapBundled

/-- Notation for the pre-Lie action: `x ▷ s` for `preLieAction x s`. -/
scoped infix:75 " ▷ " => fun x s => preLieAction x s

@[simp]
theorem preLieAction_ι (x y : L) :
    preLieAction (R := R) x (SymmetricAlgebra.ι R L y) =
      SymmetricAlgebra.ι R L (x * y) := by
  show SymmetricAlgebra.liftDerivation _ _ = _
  rw [SymmetricAlgebra.liftDerivation_apply_ι]
  rfl

@[simp]
theorem preLieAction_one (x : L) :
    preLieAction (R := R) x 1 = 0 :=
  Derivation.map_one_eq_zero _

theorem preLieAction_mul (x : L) (s t : SymmetricAlgebra R L) :
    preLieAction (R := R) x (s * t) =
      s • preLieAction (R := R) x t + t • preLieAction (R := R) x s :=
  Derivation.leibniz _ _ _

end GuinOudom

end PreLie
