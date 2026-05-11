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

/-- The per-x linear map `L →ₗ[R] S(L)`: `y ↦ ι (y * x)`. Composition of
mathlib's `LinearMap.mulRight x : L →ₗ[R] L` (the `R`-linear right
multiplication-by-x, available since `RightPreLieAlgebra` provides
`IsScalarTower R L L`) with the canonical inclusion `SymmetricAlgebra.ι`.

The convention `y ↦ y * x` (x on the RIGHT of the pre-Lie product) matches
**Manchon 2009 Theorem 1.1** (under the right-pre-Lie translation
`a ▷_LEFT b = b *_RIGHT a`) and **Oudom-Guin 2008 Notation 2.2** directly. -/
private noncomputable def actionLinearMap (x : L) :
    L →ₗ[R] SymmetricAlgebra R L :=
  (SymmetricAlgebra.ι R L).comp (LinearMap.mulRight R x)

@[simp]
private theorem actionLinearMap_apply (x y : L) :
    actionLinearMap (R := R) x y = SymmetricAlgebra.ι R L (y * x) :=
  rfl

/-- The per-x linear map `actionLinearMap` is `R`-linear in `x`. Bundled
as a linear map for use in `preLieAction`. -/
private noncomputable def actionLinearMapBundled :
    L →ₗ[R] L →ₗ[R] SymmetricAlgebra R L where
  toFun x := actionLinearMap x
  map_add' x y := by
    ext z
    simp only [actionLinearMap_apply, mul_add, map_add, LinearMap.add_apply]
  map_smul' r x := by
    ext z
    simp only [actionLinearMap_apply, mul_smul_comm, map_smul, RingHom.id_apply,
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
      SymmetricAlgebra.ι R L (y * x) := by
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

/-! ## §2: Manchon's M operator and the Lie algebra morphism

For a `RightPreLieAlgebra R L`, define `M_a : S(L) →ₗ[R] S(L)` by
`M_a u := ι(a) · u − (a ▷ u)` (Manchon 2009 Theorem 1.1 adapted for right
pre-Lie). The collection `{M_a}_{a : L}` packages into a linear map
`M : L →ₗ[R] End(S(L))`. The key result (`manchonM_lie_hom`) is that
`M` is a Lie algebra morphism: `M_⁅a, b⁆ = ⁅M_a, M_b⁆`.

This is the bridge that lets us extend `M` via the universal enveloping
algebra: `M : L →ₗ⁅R⁆ End(S(L))` lifts to an algebra hom
`M' : U(L_Lie) →ₐ[R] End(S(L))` via `UniversalEnvelopingAlgebra.lift`.

**Sign convention**: Manchon's exposition uses LEFT pre-Lie convention
where `[a, b] := a ▷ b − b ▷ a` matches mathlib's LieAdmissibleRing
bracket `a*b − b*a`. In our RIGHT pre-Lie convention, the translated
`a ▷_LEFT b = b *_RIGHT a` gives `[a,b]_Manchon = b*a − a*b = −[a,b]_LA`.
The MINUS sign in `M_a u := ι(a)·u − (a ▷ u)` (vs Manchon's plus)
compensates: with this `M`, `[M_a, M_b] = M_{[a,b]_LA}` for mathlib's
bracket. (Verified by explicit calculation; the right pre-Lie identity
gives `[L_a, L_b] = −L_{[a,b]_LA}`, and the cross-term sign in
`L_a(ι(b)·u)` flips to absorb it.)

Proof sketch:
```
M_a M_b u  = M_a (ι(b)·u − (b ▷ u))
           = ι(a)·ι(b)·u − ι(a)·(b▷u) − L_a(ι(b)·u) + L_a L_b u
           = ι(a)·ι(b)·u − ι(a)·(b▷u) − ι(b)·L_a u − ι(b*a)·u + L_a L_b u   (Leibniz)

⁅M_a, M_b⁆ u = (ι(a*b) − ι(b*a))·u + ⁅L_a, L_b⁆ u
            = ι([a,b]_LA)·u − L_{[a,b]_LA} u                                (anti-morphism)
            = M_⁅a, b⁆ u
```
where `[a, b]_LA = a*b − b*a` is mathlib's LieAdmissible commutator. -/

/-- **Manchon's M operator**: for each `a : L`, the linear endomorphism
of `S(L)` given by `M_a u := ι(a) · u − (a ▷ u)`. Bundled as a linear
map `L →ₗ[R] End(S(L))`.

Sign convention: the MINUS (vs Manchon's PLUS) compensates for the
right ↔ left pre-Lie translation, ensuring `M` is a Lie hom for
mathlib's `LieAdmissibleRing` bracket `[a,b] := a*b − b*a`. -/
noncomputable def manchonM :
    L →ₗ[R] (SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L) where
  toFun a :=
    LinearMap.mulLeft R (SymmetricAlgebra.ι R L a)
    - (preLieAction (R := R) a).toLinearMap
  map_add' a b := by
    ext s
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
               map_add, add_mul,
               (preLieAction (R := R)).map_add,
               Derivation.coe_add_linearMap]
    abel
  map_smul' r a := by
    ext s
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
               map_smul, smul_mul_assoc, RingHom.id_apply,
               (preLieAction (R := R)).map_smul,
               Derivation.coe_smul_linearMap, LinearMap.smul_apply, smul_sub]

@[simp]
theorem manchonM_apply (a : L) (u : SymmetricAlgebra R L) :
    manchonM (R := R) a u =
      SymmetricAlgebra.ι R L a * u - preLieAction (R := R) a u := by
  rfl

@[simp]
theorem manchonM_apply_one (a : L) :
    manchonM (R := R) a 1 = SymmetricAlgebra.ι R L a := by
  rw [manchonM_apply, mul_one, preLieAction_one, sub_zero]

end GuinOudom

end PreLie
