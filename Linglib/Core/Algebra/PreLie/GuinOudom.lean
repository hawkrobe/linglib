/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.NonAssoc.PreLie.Basic
import Mathlib.Algebra.NonAssoc.LieAdmissible.Defs
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic

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
   via Leibniz on products. Linearizes to
   `▷ : L →ₗ[R] Derivation R (S(L)) (S(L))`.
3. **Guin-Oudom product `★`** (R.4.2): defined by recursion
   `(ι x * s) ★ t = ι x * (s ★ t) - (x ▷ s) ★ t` and bilinear extension.
4. **Associativity of `★`** (R.4.3): the deep step. Foissy 2018 Prop 2.7.
5. **Iso `(S(L), ★) ≃ₐ[R] U(L_Lie)`** (R.4.4): via universal property
   of `SymmetricAlgebra.lift` and `UniversalEnvelopingAlgebra.lift`.

## Implementation status (this commit, R.4.0)

Skeleton + Lie instance sanity tests only. `▷` and `★` are introduced
in subsequent commits.
-/

namespace PreLie

namespace GuinOudom

variable {R : Type*} [CommRing R]
variable {L : Type*} [RightPreLieRing L] [RightPreLieAlgebra R L]

end GuinOudom

end PreLie

/-! ## Sanity tests: Lie instances are inferable from `RightPreLieRing`

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

/-! ## §1: SymmetricAlgebra.liftDerivation substrate (mathlib gap)

To define the pre-Lie action `▷ : L × S(L) → S(L)` we need the basic
fact that an `R`-linear map `f : M → S(M)` extends uniquely to a
**self-derivation** `D : S(M) → S(M)` of the symmetric algebra with
`D (ι R M y) = f y` for all `y : M`.

Mathlib has `SymmetricAlgebra.lift` (algebra-hom universal property) and
`Derivation` (structure with Leibniz) but no direct extension lemma
combining them. We supply it here via the **dual numbers / square-zero
extension** trick (Cartan, encoded in `TrivSqZeroExt`):

  An algebra hom `φ : S(M) → tsze (S(M)) (S(M))` with `φ(ι y) = (ι y, f y)`
  has the form `φ(s) = (s, D s)` for a derivation `D`, by the universal
  property of `SymmetricAlgebra.lift` and the multiplicative structure
  of `tsze`.

This substrate (Cartan-Eilenberg-style) is upstream-candidate for mathlib. -/

namespace SymmetricAlgebra

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

open scoped TrivSqZeroExt

/-- The `R`-linear inclusion `M →ₗ[R] tsze (S(M)) (S(M))` sending `y` to
`(ι y, f y)`. Helper for `liftDerivation`. -/
private noncomputable def liftDerivation_inclusion
    (f : M →ₗ[R] SymmetricAlgebra R M) :
    M →ₗ[R] TrivSqZeroExt (SymmetricAlgebra R M) (SymmetricAlgebra R M) :=
  (TrivSqZeroExt.inrHom (R := SymmetricAlgebra R M) (M := SymmetricAlgebra R M)).restrictScalars R
    ∘ₗ f
  + (TrivSqZeroExt.inlAlgHom R (SymmetricAlgebra R M) (SymmetricAlgebra R M)).toLinearMap
    ∘ₗ (ι R M)

/-- The algebra hom `S(M) →ₐ[R] tsze (S(M)) (S(M))` extending
`liftDerivation_inclusion f`. Helper for `liftDerivation`. -/
private noncomputable def liftDerivation_algHom
    (f : M →ₗ[R] SymmetricAlgebra R M) :
    SymmetricAlgebra R M →ₐ[R]
      TrivSqZeroExt (SymmetricAlgebra R M) (SymmetricAlgebra R M) :=
  SymmetricAlgebra.lift (liftDerivation_inclusion f)

private theorem liftDerivation_algHom_apply_ι
    (f : M →ₗ[R] SymmetricAlgebra R M) (y : M) :
    liftDerivation_algHom f (ι R M y) =
      TrivSqZeroExt.inr (f y) + TrivSqZeroExt.inl (ι R M y) := by
  unfold liftDerivation_algHom liftDerivation_inclusion
  rw [SymmetricAlgebra.lift_ι_apply]
  simp [TrivSqZeroExt.inrHom, TrivSqZeroExt.inlAlgHom]

private theorem liftDerivation_algHom_fst
    (f : M →ₗ[R] SymmetricAlgebra R M) (s : SymmetricAlgebra R M) :
    (liftDerivation_algHom f s).fst = s := by
  have heq : (TrivSqZeroExt.fstHom R (SymmetricAlgebra R M) (SymmetricAlgebra R M)).comp
                (liftDerivation_algHom f) =
              AlgHom.id R (SymmetricAlgebra R M) := by
    apply SymmetricAlgebra.algHom_ext
    ext y
    show (TrivSqZeroExt.fstHom R _ _) (liftDerivation_algHom f (ι R M y)) = ι R M y
    rw [liftDerivation_algHom_apply_ι]
    simp [TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_inl]
  exact AlgHom.congr_fun heq s

/-- An `R`-linear map `f : M → S(M)` extends uniquely to a self-derivation
`D : S(M) → S(M)` agreeing with `f` on the canonical inclusion
`ι R M : M → S(M)`. Constructed via the dual-number trick:
`tsze (S(M)) (S(M))` is the square-zero extension `S(M)[ε]/(ε²)`, and an
algebra hom `S(M) → S(M)[ε]` of the form `s ↦ (s, D s)` corresponds to
a derivation `D`. -/
noncomputable def liftDerivation
    (f : M →ₗ[R] SymmetricAlgebra R M) :
    Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M) where
  toFun := fun s => (liftDerivation_algHom f s).snd
  map_add' a b := by
    show (liftDerivation_algHom f (a + b)).snd =
         (liftDerivation_algHom f a).snd + (liftDerivation_algHom f b).snd
    simp only [map_add]; rfl
  map_smul' r a := by
    show (liftDerivation_algHom f (r • a)).snd = r • (liftDerivation_algHom f a).snd
    simp only [map_smul]
    rfl
  map_one_eq_zero' := by
    show (liftDerivation_algHom f 1).snd = 0
    simp only [map_one]; rfl
  leibniz' a b := by
    show (liftDerivation_algHom f (a * b)).snd =
         a • (liftDerivation_algHom f b).snd + b • (liftDerivation_algHom f a).snd
    simp only [map_mul, TrivSqZeroExt.snd_mul,
               liftDerivation_algHom_fst]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

@[simp]
theorem liftDerivation_ι (f : M →ₗ[R] SymmetricAlgebra R M) (y : M) :
    liftDerivation f (ι R M y) = f y := by
  show (liftDerivation_algHom f (ι R M y)).snd = f y
  rw [liftDerivation_algHom_apply_ι]
  simp [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_inl]

end SymmetricAlgebra

/-! ## §2: The pre-Lie action `▷ : L × S(L) → S(L)`

For a `RightPreLieAlgebra R L`, the pre-Lie product `· : L × L → L` extends
canonically to an `R`-linear "action" `▷ : L → S(L) → S(L)` via Leibniz,
using §1's `liftDerivation`. Specifically, for fixed `x : L`, the function
`y ↦ ι (x * y) : L → S(L)` lifts to a self-derivation `δ_x` of `S(L)`. The
collection `{δ_x}_{x : L}` packages as a linear map `▷` from `L` to
`Derivation R (S(L)) (S(L))`. -/

namespace PreLie

namespace GuinOudom

variable {R : Type*} [CommRing R]
variable {L : Type*} [RightPreLieRing L] [RightPreLieAlgebra R L]

/-- The per-x linear map `L →ₗ[R] S(L)`: `y ↦ ι (x * y)`. Composition of
mathlib's `LinearMap.mulLeft x : L →ₗ[R] L` (the `R`-linear left
multiplication-by-x, available since `RightPreLieAlgebra` gives
`SMulCommClass R L L`) with the canonical inclusion `SymmetricAlgebra.ι`. -/
private noncomputable def actionLinearMap (x : L) :
    L →ₗ[R] SymmetricAlgebra R L :=
  (SymmetricAlgebra.ι R L).comp (LinearMap.mulLeft R x)

@[simp]
private theorem actionLinearMap_apply (x y : L) :
    actionLinearMap (R := R) x y = SymmetricAlgebra.ι R L (x * y) :=
  rfl

/-- The **pre-Lie action** of `L` on `SymmetricAlgebra R L`: for each
`x : L`, the unique self-derivation extending `y ↦ ι (x * y)`. -/
noncomputable def preLieAction (x : L) :
    Derivation R (SymmetricAlgebra R L) (SymmetricAlgebra R L) :=
  SymmetricAlgebra.liftDerivation (actionLinearMap (R := R) x)

/-- Notation for the pre-Lie action: `x ▷ s` for `preLieAction x s`. -/
scoped infix:75 " ▷ " => fun x s => preLieAction x s

@[simp]
theorem preLieAction_ι (x y : L) :
    preLieAction (R := R) x (SymmetricAlgebra.ι R L y) =
      SymmetricAlgebra.ι R L (x * y) := by
  show SymmetricAlgebra.liftDerivation (actionLinearMap (R := R) x)
        (SymmetricAlgebra.ι R L y) = _
  rw [SymmetricAlgebra.liftDerivation_ι, actionLinearMap_apply]

@[simp]
theorem preLieAction_one (x : L) :
    preLieAction (R := R) x 1 = 0 :=
  Derivation.map_one_eq_zero _

theorem preLieAction_mul (x : L) (s t : SymmetricAlgebra R L) :
    preLieAction (R := R) x (s * t) =
      s • preLieAction (R := R) x t + t • preLieAction (R := R) x s :=
  Derivation.leibniz _ _ _

/-! ### Derivation extensionality on generators

A self-derivation of `S(L)` is determined by its values on the
canonical generators `ι R L y`. This is the key tool for proving
linearity of `preLieAction` in the L-argument. -/

private theorem derivationExt
    {D₁ D₂ : Derivation R (SymmetricAlgebra R L) (SymmetricAlgebra R L)}
    (h : ∀ y : L, D₁ (SymmetricAlgebra.ι R L y) = D₂ (SymmetricAlgebra.ι R L y)) :
    D₁ = D₂ := by
  ext s
  induction s using SymmetricAlgebra.induction with
  | algebraMap r => simp only [Derivation.map_algebraMap]
  | ι y => exact h y
  | mul a b ha hb =>
    rw [Derivation.leibniz, Derivation.leibniz, ha, hb]
  | add a b ha hb =>
    rw [Derivation.map_add, Derivation.map_add, ha, hb]

/-! ### Linearity of the action in the L-argument -/

theorem preLieAction_add_left (x y : L) :
    preLieAction (R := R) (x + y) = preLieAction (R := R) x + preLieAction (R := R) y := by
  apply derivationExt
  intro z
  rw [Derivation.add_apply, preLieAction_ι, preLieAction_ι, preLieAction_ι,
      add_mul, map_add]

theorem preLieAction_smul_left (r : R) (x : L) :
    preLieAction (R := R) (r • x) = r • preLieAction (R := R) x := by
  apply derivationExt
  intro z
  rw [Derivation.smul_apply, preLieAction_ι, preLieAction_ι, smul_mul_assoc, map_smul]

theorem preLieAction_zero_left :
    preLieAction (R := R) (0 : L) = 0 := by
  apply derivationExt
  intro z
  rw [Derivation.zero_apply, preLieAction_ι, zero_mul, map_zero]

end GuinOudom

end PreLie
