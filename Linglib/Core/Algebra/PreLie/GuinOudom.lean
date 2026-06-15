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
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-!
# The Guin-Oudom isomorphism for pre-Lie algebras
[oudom-guin-2008]
[foissy-typed-decorated-rooted-trees-2018]
[chapoton-livernet-2001]
[manchon-2011]

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

## Main definitions

For a `RightPreLieAlgebra R L`:

* `PreLie.GuinOudom.preLieAction` — the pre-Lie action `▷ : L →ₗ[R]
  Der R (S(L)) (S(L))` extending `x ▷ ι y = ι (y * x)` via
  `SymmetricAlgebra.liftDerivation` (the mathlib-gap substrate, in the
  sibling file `Core/LinearAlgebra/SymmetricAlgebra/Derivation.lean`).
* `PreLie.GuinOudom.M` — Manchon's operator `M_a u := ι(a) · u − (a ▷ u)`,
  bundled as `L →ₗ[R] End(S(L))`. The MINUS sign (vs Manchon's PLUS)
  compensates for the right-to-left pre-Lie translation.
* `PreLie.GuinOudom.MLieHom` — `M` as a Lie algebra morphism, witnessed by
  `M_lie_hom : M ⁅a, b⁆ = ⁅M a, M b⁆` for the mathlib `LieAdmissibleRing`
  bracket.
* `PreLie.GuinOudom.MAlgHom` — the lift `U(L_Lie) →ₐ[R] End(S(L))` via
  `UniversalEnvelopingAlgebra.lift R MLieHom`.
* `PreLie.GuinOudom.η` — Manchon's `η : U(L_Lie) →ₗ[R] S(L)`, defined as
  `η(u) := MAlgHom u 1`.

## TODO

* `★ : SymmetricAlgebra R L → SymmetricAlgebra R L → SymmetricAlgebra R L` —
  the Guin-Oudom product, naturally defined as `s ★ t := η(η⁻¹(s) · η⁻¹(t))`.
  Requires `η` to be an isomorphism, i.e. the PBW theorem for
  `U(L_Lie) ≅ S(L)` as filtered modules. Mathlib does not currently have
  PBW (no `Poincare`/`BirkhoffWitt`/`Witt`/`PBW` namespace; no
  `SymmetricAlgebra ≃ UEA`; no associated-graded for UEA; only adjacent
  is `UEA(FreeLieAlg X) ≃ FreeAlgebra X` in `Mathlib.Algebra.Lie.Free`
  which doesn't generalize). Blocked on PBW upstream.
* `guinOudom : (SymmetricAlgebra R L, ★) ≃ₐ[R] UniversalEnvelopingAlgebra R L`
  — the Guin-Oudom isomorphism. Same blocker.
* For downstream `Δ^c` coassociativity on
  `ConnesKreimer ℤ (Nonplanar α)`, the Grossman-Larson product is
  defined directly via Foissy 2021 Theorem 5.1's combinatorial formula
  in `Linglib/Core/Algebra/RootedTree/GrossmanLarson.lean`, bypassing
  the abstract `★` and the PBW dependency. -/

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

-- The commutator `LieRing`/`LieAlgebra` on the endomorphism ring
-- `Module.End R (S(L))` is `local` in mathlib (`Algebra.Lie.OfAssociative`);
-- bring it into scope so `MLieHom`/`MAlgHom` can target it.
attribute [local instance 100] LieRing.ofAssociativeRing

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
`M : L →ₗ[R] End(S(L))`. The key result (`M_lie_hom`) is that
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
noncomputable def M :
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
theorem M_apply (a : L) (u : SymmetricAlgebra R L) :
    M (R := R) a u =
      SymmetricAlgebra.ι R L a * u - preLieAction (R := R) a u := by
  rfl

@[simp]
theorem M_apply_one (a : L) :
    M (R := R) a 1 = SymmetricAlgebra.ι R L a := by
  rw [M_apply, mul_one, preLieAction_one, sub_zero]

/-! ### `preLieAction` is a Lie ANTI-morphism

Key intermediate result: `⁅preLieAction a, preLieAction b⁆ = -preLieAction ⁅a, b⁆`
as derivations of `S(L)`. Equivalently, `preLieAction : L → Der S(L)` is a
Lie hom into the OPPOSITE Lie algebra structure on derivations.

The sign comes from our right pre-Lie convention: with `T ▷ Y = ι(Y * T)`
(T on right of pre-Lie), the commutator `[L_a, L_b] u` for `u ∈ L`
expands to `ι((u*b)*a − (u*a)*b)`, which by the right pre-Lie identity
(associator symmetric in last two) equals `ι(u*(b*a) − u*(a*b)) =
ι(−u*[a,b]_LA) = −L_{[a,b]_LA} u`. -/

private theorem preLieAction_lie_anti (a b : L) :
    ⁅preLieAction (R := R) a, preLieAction (R := R) b⁆ =
      -preLieAction (R := R) ⁅a, b⁆ := by
  apply SymmetricAlgebra.derivation_ext
  intro u
  rw [Derivation.commutator_apply, Derivation.neg_apply]
  simp only [preLieAction_ι]
  -- Goal: ι((u * b) * a) - ι((u * a) * b) = -ι(u * ⁅a, b⁆)
  rw [Ring.lie_def, mul_sub, map_sub, neg_sub]
  -- Goal: ι((u*b)*a) - ι((u*a)*b) = ι(u*(b*a)) - ι(u*(a*b))
  -- Right pre-Lie identity: (u*b)*a - u*(b*a) = (u*a)*b - u*(a*b)
  have h := RightPreLieRing.assoc_symm' u b a
  simp only [associator_apply] at h
  -- h : (u * b) * a - u * (b * a) = (u * a) * b - u * (a * b)
  -- Transport to S(L) via ι, then close by linear arithmetic on the
  -- AddCommGroup `S(L)` (linear_combination handles the rearrangement).
  have hS : SymmetricAlgebra.ι R L ((u * b) * a)
            - SymmetricAlgebra.ι R L (u * (b * a)) =
            SymmetricAlgebra.ι R L ((u * a) * b)
            - SymmetricAlgebra.ι R L (u * (a * b)) := by
    rw [← map_sub, ← map_sub, h]
  linear_combination hS

/-! ### `M` is a Lie algebra morphism

The deep step. By Manchon (2009) Theorem 1.1, the operator `M_a u :=
ι(a) · u − (a ▷ u)` is a Lie algebra morphism `L → End(S(L))`. This is
the bridge that lets us extend `M` via the universal enveloping algebra
`U(L_Lie)`. -/

/-- Helper: `M_a` applied to `ι(b) · u` expands via Leibniz. -/
private theorem M_apply_ι_mul (a b : L) (u : SymmetricAlgebra R L) :
    M (R := R) a (SymmetricAlgebra.ι R L b * u) =
      SymmetricAlgebra.ι R L a * SymmetricAlgebra.ι R L b * u
      - SymmetricAlgebra.ι R L (b * a) * u
      - SymmetricAlgebra.ι R L b * preLieAction (R := R) a u := by
  rw [M_apply, preLieAction_mul, preLieAction_ι]
  -- Goal: ι a * (ι b * u) - (ι b • L_a u + u • ι(b*a)) = ...
  -- The Derivation.leibniz uses • for the algebra action (=mul on S(L)).
  simp only [smul_eq_mul]
  ring

/-- **Main result of §2**: `M` is a Lie algebra morphism `L → End(S(L))`.
For all `a, b : L`, `M_⁅a, b⁆ = ⁅M_a, M_b⁆` where the bracket on `End(S(L))`
is the commutator under composition.

By Manchon (2009) Theorem 1.1 (adapted to right pre-Lie convention with
the sign correction). The proof unwinds the commutator pointwise on `S(L)`,
expands `M_a (ι(b) · u - L_b u)` via Leibniz, and uses the right pre-Lie
identity (encapsulated as `preLieAction_lie_anti`) to identify the
remaining `[L_a, L_b] u` term with `-L_⁅a, b⁆ u`. -/
theorem M_lie_hom (a b : L) :
    M (R := R) ⁅a, b⁆ =
      ⁅M (R := R) a, M (R := R) b⁆ := by
  apply LinearMap.ext
  intro u
  -- Expand RHS bracket on Module.End R (S(L)) into composition/subtraction.
  rw [show (⁅M (R := R) a, M (R := R) b⁆ : Module.End R _) =
        M (R := R) a * M (R := R) b -
        M (R := R) b * M (R := R) a from
        Ring.lie_def _ _]
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  -- Expand inner applications: M b u and M a u.
  rw [M_apply b u, M_apply a u]
  -- Push outer M through subtraction; expand ι-mul and L-action parts.
  rw [map_sub, map_sub, M_apply_ι_mul, M_apply_ι_mul,
      M_apply, M_apply]
  -- Expand LHS: M ⁅a,b⁆ u via M_apply.
  rw [M_apply]
  -- Apply Ring.lie_def + linearity of ι to LHS's ι(⁅a,b⁆) = ι(a*b) - ι(b*a).
  rw [Ring.lie_def, map_sub]
  -- The pre-Lie commutator identity at u, with `⁅a, b⁆` already unfolded
  -- to `a * b - b * a` (matching the LHS form after `Ring.lie_def`).
  have hAnti : preLieAction (R := R) a (preLieAction (R := R) b u)
             - preLieAction (R := R) b (preLieAction (R := R) a u)
             = -preLieAction (R := R) (a * b - b * a) u := by
    have h := preLieAction_lie_anti (R := R) a b
    have hu := congrArg
      (fun (D : Derivation R (SymmetricAlgebra R L) (SymmetricAlgebra R L)) => D u) h
    rw [Ring.lie_def] at hu
    rwa [Derivation.commutator_apply, Derivation.neg_apply] at hu
  -- All remaining differences are S(L)-polynomial in ι, mul, and L-action terms.
  -- Modulo S(L)'s CommRing structure + hAnti, the identity holds.
  -- Need coefficient -1 since LHS-RHS expands to -1·(hAnti.LHS - hAnti.RHS).
  linear_combination -hAnti

/-! ## §3: Lift to the universal enveloping algebra

`M : L →ₗ⁅R⁆ End(S(L))` is a Lie algebra morphism (`M_lie_hom`).
By the universal property of `UniversalEnvelopingAlgebra`, this extends
uniquely to an `R`-algebra morphism
`MAlgHom : U(L_Lie) →ₐ[R] End(S(L))`. -/

/-- `M` bundled as a Lie algebra morphism `L →ₗ⁅R⁆ End(S(L))`, where the
Lie structure on `End(S(L))` is the commutator under composition (via
`Module.End`'s associative ring structure). -/
noncomputable def MLieHom :
    L →ₗ⁅R⁆ Module.End R (SymmetricAlgebra R L) :=
  { M (R := R) with
    map_lie' := fun {a b} => M_lie_hom a b }

@[simp]
theorem MLieHom_apply (a : L) :
    MLieHom (R := R) a = M (R := R) a :=
  rfl

/-- The lift of `M` to the universal enveloping algebra of `L_Lie` via
`UniversalEnvelopingAlgebra.lift`. This is the algebra hom `M' : U(L_Lie)
→ₐ[R] End(S(L))` of Manchon (2009) Theorem 1.1. -/
noncomputable def MAlgHom :
    UniversalEnvelopingAlgebra R L →ₐ[R]
      Module.End R (SymmetricAlgebra R L) :=
  UniversalEnvelopingAlgebra.lift R MLieHom

@[simp]
theorem MAlgHom_ι (a : L) :
    MAlgHom (R := R) (UniversalEnvelopingAlgebra.ι R a) = M (R := R) a := by
  show UniversalEnvelopingAlgebra.lift R MLieHom _ = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-! ## §4: Manchon's η : U(L_Lie) →ₗ[R] S(L)

Define `η(u) := M'(u) (1)`. Manchon's key insight: `η` is a filtered
linear isomorphism (PBW-style argument), so the U(L_Lie) algebra
structure transports to S(L) via `η⁻¹`, giving the Guin-Oudom product
`★`. The iso theorem itself is C3 (R.4.3). -/

/-- **Manchon's η**: the linear map `U(L_Lie) →ₗ[R] S(L)` defined by
`η(u) := M'(u) (1)`. -/
noncomputable def η :
    UniversalEnvelopingAlgebra R L →ₗ[R] SymmetricAlgebra R L where
  toFun u := MAlgHom (R := R) u 1
  map_add' u v := by simp [LinearMap.add_apply]
  map_smul' r u := by simp [LinearMap.smul_apply]

@[simp]
theorem η_apply (u : UniversalEnvelopingAlgebra R L) :
    η (R := R) u = MAlgHom (R := R) u 1 :=
  rfl

@[simp]
theorem η_ι (a : L) :
    η (R := R) (UniversalEnvelopingAlgebra.ι R a) =
      SymmetricAlgebra.ι R L a := by
  rw [η_apply, MAlgHom_ι, M_apply_one]

@[simp]
theorem η_one : η (R := R) (1 : UniversalEnvelopingAlgebra R L) =
    (1 : SymmetricAlgebra R L) := by
  show MAlgHom (R := R) 1 1 = 1
  rw [map_one MAlgHom]
  exact Module.End.one_apply _
