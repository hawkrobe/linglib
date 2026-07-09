/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.PreLie.OudomGuinCircTotal
import Linglib.Core.Algebra.PreLie.GuinOudom
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra

set_option autoImplicit false

/-!
# The Oudom-Guin ○ operation on `SymmetricAlgebra R L`
[oudom-guin-2008]

For a pre-Lie algebra `L`, this file constructs the canonical extension
of the pre-Lie product `· : L × L → L` to a bilinear operation
`○ : S(L) × S(L) → S(L)` satisfying the three defining equations of
Oudom-Guin (2008) Proposition 2.7:

* `(i)`   `A ○ 1 = A`
* `(ii)`  `T ○ (B * X) = (T ○ B) ○ X − T ○ (B ○ X)`  (for `T ∈ L`)
* `(iii)` `(A * B) ○ C = (A ○ C₍₁₎) * (B ○ C₍₂₎)`  (where `Δ(C) = Σ C₍₁₎ ⊗ C₍₂₎`)

These equations uniquely determine `○`. From `○`, the Oudom-Guin product
`★ : S(L) × S(L) → S(L)`, `A ★ B := (A ○ B₍₁₎) * B₍₂₎` (Definition 2.9), is
associative (Lemma 2.10), making `(S(L), ★, Δ)` a Hopf algebra
isomorphic to `U(L_Lie)` (Theorem 2.12).

## Why this file (and not `GuinOudom.lean`)

The sibling file `GuinOudom.lean` follows the *Manchon route*: build
`η : U(L_Lie) → S(L)` directly via the `M` operator and obtain `★` as the
transferred UEA product. That route requires `η` to be an isomorphism
(classical PBW), which mathlib does not yet have, so the Manchon-route
`★` is currently blocked.

This file follows the *Oudom-Guin route*: define `○` and `★` directly on
`S(L)`, prove `★` associative via Lemma 2.10's 6-line algebraic chain
(using Prop 2.7's defining equations + cocommutativity of `Δ`). **No PBW
is required for associativity.**

## Status

**Q1b construction landed (2026-05-16).** `oudomGuinCirc` is built via
`SymmetricAlgebra.lift` into the convolution algebra
`WithConv (S(L) →ₗ[R] S(L))`. The convolution-algebra structure
(`LinearMap.convAlgebra` in `Mathlib.RingTheory.Coalgebra.Convolution`)
makes `S(L) →ₗ[R] S(L)` an `R`-algebra under the convolution product
`(f * g)(c) := μ ∘ (f ⊗ g) ∘ Δ(c)`, commutative because `S(L)` is
cocommutative (Q1a).

The generator-level input map `circGen : L →ₗ[R] WithConv (S(L) →ₗ[R] S(L))`
sends `T ↦ ι ∘ circByT_total T` (lifting the L-valued `circByT_total T`
from Q1b Step 1 to S(L)-valued via `ι : L → S(L)`). Q1b Step 1's
T-linearity of `circByT_total` (proven in
`Linglib.Core.Algebra.PreLie.OudomGuinCircTotal`) is what makes this
generator map linear.

Remaining for Q1c (uniqueness from defining equations) is deferred.

The interface (defining equations + Prop 2.8.v + Lemma 2.10) is stable
and consumers (`Q2/Q3/Q4/Q5/Q6` of the pivot) can build against it.

## References

* [oudom-guin-2008] — original construction, §2.
* [manchon-2011] — survey, Theorem 1.1 (Manchon route, alternative).
* [chapoton-livernet-2001] — free pre-Lie algebra = rooted trees.

## Convention

Right pre-Lie (`RightPreLieAlgebra` from Tapia 2025), matching
`GuinOudom.lean`. Pre-Lie product written as `*` on `L`. Oudom-Guin's
`○` notation is reserved for the extension to `S(L)`.
-/

namespace PreLie

namespace OudomGuinCirc

open WithConv
open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {L : Type*} [RightPreLieRing L] [RightPreLieAlgebra R L]

/-! ## §1: The `○` operation on `S(L) × S(L) → S(L)`

Oudom-Guin (2008) Proposition 2.7's defining equations characterize a
unique bilinear extension of the pre-Lie product `· : L × L → L` to an
operation `○ : S(L) × S(L) → S(L)`. The construction lifts via
`SymmetricAlgebra.lift` into the convolution algebra
`WithConv (S(L) →ₗ[R] S(L))` (commutative because `S(L)` is cocommutative).

The generator-level input is `circGen : L →ₗ[R] WithConv (S(L) →ₗ[R] S(L))`,
sending `T ↦ ι ∘ circByT_total T` — the L-valued Q1b Step 1 map `circByT_total T`
post-composed with `ι : L → S(L)` to land in `S(L)`, then opted into the
convolution multiplication.

`SymmetricAlgebra.lift R L circGen` extends `circGen` uniquely to an
R-algebra hom `circHom : S(L) →ₐ[R] WithConv (S(L) →ₗ[R] S(L))`. The
bilinear `oudomGuinCirc` is then `A ↦ B ↦ (circHom A).ofConv B`. -/

/-- Generator map: `T ↦ toConv (ι ∘ circByT_total T)`. Input to
    `SymmetricAlgebra.lift`. Linear in T by `circByT_total_T_add/smul`
    from `OudomGuinCircTotal`. -/
noncomputable def circGen :
    L →ₗ[R] WithConv (SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L) where
  toFun T := toConv
    ((SymmetricAlgebra.ι R L).comp (OudomGuinCircConstruct.circByT_total T))
  map_add' T₁ T₂ := by
    apply WithConv.ofConv_injective
    simp only [WithConv.ofConv_add,
               OudomGuinCircConstruct.circByT_total_T_add,
               LinearMap.comp_add]
  map_smul' r T := by
    apply WithConv.ofConv_injective
    simp only [WithConv.ofConv_smul,
               OudomGuinCircConstruct.circByT_total_T_smul,
               LinearMap.comp_smul, RingHom.id_apply]

/-- The lifted algebra hom `circHom : S(L) →ₐ[R] WithConv (S(L) →ₗ[R] S(L))`,
    extending `circGen` via the universal property of `SymmetricAlgebra`.

    By construction:
    - `circHom (ι T) = toConv (ι ∘ circByT_total T)` (`circGen T`).
    - `circHom (A * B) = circHom A * circHom B` (convolution).
    - `circHom 1 = 1` (= `toConv (Algebra.linearMap R S(L) ∘ counit)`).

    Convolution is commutative on `WithConv (C →ₗ[R] A)` when `C` is
    cocommutative and `A` is commutative — both hold for `S(L)`, allowing
    `SymmetricAlgebra.lift` to land here. -/
noncomputable def circHom :
    SymmetricAlgebra R L →ₐ[R]
      WithConv (SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L) :=
  SymmetricAlgebra.lift circGen

/-- The **Oudom-Guin ○ operation** on `S(L)`. Bilinear extension of the
    pre-Lie product `· : L × L → L` satisfying Prop 2.7's defining
    equations.

    Defined as `A ↦ B ↦ (circHom A).ofConv B`. The composition
    `ofConv ∘ₗ circHom.toLinearMap : S(L) →ₗ[R] (S(L) →ₗ[R] S(L))` is
    linear in `A` (since `circHom` is an algebra hom, hence linear) and
    linear in `B` (since each `(circHom A).ofConv` is a linear map). -/
noncomputable def oudomGuinCirc :
    SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L →ₗ[R]
      SymmetricAlgebra R L :=
  (WithConv.linearEquiv R (SymmetricAlgebra R L →ₗ[R]
    SymmetricAlgebra R L)).toLinearMap.comp circHom.toLinearMap

@[simp]
theorem circHom_ι (T : L) :
    circHom (R := R) (SymmetricAlgebra.ι R L T) = circGen T := by
  unfold circHom
  rw [SymmetricAlgebra.lift_ι_apply]

/-- Helper: `oudomGuinCirc A` is `(circHom A).ofConv` as a linear map. By
    definition of `oudomGuinCirc` as a composition. -/
theorem oudomGuinCirc_eq_ofConv (A : SymmetricAlgebra R L) :
    oudomGuinCirc (R := R) A = (circHom A).ofConv := rfl

/-- Notation for the Oudom-Guin ○ operation. -/
scoped infix:75 " ○ " => fun A B => oudomGuinCirc A B

/-! ## §2: Defining equations (Prop 2.7)

Oudom-Guin's Proposition 2.7 states that the three equations below
uniquely characterize `○`. We state each as a theorem witnessing that
the construction satisfies the defining equations. (The uniqueness
clause of Prop 2.7 is not yet formalized.) -/

/-- **Prop 2.7 (i)**: right unit. `A ○ 1 = A` for all `A ∈ S(L)`.

    Proof structure: induction on `A` via `SymmetricAlgebra.induction`.
    - `algebraMap r`: `(algebraMap r).ofConv 1 = r • algebraMap (counit 1) =
       r • algebraMap 1 = r • 1 = algebraMap r`.
    - `ι T`: `(circGen T).ofConv 1 = (ι ∘ circByT_total T) 1 = ι (circByT_total T 1) =
       ι T` by `circByT_total_one` (OG Def 2.4 base).
    - `mul A B`: `(circHom A * circHom B).ofConv 1 =
       mul' (map (.ofConv) (.ofConv) (comul 1)) =
       mul' (map (.ofConv) (.ofConv) (1 ⊗ 1)) = (.ofConv 1) * (.ofConv 1) =
       A * B` by IH.
    - `add`: linearity. -/
theorem circ_one_right (A : SymmetricAlgebra R L) :
    oudomGuinCirc (R := R) A 1 = A := by
  rw [oudomGuinCirc_eq_ofConv]
  induction A using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes]
    rw [LinearMap.convAlgebraMap_apply (R := R) (C := SymmetricAlgebra R L)
        (A := SymmetricAlgebra R L) r (1 : SymmetricAlgebra R L)]
    rw [Bialgebra.counit_one, map_one, ← Algebra.algebraMap_eq_smul_one]
  | ι T =>
    rw [circHom_ι]
    show ((SymmetricAlgebra.ι R L).comp
            (OudomGuinCircConstruct.circByT_total T)) 1 = SymmetricAlgebra.ι R L T
    rw [LinearMap.comp_apply, OudomGuinCircConstruct.circByT_total_one]
  | mul A B ih_A ih_B =>
    rw [map_mul, LinearMap.convMul_apply, Bialgebra.comul_one,
        Algebra.TensorProduct.one_def, TensorProduct.map_tmul, LinearMap.mul'_apply, ih_A, ih_B]
  | add A B ih_A ih_B =>
    rw [map_add, WithConv.ofConv_add, LinearMap.add_apply, ih_A, ih_B]

/-- **Prop 2.7 (iii)**: distributivity via `Δ`. `(A * B) ○ C =
    Σ (A ○ C₍₁₎) · (B ○ C₍₂₎)` (Sweedler-summed over the coproduct).

    This is the defining equation that extends `○` from `L × S(L)` to
    `S(L) × S(L)` on the left argument.

    Stated via `Coalgebra.comul` from Q1a's `Bialgebra` instance on
    `SymmetricAlgebra R L`. **By construction**: `circHom` is an algebra
    hom into the convolution algebra, so `circHom (A * B) = circHom A *
    circHom B` (convolution), which unfolds to exactly the RHS. -/
theorem circ_mul_distrib_via_comul (A B C : SymmetricAlgebra R L) :
    oudomGuinCirc (R := R) (A * B) C =
      (LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
        TensorProduct.map (oudomGuinCirc A) (oudomGuinCirc B))
        (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) C) := by
  simp only [oudomGuinCirc_eq_ofConv, LinearMap.coe_comp, Function.comp_apply]
  -- LHS = (circHom (A*B)).ofConv C = (circHom A * circHom B).ofConv C by map_mul,
  -- then unfolds to mul' (map ... (comul C)) by convMul_apply.
  rw [map_mul, LinearMap.convMul_apply]

/-! ## §3: Reduction to `L × L` pre-Lie product

When both arguments are images of `L` under `ι`, the OG `○` agrees with
the original pre-Lie product on `L`. -/

/-- `ι(T) ○ ι(X) = ι(T * X)` for `T, X ∈ L`. The pre-Lie product on `L`
    lifts to `S(L)` via `ι`.

    Direct: `oudomGuinCirc (ι T) (ι X) = (circGen T).ofConv (ι X) =
    ι (circByT_total T (ι X)) = ι (T * X)` by `circByT_total_ι` (degree-1
    base case of Q1b Step 1). -/
theorem circ_ι_ι (T X : L) :
    oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T)
        (SymmetricAlgebra.ι R L X) =
      SymmetricAlgebra.ι R L (T * X) := by
  rw [oudomGuinCirc_eq_ofConv, circHom_ι]
  show ((SymmetricAlgebra.ι R L).comp
          (OudomGuinCircConstruct.circByT_total T)) (SymmetricAlgebra.ι R L X) =
        SymmetricAlgebra.ι R L (T * X)
  rw [LinearMap.comp_apply, OudomGuinCircConstruct.circByT_total_ι]

/-- `1 ○ A = ε(A) · 1` for `A ∈ S(L)`. The counit map appears here.
    (Prop 2.8 (i) in Oudom-Guin.)

    Direct: `oudomGuinCirc 1 A = (circHom 1).ofConv A = (1 : WithConv).ofConv A
    = algebraMap R (S L) (counit A) = counit A • 1`. Then `counit = algebraMapInv`
    by `instBialgebra`'s construction. -/
theorem one_circ (A : SymmetricAlgebra R L) :
    oudomGuinCirc (R := R) (1 : SymmetricAlgebra R L) A =
      (SymmetricAlgebra.algebraMapInv (M := L) A) • (1 : SymmetricAlgebra R L) := by
  rw [oudomGuinCirc_eq_ofConv, map_one, LinearMap.convOne_apply]
  -- Goal: algebraMap R (S L) (counit A) = algebraMapInv A • 1
  -- counit = algebraMapInv by definitional unfolding of instBialgebra.
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

/-- Bialgebra counit-comul triangle for `SymmetricAlgebra`:
    `(mul' R R) ∘ (map ε ε) ∘ Δ = ε` as a linear map `S(L) → R`.
    Specialized: `mul' R R (map algebraMapInv algebraMapInv (comul B)) = algebraMapInv B`. -/
private theorem mul'_map_algebraMapInv_comul (B : SymmetricAlgebra R L) :
    LinearMap.mul' R R
        (TensorProduct.map
          (SymmetricAlgebra.algebraMapInv (R := R) (M := L)).toLinearMap
          (SymmetricAlgebra.algebraMapInv (R := R) (M := L)).toLinearMap
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B)) =
      SymmetricAlgebra.algebraMapInv (R := R) (M := L) B := by
  -- algebraMapInv.toLinearMap = Coalgebra.counit by the instBialgebra setup.
  have h_counit_eq : (SymmetricAlgebra.algebraMapInv (R := R) (M := L)).toLinearMap =
                      Coalgebra.counit (R := R) (A := SymmetricAlgebra R L) := rfl
  rw [h_counit_eq, ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply,
      Coalgebra.rTensor_counit_comul, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
      one_mul]
  rfl

/-- **Prop 2.8 (ii)**: counit and `○` commute. `ε(A ○ B) = ε(A) · ε(B)`.

    Strategy: prove the linear-map equality `ε ∘ₗ oudomGuinCirc A = ε A • ε`,
    then apply at B. Induction on A:
    - `algebraMap r`: `(algebraMap r in WithConv).ofConv B' = r • algebraMap (counit B')`;
      ε of both sides reduces via `algebraMap_leftInverse` + `counit = algebraMapInv`.
    - `ι T`: `(circGen T).ofConv B' = ι (circByT_total T B')`; ε kills ι.
    - `mul A₁ A₂`: push ε through `mul'` (`AlgHom.comp_mul'`), fuse nested
      `TensorProduct.map`, apply IH, close via `mul'_map_algebraMapInv_comul`.
    - `add`: linearity. -/
theorem counit_circ (A B : SymmetricAlgebra R L) :
    SymmetricAlgebra.algebraMapInv (M := L) (oudomGuinCirc (R := R) A B) =
      (SymmetricAlgebra.algebraMapInv (M := L) A) *
      (SymmetricAlgebra.algebraMapInv (M := L) B) := by
  -- Reduce to a linear-map equation pre-quantified over B.
  suffices h : (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap.comp
                  (oudomGuinCirc (R := R) A) =
               (SymmetricAlgebra.algebraMapInv (M := L) A) •
                 (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap by
    have := congrArg (fun (f : SymmetricAlgebra R L →ₗ[R] R) => f B) h
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
               smul_eq_mul] at this
    exact this
  induction A using SymmetricAlgebra.induction with
  | algebraMap r =>
    ext B'
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
               smul_eq_mul, oudomGuinCirc_eq_ofConv]
    rw [AlgHom.commutes, LinearMap.convAlgebraMap_apply, map_smul,
        AlgHom.commutes, SymmetricAlgebra.algebraMap_leftInverse, smul_eq_mul]
    -- Goal: r * (algebraMap R R) (counit B') = r * algebraMapInv B'
    -- (algebraMap R R) = id, counit = algebraMapInv (def from instBialgebra).
    rfl
  | ι T =>
    ext B'
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
               smul_eq_mul, oudomGuinCirc_eq_ofConv, circHom_ι,
               SymmetricAlgebra.algebraMapInv_ι, zero_mul]
    show SymmetricAlgebra.algebraMapInv ((SymmetricAlgebra.ι R L).comp
            (OudomGuinCircConstruct.circByT_total T) B') = 0
    rw [LinearMap.comp_apply, SymmetricAlgebra.algebraMapInv_ι]
  | mul A₁ A₂ ih₁ ih₂ =>
    ext B'
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    rw [oudomGuinCirc_eq_ofConv, map_mul, LinearMap.convMul_apply]
    -- Push algebraMapInv through mul' via AlgHom.comp_mul'
    have h_push := congrArg
        (fun (f : (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) →ₗ[R] R) =>
          f ((TensorProduct.map (circHom A₁).ofConv (circHom A₂).ofConv)
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B')))
        (AlgHom.comp_mul' (SymmetricAlgebra.algebraMapInv (M := L)))
    simp only [LinearMap.coe_comp, Function.comp_apply,
               AlgHom.toLinearMap_apply] at h_push
    rw [h_push]
    -- Fuse the two `TensorProduct.map` applications via `TensorProduct.map_comp`:
    -- args order in mathlib is (f₂, g₂, f₁, g₁): map (f₂∘f₁) (g₂∘g₁) = map f₂ g₂ ∘ map f₁ g₁.
    have h_fuse := congrArg
      (fun (f : (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) →ₗ[R] R ⊗[R] R) =>
        f (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B'))
      (TensorProduct.map_comp
        (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap
        (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap
        (circHom A₁).ofConv
        (circHom A₂).ofConv)
    simp only [LinearMap.coe_comp, Function.comp_apply] at h_fuse
    rw [← h_fuse]
    -- Apply ih₁ and ih₂ to substitute (algInv ∘ oudomGuinCirc Aᵢ) = algInv Aᵢ • algInv.
    -- First convert (circHom Aᵢ).ofConv back to oudomGuinCirc Aᵢ (they're defeq).
    rw [show (circHom A₁).ofConv = oudomGuinCirc (R := R) A₁ from rfl,
        show (circHom A₂).ofConv = oudomGuinCirc (R := R) A₂ from rfl,
        ih₁, ih₂]
    -- Now: mul' R R (map (algInv A₁ • algInv) (algInv A₂ • algInv) (comul B'))
    -- Pull out the scalars from the map, then from outside the application of mul'.
    rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul,
        LinearMap.smul_apply, map_smul, mul'_map_algebraMapInv_comul,
        ← map_mul, smul_eq_mul]
  | add A₁ A₂ ih₁ ih₂ =>
    ext B'
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
               smul_eq_mul]
    rw [oudomGuinCirc_eq_ofConv, map_add, WithConv.ofConv_add, LinearMap.add_apply,
        map_add, ← oudomGuinCirc_eq_ofConv, ← oudomGuinCirc_eq_ofConv, map_add]
    have h₁ := congrArg (fun (f : SymmetricAlgebra R L →ₗ[R] R) => f B') ih₁
    have h₂ := congrArg (fun (f : SymmetricAlgebra R L →ₗ[R] R) => f B') ih₂
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
               smul_eq_mul] at h₁ h₂
    rw [h₁, h₂, ← add_mul]

/-! ### §3.A: Prop 2.7 (ii) — the Def 2.4 recursion at the S(L) level

`circ_T_mul`: `ι T ○ (B · ι X) = (ι T ○ B) ○ ι X - ι T ○ (B ○ ι X)`.

Proof strategy: tprod-extensionality. The identity is linear in B; verify on the
spanning set of monomials `ι(a₀) · ... · ι(a_{m-1}) = algHomL (tprod_m a)` via
`circTMultilinear_succ` (Def 2.4 at the per-degree level). The crucial helper
is the derivation formula `oudomGuinCirc (algHomL z) (ι X) = derivative_TA z X`
expressed as a sum over positions, then matched with the multilinear
recursion. -/

/-- **Leibniz form** for `oudomGuinCirc · (ι X)` on a product:
    `(A * B) ○ ι X = (A ○ ι X) * B + A * (B ○ ι X)`.

    Follows from Prop 2.7 (iii) applied at `C = ι X`, where
    `comul (ι X) = ι X ⊗ 1 + 1 ⊗ ι X` (since `ι X` is primitive) and
    `_ ○ 1 = _` (circ_one_right). -/
theorem oudomGuinCirc_mul_ι (A B : SymmetricAlgebra R L) (X : L) :
    oudomGuinCirc (R := R) (A * B) (SymmetricAlgebra.ι R L X) =
      oudomGuinCirc A (SymmetricAlgebra.ι R L X) * B +
      A * oudomGuinCirc B (SymmetricAlgebra.ι R L X) := by
  rw [circ_mul_distrib_via_comul]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [SymmetricAlgebra.comul_ι]
  simp only [map_add, TensorProduct.map_tmul, LinearMap.mul'_apply,
             circ_one_right]

/-- **Derivation formula** for monomials: for a tprod `z = tprod_m a` in TA, the
    image `B = algHomL z = ι(a₀) · ... · ι(a_{m-1}) ∈ S(L)` satisfies
    `oudomGuinCirc B (ι X) = Σᵢ algHomL (tprod_m (update a i (a i * X)))`.

    Proven by induction on `m`; base case uses `one_circ`, step uses Prop 2.7 (iii)
    + `comul_ι` + `circ_one_right` + `circ_ι_ι`.

    Provides the Leibniz expansion of `(∏ ι(a i)) ○ ι X`; consumed downstream by
    `OudomGuinBridge`. -/
theorem oudomGuinCirc_algHomL_tprod_ι (X : L) :
    ∀ (m : ℕ) (a : Fin m → L),
      oudomGuinCirc (R := R)
          (OudomGuinCircConstruct.algHomL
            (TensorAlgebra.tprod R L m a))
          (SymmetricAlgebra.ι R L X) =
        ∑ i : Fin m,
          OudomGuinCircConstruct.algHomL
            (TensorAlgebra.tprod R L m (Function.update a i (a i * X))) := by
  intro m
  induction m with
  | zero =>
    intro a
    -- tprod_0 a = 1 (empty product); algHomL 1 = 1; oudomGuinCirc 1 (ι X) = 0.
    have h_tprod0 : TensorAlgebra.tprod R L 0 a = 1 := by
      rw [TensorAlgebra.tprod_apply]
      simp [List.ofFn_zero]
    rw [h_tprod0, show OudomGuinCircConstruct.algHomL (R := R) (L := L)
                        (1 : TensorAlgebra R L) = (1 : SymmetricAlgebra R L) from
          map_one (SymmetricAlgebra.algHom R L), one_circ,
        SymmetricAlgebra.algebraMapInv_ι, zero_smul, Fin.sum_univ_zero]
  | succ m ih =>
    intro a
    -- Decompose a = Fin.snoc (Fin.init a) (a (Fin.last m))
    have h_a_eq : a = Fin.snoc (Fin.init a) (a (Fin.last m)) := (Fin.snoc_init_self a).symm
    -- tprod_{m+1} (snoc a' Y) = tprod_m a' * ι Y in TA
    have h_tprod_succ :
        TensorAlgebra.tprod R L (m + 1) a =
        TensorAlgebra.tprod R L m (Fin.init a) * TensorAlgebra.ι R (a (Fin.last m)) := by
      conv_lhs => rw [h_a_eq]
      rw [Fin.snoc_eq_append,
          OudomGuinCircConstruct.ι_eq_tprod_one,
          ← OudomGuinCircConstruct.tprod_mul_tprod]
      congr 1
    -- algHomL of LHS = algHomL of RHS (algHomL is alg hom)
    have h_algHomL_split :
        OudomGuinCircConstruct.algHomL (R := R) (L := L)
            (TensorAlgebra.tprod R L (m + 1) a) =
          OudomGuinCircConstruct.algHomL (TensorAlgebra.tprod R L m (Fin.init a)) *
            SymmetricAlgebra.ι R L (a (Fin.last m)) := by
      rw [h_tprod_succ]
      show (SymmetricAlgebra.algHom R L) _ = _
      rw [map_mul]; rfl
    rw [h_algHomL_split]
    -- Apply Leibniz form
    rw [oudomGuinCirc_mul_ι]
    -- LHS = (B' ○ ι X) * ι Y + B' * (ι Y ○ ι X) where B' = algHomL (tprod_m (Fin.init a)), Y = a (last m)
    rw [circ_ι_ι]
    -- = (B' ○ ι X) * ι Y + B' * ι (Y * X)
    -- Apply IH to B' ○ ι X
    rw [ih (Fin.init a)]
    -- = Σⱼ : Fin m algHomL (tprod_m (update (Fin.init a) j (...))) * ι Y + B' * ι (Y * X)
    -- Distribute multiplication on the left: (Σⱼ xⱼ) * Y = Σⱼ (xⱼ * Y)
    rw [Finset.sum_mul]
    -- Convert each xⱼ * ι Y to algHomL (tprod_{m+1} (snoc (update (Fin.init a) j (...)) Y))
    -- Tuple equality used in both the sum-side and last-term: snoc-update conversion.
    have h_snoc_init : Fin.snoc (Fin.init a) (a (Fin.last m)) = a := Fin.snoc_init_self a
    have h_tuple_j : ∀ (j : Fin m),
        Fin.snoc (Function.update (Fin.init a) j (Fin.init a j * X)) (a (Fin.last m)) =
          Function.update a (Fin.castSucc j) (a (Fin.castSucc j) * X) := by
      intro j
      rw [Fin.snoc_update, h_snoc_init]
      -- Fin.init a j = a (Fin.castSucc j) by definition.
      rfl
    have h_tuple_last :
        Fin.snoc (Fin.init a) (a (Fin.last m) * X) =
          Function.update a (Fin.last m) (a (Fin.last m) * X) := by
      rw [← Fin.update_snoc_last, h_snoc_init]
    -- Convert each term in the sum.
    have h_sum_eq :
        (∑ j : Fin m,
            OudomGuinCircConstruct.algHomL
              (TensorAlgebra.tprod R L m (Function.update (Fin.init a) j (Fin.init a j * X))) *
            SymmetricAlgebra.ι R L (a (Fin.last m))) =
        ∑ j : Fin m,
          OudomGuinCircConstruct.algHomL
            (TensorAlgebra.tprod R L (m + 1)
              (Function.update a (Fin.castSucc j) (a (Fin.castSucc j) * X))) := by
      apply Finset.sum_congr rfl
      intro j _
      -- algHomL (tprod_m ...) * ι Y = algHomL (tprod_m ... * ι Y) (via algHom mul + algHomL = .toLinearMap)
      have h_mul : ∀ (z : TensorAlgebra R L) (Y : L),
          OudomGuinCircConstruct.algHomL (R := R) (L := L) z *
            SymmetricAlgebra.ι R L Y =
          OudomGuinCircConstruct.algHomL (z * TensorAlgebra.ι R Y) := by
        intro z Y
        show (SymmetricAlgebra.algHom R L) z * (SymmetricAlgebra.algHom R L) (TensorAlgebra.ι R Y) =
              OudomGuinCircConstruct.algHomL (z * TensorAlgebra.ι R Y)
        rw [← map_mul]; rfl
      rw [h_mul, OudomGuinCircConstruct.ι_eq_tprod_one,
          OudomGuinCircConstruct.tprod_mul_tprod, Fin.append_right_eq_snoc, h_tuple_j]
    rw [h_sum_eq, Fin.sum_univ_castSucc]
    congr 1
    -- Last term: algHomL (tprod_m (Fin.init a)) * ι (a (Fin.last m) * X) =
    --            algHomL (tprod_{m+1} (update a (Fin.last m) (a (Fin.last m) * X)))
    have h_mul' : ∀ (z : TensorAlgebra R L) (Y : L),
        OudomGuinCircConstruct.algHomL (R := R) (L := L) z *
          SymmetricAlgebra.ι R L Y =
        OudomGuinCircConstruct.algHomL (z * TensorAlgebra.ι R Y) := by
      intro z Y
      show (SymmetricAlgebra.algHom R L) z * (SymmetricAlgebra.algHom R L) (TensorAlgebra.ι R Y) =
            OudomGuinCircConstruct.algHomL (z * TensorAlgebra.ι R Y)
      rw [← map_mul]; rfl
    rw [h_mul', OudomGuinCircConstruct.ι_eq_tprod_one,
        OudomGuinCircConstruct.tprod_mul_tprod, Fin.append_right_eq_snoc, h_tuple_last]

/-- **Substrate helper**: TA-level form of Prop 2.7 (ii). For tprods,
    `circByT_total T (algHomL z * ι X) = (circByT_total T (algHomL z)) * X -
    Σᵢ circByT_total T (algHomL (tprod_m (update a i (a i * X))))`. The Σᵢ on the
    right equals `circByT_total T (oudomGuinCirc B (ι X))` after applying
    `oudomGuinCirc_algHomL_tprod_ι`. -/
private theorem circByT_total_algHomL_tprod_mul_ι (T : L) (X : L) (m : ℕ) (a : Fin m → L) :
    OudomGuinCircConstruct.circByT_total T
        ((OudomGuinCircConstruct.algHomL
            (TensorAlgebra.tprod R L m a)) *
          SymmetricAlgebra.ι R L X) =
      (OudomGuinCircConstruct.circByT_total T
          (OudomGuinCircConstruct.algHomL (TensorAlgebra.tprod R L m a))) * X -
        ∑ i : Fin m,
          OudomGuinCircConstruct.circByT_total T
            (OudomGuinCircConstruct.algHomL
              (TensorAlgebra.tprod R L m (Function.update a i (a i * X)))) := by
  -- Step 1: ι X = algHomL (TensorAlgebra.ι R X); algHomL is alg hom.
  have h_ι_eq : SymmetricAlgebra.ι R L X =
                OudomGuinCircConstruct.algHomL (R := R) (L := L)
                  (TensorAlgebra.ι R X) := rfl
  have h_mul : (OudomGuinCircConstruct.algHomL
                  (TensorAlgebra.tprod R L m a)) * SymmetricAlgebra.ι R L X =
               OudomGuinCircConstruct.algHomL
                 (TensorAlgebra.tprod R L m a * TensorAlgebra.ι R X) := by
    rw [h_ι_eq]
    show (SymmetricAlgebra.algHom R L) _ * (SymmetricAlgebra.algHom R L) _ = _
    rw [← map_mul]; rfl
  rw [h_mul]
  -- Step 2: tprod_m a * ι X = tprod_{m+1} (Fin.append a (fun _ => X))
  rw [OudomGuinCircConstruct.ι_eq_tprod_one X,
      OudomGuinCircConstruct.tprod_mul_tprod]
  -- Step 3: apply circByT_total_comp_algHomL to convert circByT_total of algHomL into circTTensor.
  have h_apply_total :=
    congrArg
      (fun (f : TensorAlgebra R L →ₗ[R] L) =>
        f (TensorAlgebra.tprod R L (m + 1)
          (Fin.append a (fun _ : Fin 1 => X))))
      (OudomGuinCircConstruct.circByT_total_comp_algHomL (R := R) T)
  simp only [LinearMap.comp_apply] at h_apply_total
  rw [h_apply_total]
  -- Now LHS: circTTensor T (tprod_{m+1} (Fin.append a (fun _ => X)))
  rw [OudomGuinCircConstruct.circTTensor_tprod]
  -- Now LHS: circTMultilinear T (m+1) (Fin.append a (fun _ => X))
  rw [OudomGuinCircConstruct.circTMultilinear_succ]
  -- Fin.init of append with one element = a; last = X.
  have h_init : Fin.init (Fin.append a (fun _ : Fin 1 => X)) = a := by
    rw [Fin.append_right_eq_snoc, Fin.init_snoc]
  have h_last : (Fin.append a (fun _ : Fin 1 => X)) (Fin.last m) = X := by
    rw [Fin.append_right_eq_snoc, Fin.snoc_last]
  rw [h_init, h_last]
  -- Now LHS: circTMultilinear T m a * X - Σᵢ circTMultilinear T m (update a i (a i * X))
  -- For RHS conversion: each circTMultilinear T m a' = circByT_total T (algHomL (tprod_m a'))
  have h_RHS_first :
      OudomGuinCircConstruct.circByT_total T
          (OudomGuinCircConstruct.algHomL (TensorAlgebra.tprod R L m a)) =
        OudomGuinCircConstruct.circTMultilinear R T m a := by
    have h := congrArg
      (fun (f : TensorAlgebra R L →ₗ[R] L) => f (TensorAlgebra.tprod R L m a))
      (OudomGuinCircConstruct.circByT_total_comp_algHomL (R := R) T)
    simp only [LinearMap.comp_apply] at h
    rw [h, OudomGuinCircConstruct.circTTensor_tprod]
  rw [h_RHS_first]
  -- Each summand on RHS: similar conversion.
  have h_RHS_sum :
      (∑ i : Fin m,
          OudomGuinCircConstruct.circByT_total T
            (OudomGuinCircConstruct.algHomL
              (TensorAlgebra.tprod R L m (Function.update a i (a i * X))))) =
        (∑ i : Fin m, OudomGuinCircConstruct.circTMultilinear R T m
            (Function.update a i (a i * X))) := by
    apply Finset.sum_congr rfl
    intro i _
    have h := congrArg
      (fun (f : TensorAlgebra R L →ₗ[R] L) =>
        f (TensorAlgebra.tprod R L m (Function.update a i (a i * X))))
      (OudomGuinCircConstruct.circByT_total_comp_algHomL (R := R) T)
    simp only [LinearMap.comp_apply] at h
    rw [h, OudomGuinCircConstruct.circTTensor_tprod]
  rw [h_RHS_sum]

/-- **Prop 2.7 (ii)**: recursive equation for `T ∈ L` on the left.
    `T ○ (B · X) = (T ○ B) ○ X − T ○ (B ○ X)` for `T, X ∈ L`, `B ∈ S(L)`.

    This is the Def 2.4 recursion lifted to the symmetric-algebra setting.

    Proof: tprod-extensionality. Define the linear map
    `Δ_X(B) := LHS(B) - RHS(B) : S(L) →ₗ S(L)`. To show `Δ_X = 0`, it suffices to
    show `Δ_X ∘ₗ algHomL = 0 : TA →ₗ S(L)`. Via `TA_linearMap_ext_tprod`, this
    reduces to checking on tprods, which follows from
    `circByT_total_algHomL_tprod_mul_ι` + `oudomGuinCirc_algHomL_tprod_ι` +
    `circ_ι_ι` (collapsing the algInv-of-multilinear into `T*X`-form). -/
theorem circ_T_mul (T : L) (B : SymmetricAlgebra R L) (X : L) :
    oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T)
        (B * SymmetricAlgebra.ι R L X) =
      oudomGuinCirc (R := R)
          (oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T) B)
          (SymmetricAlgebra.ι R L X) -
      oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T)
          (oudomGuinCirc (R := R) B (SymmetricAlgebra.ι R L X)) := by
  -- Reduce via algHomL surjectivity to a statement about z ∈ TA.
  obtain ⟨z, hz⟩ := OudomGuinCircConstruct.algHomL_surjective B
  subst hz
  -- Define the three pieces as linear maps in z, then prove their identity via
  -- TA_linearMap_ext_tprod (check on tprods).
  -- For LinearMap construction: each side is a linear endomap composed with algHomL.
  -- Use `LinearMap.flip oudomGuinCirc (ι X) : S(L) →ₗ[R] S(L)`, `B ↦ oudomGuinCirc B (ι X)`.
  set f_LHS : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
    (oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T)).comp
      ((LinearMap.mulRight R (SymmetricAlgebra.ι R L X)).comp
        OudomGuinCircConstruct.algHomL) with hf_LHS
  set f_RHS1 : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
    ((LinearMap.flip (oudomGuinCirc (R := R))) (SymmetricAlgebra.ι R L X)).comp
      ((oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T)).comp
        OudomGuinCircConstruct.algHomL) with hf_RHS1
  set f_RHS2 : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
    (oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T)).comp
      (((LinearMap.flip (oudomGuinCirc (R := R))) (SymmetricAlgebra.ι R L X)).comp
        OudomGuinCircConstruct.algHomL) with hf_RHS2
  -- Identity to show: f_LHS = f_RHS1 - f_RHS2 (as linear maps TA →ₗ S(L)).
  suffices h_LM : f_LHS = f_RHS1 - f_RHS2 by
    have := congrArg (fun (f : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L) => f z) h_LM
    simp only [hf_LHS, hf_RHS1, hf_RHS2,
               LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.mulRight_apply,
               LinearMap.flip_apply] at this
    exact this
  -- Apply TA_linearMap_ext_tprod.
  apply OudomGuinCircConstruct.TA_linearMap_ext_tprod
  intro m a
  -- Compute f_LHS, f_RHS1, f_RHS2 at tprod_m a.
  simp only [hf_LHS, hf_RHS1, hf_RHS2,
             LinearMap.comp_apply, LinearMap.sub_apply,
             LinearMap.mulRight_apply, LinearMap.flip_apply]
  -- LHS: oudomGuinCirc (ι T) (algHomL (tprod_m a) * ι X)
  -- RHS-1: oudomGuinCirc (oudomGuinCirc (ι T) (algHomL (tprod_m a))) (ι X)
  -- RHS-2: oudomGuinCirc (ι T) (oudomGuinCirc (algHomL (tprod_m a)) (ι X))
  -- All three reduce to ι expressions over L.
  -- For each, use oudomGuinCirc (ι Y) B = ι (circByT_total Y B):
  have h_circ_ιT : ∀ B : SymmetricAlgebra R L,
      oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T) B =
        SymmetricAlgebra.ι R L (OudomGuinCircConstruct.circByT_total T B) := by
    intro B
    rw [oudomGuinCirc_eq_ofConv, circHom_ι]
    rfl
  -- LHS: oudomGuinCirc (ι T) (algHomL (tprod_m a) * ι X)
  --    = ι (circByT_total T (algHomL (tprod_m a) * ι X))  [h_circ_ιT]
  --    = ι (circByT_total T (algHomL (tprod_m a)) * X
  --         - Σᵢ circByT_total T (algHomL (tprod_m (update a i (a i*X)))))  [helper]
  --    = ι (circByT_total T (algHomL (tprod_m a)) * X)
  --      - Σᵢ ι (circByT_total T (algHomL (tprod_m (update a i (a i*X)))))  [map_sub + map_sum]
  rw [h_circ_ιT (OudomGuinCircConstruct.algHomL _ * _),
      circByT_total_algHomL_tprod_mul_ι, map_sub, map_sum]
  -- RHS-1: oudomGuinCirc (oudomGuinCirc (ι T) (algHomL (tprod_m a))) (ι X)
  --       = oudomGuinCirc (ι (circByT_total T (algHomL (tprod_m a)))) (ι X)  [h_circ_ιT]
  --       = ι (circByT_total T (algHomL (tprod_m a)) * X)  [circ_ι_ι]
  rw [h_circ_ιT (OudomGuinCircConstruct.algHomL _), circ_ι_ι]
  -- RHS-2: oudomGuinCirc (ι T) (oudomGuinCirc (algHomL (tprod_m a)) (ι X))
  --       = ι (circByT_total T (oudomGuinCirc (algHomL (tprod_m a)) (ι X)))  [h_circ_ιT]
  --       = ι (circByT_total T (Σᵢ algHomL (...)))  [oudomGuinCirc_algHomL_tprod_ι]
  --       = ι (Σᵢ circByT_total T (algHomL (...)))  [linearity of circByT_total T]
  --       = Σᵢ ι (circByT_total T (algHomL (...)))  [map_sum]
  rw [h_circ_ιT (oudomGuinCirc _ _),
      oudomGuinCirc_algHomL_tprod_ι, map_sum, map_sum]

/-! ### §3.B: Prop 2.8 (iii) — `Δ` commutes with `○`

`Δ(A ○ B) = Σ (A₍₁₎ ○ B₍₁₎) ⊗ (A₍₂₎ ○ B₍₂₎)`, Sweedler-summed over both
coproducts. Stated and proved as a pointwise identity, with the
multi-Sweedler reshuffling encoded by `TensorProduct.tensorTensorTensorComm`
(`TTTC`): `(M ⊗ N) ⊗ (P ⊗ Q) → (M ⊗ P) ⊗ (N ⊗ Q)`, applied to
`Δ A ⊗ Δ B ∈ (S ⊗ S) ⊗ (S ⊗ S)`.

Proof structure: induction on `A` via `SymmetricAlgebra.induction`. The
`mul` case requires the iterated-coproduct invariance
`TTTC ∘ (Δ ⊗ Δ) ∘ Δ = (Δ ⊗ Δ) ∘ Δ`, which follows from cocommutativity
of `Δ` (via `Coalgebra.IsCocomm`). We factor this into the auxiliary
lemma `comul_squared_TTTC_eq`. -/

/-- **Auxiliary**: iterated coproduct on `S(L)` is invariant under the
    inner `tensorTensorTensorComm` reshuffle. By cocommutativity of `Δ`:
    `TTTC ∘ (Δ ⊗ Δ) ∘ Δ = (Δ ⊗ Δ) ∘ Δ` as maps `S(L) → S(L)^{⊗4}`.

    Proof: lift to `Algebra.TensorProduct.tensorTensorTensorComm` (alg
    equiv) composed with `Algebra.TensorProduct.map comulAlgHom comulAlgHom`
    composed with `comulAlgHom`. Both sides are algebra homs `S(L) →ₐ
    S(L)^{⊗4}`; by `SymmetricAlgebra.algHom_ext`, agree iff agree on
    generators `ι T`. Check on `ι T` (primitive): the 4-term sum of
    single-position primitives is symmetric under position-2-3 swap,
    closed by `abel`. -/
private theorem comul_squared_TTTC_eq :
    (TensorProduct.tensorTensorTensorComm R
        (SymmetricAlgebra R L) (SymmetricAlgebra R L)
        (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
      ((TensorProduct.map
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))).comp
        (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))) =
    (TensorProduct.map
        (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
        (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))).comp
      (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)) := by
  -- Reduce to pointwise equality via `ext`, then induct on B.
  -- Goal becomes: for all B, TTTC ((TP.map Δ Δ)(Δ B)) = (TP.map Δ Δ)(Δ B).
  -- The pointwise form lets us use Bialgebra.comulAlgHom's `map_mul` for the mul case.
  ext B
  -- Switch to alg hom forms throughout so we can use `map_mul`, `map_add`, etc.
  show (Algebra.TensorProduct.tensorTensorTensorComm R R R R _ _ _ _)
          ((Algebra.TensorProduct.map
              (Bialgebra.comulAlgHom R (SymmetricAlgebra R L))
              (Bialgebra.comulAlgHom R (SymmetricAlgebra R L)))
            ((Bialgebra.comulAlgHom R (SymmetricAlgebra R L)) B)) =
        (Algebra.TensorProduct.map
            (Bialgebra.comulAlgHom R (SymmetricAlgebra R L))
            (Bialgebra.comulAlgHom R (SymmetricAlgebra R L)))
          ((Bialgebra.comulAlgHom R (SymmetricAlgebra R L)) B)
  induction B using SymmetricAlgebra.induction with
  | algebraMap r =>
    -- All three alg homs/equivs commute with algebraMap.
    simp only [AlgHom.commutes, AlgEquiv.commutes]
  | ι T =>
    -- Δ(ι T) = ι T ⊗ 1 + 1 ⊗ ι T (primitive). Expand fully and apply TTTC
    -- pointwise. The resulting 4 single-position-ι-T terms are TTTC-permuted
    -- (position 2 ↔ 3 swap); abel closes.
    have h_cm_ι : (Bialgebra.comulAlgHom R (SymmetricAlgebra R L))
                    (SymmetricAlgebra.ι R L T) =
                  SymmetricAlgebra.ι R L T ⊗ₜ[R] 1 +
                    1 ⊗ₜ[R] SymmetricAlgebra.ι R L T :=
      SymmetricAlgebra.comul_ι R L T
    simp only [h_cm_ι, map_add, Algebra.TensorProduct.map_tmul, map_one,
               Algebra.TensorProduct.one_def,
               TensorProduct.add_tmul, TensorProduct.tmul_add,
               Algebra.TensorProduct.tensorTensorTensorComm_tmul]
    abel
  | mul A₁ A₂ ih₁ ih₂ =>
    -- Δ(A₁ · A₂) = Δ A₁ · Δ A₂ via map_mul on cm.
    -- (TP.map cm cm) preserves mul via map_mul.
    -- TTTC preserves mul via map_mul.
    -- Apply IH.
    rw [map_mul, map_mul, map_mul, ih₁, ih₂]
  | add A₁ A₂ ih₁ ih₂ =>
    rw [map_add, map_add, map_add, ih₁, ih₂]

/-- **Helper**: the cocomm-step factorization. The unified RHS structure
    `(TP.map μ μ)(TTTC((a ⊗ b) ⊗ x)) = TP.map (○a) (○b) x` follows by
    pure-tensor extension + `tensorTensorTensorComm_tmul`. -/
private lemma map_uncurry_TTTC_pure (a b : SymmetricAlgebra R L)
    (x : SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) :
    (TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                       (TensorProduct.lift (oudomGuinCirc (R := R))))
      ((TensorProduct.tensorTensorTensorComm R
          (SymmetricAlgebra R L) (SymmetricAlgebra R L)
          (SymmetricAlgebra R L) (SymmetricAlgebra R L))
        ((a ⊗ₜ[R] b) ⊗ₜ[R] x)) =
    (TensorProduct.map (oudomGuinCirc (R := R) a) (oudomGuinCirc (R := R) b)) x := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [TensorProduct.tmul_zero, map_zero]
  | tmul p q =>
    rw [TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
        TensorProduct.lift.tmul, TensorProduct.lift.tmul, TensorProduct.map_tmul]
  | add x y ihx ihy =>
    rw [TensorProduct.tmul_add, map_add, map_add, ihx, ihy, map_add]

/-- **Helper**: `(○1)` as a linear map equals `algebraMap R S ∘ counit`.

    Combines `one_circ` (`1 ○ B = ε(B) • 1`) and `algebraMap_eq_smul_one`. -/
private lemma circ_one_eq_algebraMap_comp_counit :
    oudomGuinCirc (R := R) (1 : SymmetricAlgebra R L) =
      (Algebra.linearMap R (SymmetricAlgebra R L)).comp
        (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap := by
  ext B
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
             Algebra.linearMap_apply]
  rw [one_circ, Algebra.algebraMap_eq_smul_one]

/-- **Helper**: `TP.map (○a) (○1) (Δ B) = (a ○ B) ⊗ 1`.

    Proof: factor `(○1) = algebraMap ∘ counit`, then use the counit triangle
    `(id ⊗ counit)(Δ B) = B ⊗ 1` (`Coalgebra.lTensor_counit_comul`) and
    `algebraMap 1 = 1`. -/
private lemma map_circ_a_circ_one_comul (a B : SymmetricAlgebra R L) :
    (TensorProduct.map (oudomGuinCirc (R := R) a)
                       (oudomGuinCirc (R := R) (1 : SymmetricAlgebra R L)))
      (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B) =
    (oudomGuinCirc (R := R) a B) ⊗ₜ[R] (1 : SymmetricAlgebra R L) := by
  rw [circ_one_eq_algebraMap_comp_counit,
      show TensorProduct.map (oudomGuinCirc (R := R) a)
            ((Algebra.linearMap R (SymmetricAlgebra R L)).comp
              (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap) =
        (TensorProduct.map (oudomGuinCirc (R := R) a)
            (Algebra.linearMap R (SymmetricAlgebra R L))).comp
          (TensorProduct.map (LinearMap.id : SymmetricAlgebra R L →ₗ[R] _)
            (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap) from by
        rw [← TensorProduct.map_comp, LinearMap.comp_id]]
  rw [LinearMap.comp_apply]
  -- TP.map id algebraMapInv (comul B) = B ⊗ 1 via Coalgebra.lTensor_counit_comul.
  rw [show (TensorProduct.map (LinearMap.id : SymmetricAlgebra R L →ₗ[R] _)
            (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap)
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B) =
        B ⊗ₜ[R] (1 : R) from
      Coalgebra.lTensor_counit_comul B]
  rw [TensorProduct.map_tmul, Algebra.linearMap_apply, map_one]

/-- **Helper**: `TP.map (○1) (○b) (Δ B) = 1 ⊗ (b ○ B)`.

    Mirror of `map_circ_a_circ_one_comul` using the right counit triangle
    (`rTensor_counit_comul`). -/
private lemma map_circ_one_circ_b_comul (b B : SymmetricAlgebra R L) :
    (TensorProduct.map (oudomGuinCirc (R := R) (1 : SymmetricAlgebra R L))
                       (oudomGuinCirc (R := R) b))
      (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B) =
    (1 : SymmetricAlgebra R L) ⊗ₜ[R] (oudomGuinCirc (R := R) b B) := by
  rw [circ_one_eq_algebraMap_comp_counit,
      show TensorProduct.map
            ((Algebra.linearMap R (SymmetricAlgebra R L)).comp
              (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap)
            (oudomGuinCirc (R := R) b) =
        (TensorProduct.map (Algebra.linearMap R (SymmetricAlgebra R L))
            (oudomGuinCirc (R := R) b)).comp
          (TensorProduct.map (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap
            (LinearMap.id : SymmetricAlgebra R L →ₗ[R] _)) from by
        rw [← TensorProduct.map_comp, LinearMap.comp_id]]
  rw [LinearMap.comp_apply]
  rw [show (TensorProduct.map (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap
            (LinearMap.id : SymmetricAlgebra R L →ₗ[R] _))
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B) =
        (1 : R) ⊗ₜ[R] B from
      Coalgebra.rTensor_counit_comul B]
  rw [TensorProduct.map_tmul, Algebra.linearMap_apply, map_one]

/-- **Pure-tensor M-form helper.** For `a₁, a₂, c₁, c₂ ∈ S(L)` and arbitrary
    `p, q ∈ S(L) ⊗ S(L)`:

    ```
    mul'_{S⊗S}((TP.map (M (a₁⊗a₂)) (M (c₁⊗c₂))) (TTTC (p ⊗ q)))
      = mul' (TP.map (○a₁) (○c₁) p) ⊗ mul' (TP.map (○a₂) (○c₂) q)
    ```

    where `M u Y := (TP.map ○_lift ○_lift) (TTTC (u ⊗ Y))`.

    Proof: bilinear in `p, q`. By `TensorProduct.induction_on` on each (with
    `generalizing q` for the outer one), reduce to pure tensors. Pure-tensor
    case unfolds by `simp` with `tensorTensorTensorComm_tmul`, `map_tmul`,
    `lift.tmul`, `mul'_apply`. -/
private lemma mul_TP_TTTC_circ_pure_u_v
    (a₁ a₂ c₁ c₂ : SymmetricAlgebra R L)
    (p q : SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) :
    LinearMap.mul' R (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
      ((TensorProduct.map
          ((TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                              (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
            ((TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
              ((TensorProduct.mk R
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L))
                (a₁ ⊗ₜ[R] a₂))))
          ((TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                              (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
            ((TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
              ((TensorProduct.mk R
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L))
                (c₁ ⊗ₜ[R] c₂)))))
        ((TensorProduct.tensorTensorTensorComm R
            (SymmetricAlgebra R L) (SymmetricAlgebra R L)
            (SymmetricAlgebra R L) (SymmetricAlgebra R L)) (p ⊗ₜ[R] q))) =
    (LinearMap.mul' R (SymmetricAlgebra R L)
        ((TensorProduct.map (oudomGuinCirc (R := R) a₁)
                            (oudomGuinCirc (R := R) c₁)) p)) ⊗ₜ[R]
    (LinearMap.mul' R (SymmetricAlgebra R L)
        ((TensorProduct.map (oudomGuinCirc (R := R) a₂)
                            (oudomGuinCirc (R := R) c₂)) q)) := by
  induction p using TensorProduct.induction_on generalizing q with
  | zero =>
    simp only [TensorProduct.zero_tmul, map_zero, TensorProduct.zero_tmul]
  | tmul x y =>
    induction q using TensorProduct.induction_on with
    | zero =>
      simp only [TensorProduct.tmul_zero, map_zero, TensorProduct.tmul_zero]
    | tmul x' y' =>
      simp only [LinearMap.comp_apply, TensorProduct.mk_apply,
                 LinearEquiv.coe_toLinearMap,
                 TensorProduct.tensorTensorTensorComm_tmul,
                 TensorProduct.map_tmul, TensorProduct.lift.tmul,
                 LinearMap.mul'_apply, Algebra.TensorProduct.tmul_mul_tmul]
    | add q1 q2 ihq1 ihq2 =>
      simp only [TensorProduct.tmul_add, map_add, ihq1, ihq2,
                 TensorProduct.tmul_add]
  | add p1 p2 ihp1 ihp2 =>
    simp only [TensorProduct.add_tmul, map_add, ihp1 q, ihp2 q,
               TensorProduct.add_tmul]

/-- **G-form post-factoring/post-cocomm identity.** For arbitrary `u, v, y ∈ S⊗S`:
    ```
    mul'_{S⊗S}((TP.map (G u) (G v)) (TTTC ((TP.map cm cm) y)))
      = (TP.map ○ ○) (TTTC ((u · v) ⊗ y))
    ```
    where `G u Y := (TP.map ○ ○)(TTTC(u ⊗ Y))`.

    This is the bilinear identity that closes `comul_circ_mul_cocomm_aux` once
    `TP.map_comp` has factored F_i = G_{cm A_i} ∘ cm and cocomm has inserted
    a TTTC at Δ²B. Specialized at `u = cm A₁, v = cm A₂, y = cm B`.

    Proof: nested `TensorProduct.induction_on` on `u, v, y`. Pure case `u =
    a₁⊗a₂, v = c₁⊗c₂, y = b⊗b'` reduces via `mul_TP_TTTC_circ_pure_u_v`
    (Lemma A) + `circ_mul_distrib_via_comul` (Prop 2.7.iii) to a common
    `((a₁·c₁) ○ b) ⊗ ((a₂·c₂) ○ b')` form. Add cases distribute via
    linearity of `TP.mk`, `TP.map`, `*`, and `mul'`. -/
private lemma mul_TP_G_TTTC_cm_eq_circ_mul
    (u v y : SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) :
    LinearMap.mul' R (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
      ((TensorProduct.map
          ((TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                              (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
            ((TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
              ((TensorProduct.mk R
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)) u)))
          ((TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                              (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
            ((TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
              ((TensorProduct.mk R
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)) v))))
        ((TensorProduct.tensorTensorTensorComm R
            (SymmetricAlgebra R L) (SymmetricAlgebra R L)
            (SymmetricAlgebra R L) (SymmetricAlgebra R L))
          ((TensorProduct.map
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))) y))) =
    (TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                       (TensorProduct.lift (oudomGuinCirc (R := R))))
      ((TensorProduct.tensorTensorTensorComm R
          (SymmetricAlgebra R L) (SymmetricAlgebra R L)
          (SymmetricAlgebra R L) (SymmetricAlgebra R L))
        ((u * v) ⊗ₜ[R] y)) := by
  -- Step 1: reduce u to pure form.
  induction u using TensorProduct.induction_on generalizing v y with
  | zero =>
    simp only [LinearMap.comp_zero, TensorProduct.map_zero_left,
               LinearMap.zero_apply, map_zero, zero_mul,
               TensorProduct.zero_tmul]
  | tmul a₁ a₂ =>
    -- Step 2: reduce v to pure form.
    induction v using TensorProduct.induction_on generalizing y with
    | zero =>
      simp only [LinearMap.comp_zero, TensorProduct.map_zero_right,
                 LinearMap.zero_apply, map_zero, mul_zero,
                 TensorProduct.zero_tmul]
    | tmul c₁ c₂ =>
      -- Step 3: reduce y to pure form.
      induction y using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero, TensorProduct.tmul_zero]
      | tmul b b' =>
        -- All pure. (TP.map cm cm)(b ⊗ b') = cm b ⊗ cm b'.
        -- Then apply Lemma A (mul_TP_TTTC_circ_pure_u_v) at p = cm b, q = cm b'.
        rw [TensorProduct.map_tmul]
        rw [mul_TP_TTTC_circ_pure_u_v]
        -- Goal: mul'((TP.map (○a₁) (○c₁))(cm b)) ⊗ mul'((TP.map (○a₂) (○c₂))(cm b'))
        --     = (TP.map ○ ○)(TTTC(((a₁⊗a₂) * (c₁⊗c₂)) ⊗ (b ⊗ b')))
        -- Apply Prop 2.7.iii (circ_mul_distrib_via_comul) backwards on each LHS factor.
        rw [show LinearMap.mul' R (SymmetricAlgebra R L)
                  ((TensorProduct.map (oudomGuinCirc (R := R) a₁)
                                      (oudomGuinCirc (R := R) c₁))
                    (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) b)) =
                oudomGuinCirc (R := R) (a₁ * c₁) b from by
              rw [circ_mul_distrib_via_comul]
              rfl]
        rw [show LinearMap.mul' R (SymmetricAlgebra R L)
                  ((TensorProduct.map (oudomGuinCirc (R := R) a₂)
                                      (oudomGuinCirc (R := R) c₂))
                    (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) b')) =
                oudomGuinCirc (R := R) (a₂ * c₂) b' from by
              rw [circ_mul_distrib_via_comul]
              rfl]
        -- Goal: ((a₁·c₁) ○ b) ⊗ ((a₂·c₂) ○ b') = RHS
        -- Unfold RHS: (a₁⊗a₂)*(c₁⊗c₂) = (a₁·c₁) ⊗ (a₂·c₂), TTTC, TP.map ○ ○, lift.tmul.
        rw [Algebra.TensorProduct.tmul_mul_tmul,
            TensorProduct.tensorTensorTensorComm_tmul,
            TensorProduct.map_tmul,
            TensorProduct.lift.tmul, TensorProduct.lift.tmul]
      | add y1 y2 ihy1 ihy2 =>
        simp only [map_add, mul_add, TensorProduct.tmul_add, ihy1, ihy2]
    | add v1 v2 ihv1 ihv2 =>
      simp only [LinearMap.map_add, LinearMap.add_comp, LinearMap.comp_add,
                 TensorProduct.map_add_right, LinearMap.add_apply, map_add,
                 mul_add, TensorProduct.add_tmul, TensorProduct.tmul_add,
                 ihv1 y, ihv2 y]
  | add u1 u2 ihu1 ihu2 =>
    simp only [LinearMap.map_add, LinearMap.add_comp, LinearMap.comp_add,
               TensorProduct.map_add_left, LinearMap.add_apply, map_add,
               add_mul, TensorProduct.add_tmul, ihu1 v y, ihu2 v y]

/-- **Cocomm-step helper for `comul_circ` mul case.**

    After applying Prop 2.7.iii (LHS expansion) + `AlgHom.comp_mul'` (push Δ
    through `mul'`) + `TensorProduct.map_comp` (fuse TP.maps) + IH (substitute
    `Δ ∘ ○A_i = (TP.map ○ ○) ∘ TTTC ∘ (TP.map Δ Δ) ∘ (TP.mk A_i)`) on the LHS,
    and `Bialgebra.comul_mul` on the RHS, the mul case of `comul_circ` reduces
    to this identity.

    Both sides, fully expanded via Sweedler, give 4-fold sums:
    - LHS pairing: `(b_{1,1}, b_{2,1}) | (b_{1,2}, b_{2,2})`
    - RHS pairing (after Prop 2.7.iii on each `(a · a') ○ b` factor):
      `(b_{1,1}, b_{1,2}) | (b_{2,1}, b_{2,2})`

    They differ by swapping `b_{2,1} ↔ b_{1,2}`, which is TTTC on the iterated
    coproduct of `B`. By `comul_squared_TTTC_eq` (cocommutativity of `Δ`), this
    swap fixes the iterated coproduct, so the two sides agree.

    Proof structure:
    1. Factor F_i = G_{cm A_i} ∘ cm via `TP.map_comp`, where
       `G u Y := (TP.map ○ ○)(TTTC(u ⊗ Y))`.
    2. Insert TTTC at Δ²B via `comul_squared_TTTC_eq` (cocomm).
    3. Apply `mul_TP_G_TTTC_cm_eq_circ_mul` specialized at `u = cm A₁,
       v = cm A₂, y = cm B`. -/
private theorem comul_circ_mul_cocomm_aux (A₁ A₂ B : SymmetricAlgebra R L) :
    LinearMap.mul' R (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
      ((TensorProduct.map
          ((TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                              (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
            ((TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
              ((TensorProduct.map
                  (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
                  (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))).comp
                ((TensorProduct.mk R (SymmetricAlgebra R L) (SymmetricAlgebra R L)) A₁))))
          ((TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                              (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
            ((TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
              ((TensorProduct.map
                  (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
                  (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))).comp
                ((TensorProduct.mk R (SymmetricAlgebra R L) (SymmetricAlgebra R L)) A₂)))))
        (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B)) =
    (TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                       (TensorProduct.lift (oudomGuinCirc (R := R))))
      ((TensorProduct.tensorTensorTensorComm R
          (SymmetricAlgebra R L) (SymmetricAlgebra R L)
          (SymmetricAlgebra R L) (SymmetricAlgebra R L))
        ((Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) A₁ *
          Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) A₂)
            ⊗ₜ[R]
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B))) := by
  -- Step 1: Rewrite `(TP.map cm cm).comp ((TP.mk A_i))` into
  --         `((TP.mk (cm A_i))).comp cm` (swap cm to the right).
  have h_swap : ∀ A : SymmetricAlgebra R L,
      (TensorProduct.map
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))).comp
          ((TensorProduct.mk R (SymmetricAlgebra R L) (SymmetricAlgebra R L)) A) =
        ((TensorProduct.mk R
            (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
            (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L))
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) A)).comp
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)) := by
    intro A
    ext X
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply, TensorProduct.map_tmul]
  rw [h_swap A₁, h_swap A₂]
  -- Step 2: Rearrange comp via associativity so `cm` is at the outermost right.
  rw [show (TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                              (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
            ((TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
              (((TensorProduct.mk R
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L))
                  (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) A₁)).comp
                (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)))) =
          ((TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                              (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
            ((TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
              ((TensorProduct.mk R
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L))
                (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) A₁)))).comp
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)) from rfl,
      show (TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                              (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
            ((TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
              (((TensorProduct.mk R
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L))
                  (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) A₂)).comp
                (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)))) =
          ((TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                              (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
            ((TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
              ((TensorProduct.mk R
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L))
                (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) A₂)))).comp
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)) from rfl]
  -- Step 3: Factor `TP.map (G ∘ cm) (G ∘ cm) = (TP.map G G) ∘ (TP.map cm cm)`.
  rw [TensorProduct.map_comp]
  -- Now LHS = mul'_{S⊗S}((TP.map G_1 G_2)((TP.map cm cm)(cm B))).
  simp only [LinearMap.coe_comp, Function.comp_apply]
  -- Step 4: Insert TTTC at (TP.map cm cm)(cm B) via cocomm.
  have h_cocomm := congrArg
      (fun (f : SymmetricAlgebra R L →ₗ[R]
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) ⊗[R]
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)) => f B)
      comul_squared_TTTC_eq
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h_cocomm
  rw [← h_cocomm]
  -- Step 5: Apply Lemma B specialized at u = cm A_1, v = cm A_2, y = cm B.
  exact mul_TP_G_TTTC_cm_eq_circ_mul
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) A₁)
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) A₂)
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B)

/-- **Prop 2.8 (iii)** of Oudom-Guin (2008). `Δ(A ○ B) = Σ (A₍₁₎ ○ B₍₁₎) ⊗
    (A₍₂₎ ○ B₍₂₎)`, the bialgebra-style "○ is a coalgebra map" identity
    on `S(L) ⊗ S(L)` with the tensor product coalgebra structure.

    In linear-map terms: `(uncurried ○) : S(L) ⊗ S(L) → S(L)` is a
    coalgebra map (target coalgebra: `S(L)`; source coalgebra: tensor
    product). Equivalently:

    ```
    Δ ∘ μ = (μ ⊗ μ) ∘ TTTC ∘ (Δ ⊗ Δ)    as maps  S ⊗ S → S ⊗ S
    ```

    where `μ = TensorProduct.lift oudomGuinCirc`.

    Proof: induction on `A` via `SymmetricAlgebra.induction` with
    `generalizing B`. The four cases:

    * `algebraMap r`: both sides reduce to `r • ε(B) • (1 ⊗ 1)` via
      `one_circ` (Prop 2.8.i) + counit triangle. Uses helpers
      `map_uncurry_TTTC_pure` + `map_circ_a_circ_one_comul`.
    * `ι T`: both sides reduce to `(ι T ○ B) ⊗ 1 + 1 ⊗ (ι T ○ B)` via
      primitivity of `ι T` (so `Δ(ι T) = ι T ⊗ 1 + 1 ⊗ ι T`) and
      `circByT_total T B ∈ L` (so its image under `ι` is primitive too).
      Uses `map_circ_a_circ_one_comul` and `map_circ_one_circ_b_comul` on
      the two halves of `Δ(ι T)`.
    * `mul A₁ A₂`: OG's Sweedler-chasing chain using Prop 2.7.iii
      (`circ_mul_distrib_via_comul`) twice, `Bialgebra.comul_mul`, IH on
      both factors, and `comul_squared_TTTC_eq` (cocommutativity-derived
      4-fold symmetry) to align the inner pairing.
    * `add A₁ A₂`: linearity. -/
theorem comul_circ (A B : SymmetricAlgebra R L) :
    Coalgebra.comul (R := R) (oudomGuinCirc (R := R) A B) =
      (TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                         (TensorProduct.lift (oudomGuinCirc (R := R))))
        ((TensorProduct.tensorTensorTensorComm R
            (SymmetricAlgebra R L) (SymmetricAlgebra R L)
            (SymmetricAlgebra R L) (SymmetricAlgebra R L))
          ((TensorProduct.map
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)))
            (A ⊗ₜ[R] B))) := by
  induction A using SymmetricAlgebra.induction generalizing B with
  | algebraMap r =>
    -- A = r • 1. Pull r out via linearity in A and reduce to A = 1.
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [map_smul, LinearMap.smul_apply, ← TensorProduct.smul_tmul']
    congr 1
    -- Goal: comul (1 ○ B) = TP.map μ μ (TTTC (TP.map Δ Δ (1 ⊗ B)))
    rw [one_circ, map_smul, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
        TensorProduct.map_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
        map_uncurry_TTTC_pure, map_circ_a_circ_one_comul, one_circ,
        TensorProduct.smul_tmul']
  | ι T =>
    -- LHS: comul (ι T ○ B) = comul (ι (circByT_total T B)) [by oudomGuinCirc_eq_ofConv + circHom_ι]
    --     = (ι T ○ B) ⊗ 1 + 1 ⊗ (ι T ○ B)  [by SymmetricAlgebra.comul_ι and primitivity]
    have h_ι_T_circ : oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T) B =
                     SymmetricAlgebra.ι R L (OudomGuinCircConstruct.circByT_total T B) := by
      rw [oudomGuinCirc_eq_ofConv, circHom_ι]; rfl
    rw [h_ι_T_circ,
        SymmetricAlgebra.comul_ι R L (OudomGuinCircConstruct.circByT_total T B)]
    -- Now RHS computation: comul (ι T) = ι T ⊗ 1 + 1 ⊗ ι T (primitive).
    rw [TensorProduct.map_tmul, SymmetricAlgebra.comul_ι R L T]
    -- After: TP.map μ μ (TTTC ((ι T ⊗ 1 + 1 ⊗ ι T) ⊗ Δ B))
    rw [TensorProduct.add_tmul, map_add, map_add,
        map_uncurry_TTTC_pure, map_uncurry_TTTC_pure,
        map_circ_a_circ_one_comul, map_circ_one_circ_b_comul]
    -- Now: ι (circByT_total T B) ⊗ 1 + 1 ⊗ ι (circByT_total T B) = (ι T ○ B) ⊗ 1 + 1 ⊗ (ι T ○ B)
    rw [← h_ι_T_circ]
  | mul A₁ A₂ ih₁ ih₂ =>
    -- ## Step 1: LHS via Prop 2.7.iii (`circ_mul_distrib_via_comul`).
    -- `(A₁·A₂) ○ B = mul'(TP.map (○A₁) (○A₂) (Δ B))`.
    rw [circ_mul_distrib_via_comul]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    -- Goal: Δ(mul'(TP.map (○A₁) (○A₂)(Δ B))) =
    --       (TP.map ○_lift ○_lift)(TTTC((TP.map Δ Δ)((A₁*A₂) ⊗ B)))
    -- ## Step 2: Push Δ through mul' via `AlgHom.comp_mul'` on `Bialgebra.comulAlgHom`.
    -- The linear-map equation `comul ∘ mul' = mul'_{S⊗S} ∘ (TP.map comul comul)`.
    have h_push_lm :
        (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)).comp
            (LinearMap.mul' R (SymmetricAlgebra R L)) =
          (LinearMap.mul' R (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)).comp
            (TensorProduct.map
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))) :=
      AlgHom.comp_mul' (Bialgebra.comulAlgHom R (SymmetricAlgebra R L))
    have h_push := congrArg
        (fun (f : (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) →ₗ[R]
                    SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) =>
          f ((TensorProduct.map (oudomGuinCirc (R := R) A₁) (oudomGuinCirc (R := R) A₂))
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B)))
        h_push_lm
    simp only [LinearMap.coe_comp, Function.comp_apply] at h_push
    rw [h_push]
    -- Goal: mul'_{S⊗S}((TP.map Δ Δ)(TP.map (○A₁)(○A₂)(Δ B))) = RHS
    -- ## Step 3: Fuse the two TP.maps on LHS.
    have h_fuse := congrArg
        (fun (f : (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) →ₗ[R]
                    (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) ⊗[R]
                    (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)) =>
          f (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B))
        (TensorProduct.map_comp
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
          (oudomGuinCirc (R := R) A₁)
          (oudomGuinCirc (R := R) A₂))
    simp only [LinearMap.coe_comp, Function.comp_apply] at h_fuse
    rw [← h_fuse]
    -- Goal: mul'_{S⊗S}((TP.map (Δ ∘ₗ ○A₁) (Δ ∘ₗ ○A₂))(Δ B)) = RHS
    -- ## Step 4: Apply IH as LinearMap equations on the LHS.
    -- ih_i : ∀ B', Δ(A_i ○ B') = (TP.map ○_lift ○_lift)(TTTC((TP.map Δ Δ)(A_i ⊗ B')))
    -- Linear-map form: `Δ ∘ ○A_i = (TP.map ○_lift ○_lift) ∘ TTTC ∘ (TP.map Δ Δ) ∘ (TP.mk A_i)`.
    have ih₁_lm : (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)).comp
                    (oudomGuinCirc (R := R) A₁) =
                  (TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                                     (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
                    ((TensorProduct.tensorTensorTensorComm R
                        (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                        (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
                      ((TensorProduct.map
                          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
                          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))).comp
                        ((TensorProduct.mk R (SymmetricAlgebra R L) (SymmetricAlgebra R L)) A₁))) := by
      ext B'
      simp only [LinearMap.comp_apply, TensorProduct.mk_apply]
      exact ih₁ B'
    have ih₂_lm : (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)).comp
                    (oudomGuinCirc (R := R) A₂) =
                  (TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                                     (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
                    ((TensorProduct.tensorTensorTensorComm R
                        (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                        (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
                      ((TensorProduct.map
                          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
                          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))).comp
                        ((TensorProduct.mk R (SymmetricAlgebra R L) (SymmetricAlgebra R L)) A₂))) := by
      ext B'
      simp only [LinearMap.comp_apply, TensorProduct.mk_apply]
      exact ih₂ B'
    rw [ih₁_lm, ih₂_lm]
    -- ## Step 5: Reduce RHS via `Bialgebra.comul_mul`.
    -- `(TP.map Δ Δ)((A₁*A₂) ⊗ B) = Δ(A₁*A₂) ⊗ Δ B = (Δ A₁ · Δ A₂) ⊗ Δ B`.
    rw [TensorProduct.map_tmul, Bialgebra.comul_mul]
    -- ## Step 6: The cocomm step. Both sides are now expressed; close via the
    -- key lemma `comul_circ_mul_cocomm_aux` (below).
    exact comul_circ_mul_cocomm_aux A₁ A₂ B
  | add A₁ A₂ ih₁ ih₂ =>
    -- Linearity in A: distribute through both sides.
    simp only [LinearMap.add_apply, map_add, TensorProduct.add_tmul]
    rw [ih₁, ih₂]

/-! ## §4: Prop 2.8.v — the key inductive lemma

`(A ○ B) ○ C = A ○ ((B ○ C₍₁₎) · C₍₂₎)`. Proved by induction on the
length of `A` (Oudom-Guin paper page 7).

This is THE substantive lemma needed for Lemma 2.10's proof of `★`
associativity. -/

/-- **Sweedler counit calculation** for the Q2 RHS:
    `ε((B ○ C₍₁₎) · C₍₂₎) = ε(B) · ε(C)`.

    Adapts the smul-pullout pattern from `counit_circ`'s mul case to a
    sub-shape that occurs inside the Q2 algebraMap case. -/
private theorem algebraMapInv_circ_mul'_comul_aux
    (B C : SymmetricAlgebra R L) :
    SymmetricAlgebra.algebraMapInv (M := L)
        ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
          TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) C)) =
      SymmetricAlgebra.algebraMapInv (M := L) B *
      SymmetricAlgebra.algebraMapInv (M := L) C := by
  simp only [LinearMap.coe_comp, Function.comp_apply]
  -- Push algebraMapInv through mul' via AlgHom.comp_mul'.
  have h_push := congrArg
      (fun (f : (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) →ₗ[R] R) =>
        f ((TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) C)))
      (AlgHom.comp_mul' (SymmetricAlgebra.algebraMapInv (M := L)))
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply] at h_push
  rw [h_push]
  -- Fuse the two TensorProduct.map applications.
  have h_fuse := congrArg
      (fun (f : (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) →ₗ[R] R ⊗[R] R) =>
        f (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) C))
      (TensorProduct.map_comp
        (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap
        (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap
        (oudomGuinCirc (R := R) B)
        LinearMap.id)
  simp only [LinearMap.coe_comp, Function.comp_apply] at h_fuse
  rw [← h_fuse]
  -- Apply counit_circ in linear-map form: algInv ∘ ○B = algInv B • algInv.
  have h_algInv_circ_B :
      (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap.comp
          (oudomGuinCirc (R := R) B) =
        SymmetricAlgebra.algebraMapInv (M := L) B •
          (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap := by
    ext X
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
               LinearMap.smul_apply, smul_eq_mul]
    exact counit_circ B X
  rw [h_algInv_circ_B, LinearMap.comp_id]
  -- Pull smul out of the left factor, then out of map and mul'.
  rw [TensorProduct.map_smul_left, LinearMap.smul_apply, map_smul,
      mul'_map_algebraMapInv_comul, smul_eq_mul]

/-- **Prop 2.8 (iv)** of Oudom-Guin (2008) — generalization of `circ_T_mul`
    (Prop 2.7.ii) from `A = ι T` to arbitrary `A ∈ S(L)`:

    `A ○ (B · ι X) = (A ○ B) ○ ι X - A ○ (B ○ ι X)` for all `A, B ∈ S(L)`, `X ∈ L`.

    This is the key ingredient for closing Q2 (`circ_assoc_via_comul`,
    Prop 2.8.v) by induction on `C`.

    Proof by `SymmetricAlgebra.induction` on `A`:

    * `algebraMap r`: both sides reduce to 0 via `algebraMapInv_ι X = 0`
      (since `ε(ι X) = 0` for primitives).
    * `ι T`: direct from `circ_T_mul` (Prop 2.7.ii).
    * `mul A₁ A₂` (with IH): Sweedler expansion via `circ_mul_distrib_via_comul`
      (Prop 2.7.iii) on all three `(A₁·A₂) ○ _` instances + IH on each factor
      + `comul_circ` (Prop 2.8.iii) on `cm(B ○ ι X)`.
    * `add A₁ A₂` (with IH): linearity. -/
private theorem circ_general_mul_ι
    (A : SymmetricAlgebra R L) :
    ∀ (B : SymmetricAlgebra R L) (X : L),
      oudomGuinCirc (R := R) A (B * SymmetricAlgebra.ι R L X) =
        oudomGuinCirc (R := R)
            (oudomGuinCirc (R := R) A B) (SymmetricAlgebra.ι R L X) -
        oudomGuinCirc (R := R) A
            (oudomGuinCirc (R := R) B (SymmetricAlgebra.ι R L X)) := by
  induction A using SymmetricAlgebra.induction with
  | algebraMap r =>
    intro B X
    -- Both sides reduce to 0 via `algebraMapInv (ι X) = 0`.
    rw [Algebra.algebraMap_eq_smul_one]
    -- LHS: (r•1) ○ (B · ι X) = r • algebraMapInv(B · ι X) • 1
    --                        = r • (algebraMapInv B * 0) • 1 = 0
    rw [show oudomGuinCirc (R := R) (r • (1 : SymmetricAlgebra R L))
              (B * SymmetricAlgebra.ι R L X) =
            r • SymmetricAlgebra.algebraMapInv (M := L)
                (B * SymmetricAlgebra.ι R L X) •
              (1 : SymmetricAlgebra R L) from by
          rw [map_smul, LinearMap.smul_apply, one_circ]]
    rw [show SymmetricAlgebra.algebraMapInv (M := L)
              (B * SymmetricAlgebra.ι R L X) = 0 from by
          rw [map_mul, SymmetricAlgebra.algebraMapInv_ι, mul_zero]]
    rw [zero_smul, smul_zero]
    -- RHS1: ((r•1) ○ B) ○ ι X = r • algebraMapInv B • algebraMapInv(ι X) • 1 = 0
    rw [show oudomGuinCirc (R := R) (r • (1 : SymmetricAlgebra R L)) B =
            r • SymmetricAlgebra.algebraMapInv (M := L) B •
              (1 : SymmetricAlgebra R L) from by
          rw [map_smul, LinearMap.smul_apply, one_circ]]
    rw [show oudomGuinCirc (R := R)
              (r • SymmetricAlgebra.algebraMapInv (M := L) B •
                (1 : SymmetricAlgebra R L))
              (SymmetricAlgebra.ι R L X) =
            r • SymmetricAlgebra.algebraMapInv (M := L) B •
              SymmetricAlgebra.algebraMapInv (M := L) (SymmetricAlgebra.ι R L X) •
              (1 : SymmetricAlgebra R L) from by
          rw [map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, one_circ]]
    rw [SymmetricAlgebra.algebraMapInv_ι, zero_smul, smul_zero]
    -- RHS2: (r•1) ○ (B ○ ι X) = r • algebraMapInv(B ○ ι X) • 1
    --                         = r • (algebraMapInv B * 0) • 1 = 0
    rw [show oudomGuinCirc (R := R) (r • (1 : SymmetricAlgebra R L))
              (oudomGuinCirc (R := R) B (SymmetricAlgebra.ι R L X)) =
            r • SymmetricAlgebra.algebraMapInv (M := L)
                (oudomGuinCirc (R := R) B (SymmetricAlgebra.ι R L X)) •
              (1 : SymmetricAlgebra R L) from by
          rw [map_smul, LinearMap.smul_apply, one_circ]]
    rw [counit_circ, SymmetricAlgebra.algebraMapInv_ι, mul_zero,
        zero_smul, smul_zero]
    -- Goal: 0 = 0 - 0
    rw [sub_self]
  | ι T =>
    intro B X
    -- Direct from circ_T_mul (Prop 2.7.ii).
    exact circ_T_mul T B X
  | mul A₁ A₂ ih₁ ih₂ =>
    intro B X
    -- ih₁ : ∀ B' X', A₁ ○ (B' * ι X') = (A₁ ○ B') ○ ι X' - A₁ ○ (B' ○ ι X')
    -- ih₂ : ∀ B' X', A₂ ○ (B' * ι X') = (A₂ ○ B') ○ ι X' - A₂ ○ (B' ○ ι X')
    -- Apply Prop 2.7.iii to all three (A₁*A₂) ○ ___ instances.
    rw [circ_mul_distrib_via_comul A₁ A₂ (B * SymmetricAlgebra.ι R L X),
        circ_mul_distrib_via_comul A₁ A₂ B,
        circ_mul_distrib_via_comul A₁ A₂
          (oudomGuinCirc (R := R) B (SymmetricAlgebra.ι R L X))]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    -- Compute cm(B * ι X) = cm B * cm(ι X) = cm B * (ι X ⊗ 1 + 1 ⊗ ι X).
    rw [show Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)
              (B * SymmetricAlgebra.ι R L X) =
            Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B *
              Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)
                (SymmetricAlgebra.ι R L X) from by
          rw [Bialgebra.comul_mul]]
    rw [SymmetricAlgebra.comul_ι]
    -- Compute cm(B ○ ι X) via comul_circ.
    rw [comul_circ B (SymmetricAlgebra.ι R L X)]
    rw [TensorProduct.map_tmul, SymmetricAlgebra.comul_ι]
    -- Generalize cm B → bsum so we can induct on it (no hypothesis kept;
    -- we prove the equation for all bsum and the specific case follows).
    generalize (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B) = bsum
    -- Induct on bsum via TP.induction_on.
    induction bsum using TensorProduct.induction_on with
    | zero =>
      simp only [zero_mul, TensorProduct.zero_tmul, map_zero, sub_zero,
                 LinearMap.zero_apply]
    | tmul b₁ b₂ =>
      -- Pure case: bsum = b₁ ⊗ b₂. Both sides expand to matching 4-term sums.
      -- LHS: (b₁⊗b₂) * (ιX ⊗ 1 + 1 ⊗ ιX) = (b₁·ιX) ⊗ b₂ + b₁ ⊗ (b₂·ιX).
      rw [show (b₁ ⊗ₜ[R] b₂) *
              (SymmetricAlgebra.ι R L X ⊗ₜ[R] (1 : SymmetricAlgebra R L) +
               (1 : SymmetricAlgebra R L) ⊗ₜ[R] SymmetricAlgebra.ι R L X) =
            (b₁ * SymmetricAlgebra.ι R L X) ⊗ₜ[R] b₂ +
            b₁ ⊗ₜ[R] (b₂ * SymmetricAlgebra.ι R L X) from by
          rw [mul_add, Algebra.TensorProduct.tmul_mul_tmul,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]]
      -- RHS-second: TTTC((b₁⊗b₂) ⊗ (ιX ⊗ 1 + 1 ⊗ ιX)) = (b₁⊗ιX) ⊗ (b₂⊗1) + (b₁⊗1) ⊗ (b₂⊗ιX).
      rw [show (TensorProduct.tensorTensorTensorComm R
                  (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                  (SymmetricAlgebra R L) (SymmetricAlgebra R L))
                ((b₁ ⊗ₜ[R] b₂) ⊗ₜ[R]
                  (SymmetricAlgebra.ι R L X ⊗ₜ[R] (1 : SymmetricAlgebra R L) +
                   (1 : SymmetricAlgebra R L) ⊗ₜ[R] SymmetricAlgebra.ι R L X)) =
            (b₁ ⊗ₜ[R] SymmetricAlgebra.ι R L X) ⊗ₜ[R]
              (b₂ ⊗ₜ[R] (1 : SymmetricAlgebra R L)) +
            (b₁ ⊗ₜ[R] (1 : SymmetricAlgebra R L)) ⊗ₜ[R]
              (b₂ ⊗ₜ[R] SymmetricAlgebra.ι R L X) from by
          rw [TensorProduct.tmul_add, map_add,
              TensorProduct.tensorTensorTensorComm_tmul,
              TensorProduct.tensorTensorTensorComm_tmul]]
      -- Apply TP.map (lift ○)(lift ○): map (b⊗c) gives (b○_) ⊗ (c○_).
      -- And ○ 1 = identity (by circ_one_right).
      simp only [map_add, TensorProduct.map_tmul, TensorProduct.lift.tmul,
                 LinearMap.mul'_apply, Algebra.TensorProduct.tmul_mul_tmul,
                 circ_one_right]
      -- Apply IH on A₁ at B' = b₁ and A₂ at B' = b₂.
      rw [ih₁ b₁ X, ih₂ b₂ X]
      -- Apply Prop 2.7.iii on `((A₁ ○ b₁) · (A₂ ○ b₂)) ○ ι X`.
      rw [circ_mul_distrib_via_comul
            (oudomGuinCirc (R := R) A₁ b₁)
            (oudomGuinCirc (R := R) A₂ b₂)
            (SymmetricAlgebra.ι R L X)]
      simp only [LinearMap.coe_comp, Function.comp_apply,
                 SymmetricAlgebra.comul_ι, map_add, TensorProduct.map_tmul,
                 LinearMap.mul'_apply, circ_one_right]
      ring
    | add y₁ y₂ ihy₁ ihy₂ =>
      simp only [add_mul, TensorProduct.add_tmul, map_add,
                 LinearMap.add_apply, ihy₁, ihy₂]
      ring
  | add A₁ A₂ ih₁ ih₂ =>
    intro B X
    -- Linearity in A.
    simp only [map_add, LinearMap.add_apply, ih₁, ih₂]
    ring

/-- **Compatibility lemma for Q2**: For `B, D ∈ S(L)` and `X ∈ L`:
    ```
    (mul' ∘ TP.map (○B) id)(cm(D · ι X)) =
      Y_D · ι X + Y_D ○ ι X - (mul' ∘ TP.map (○B) id)(cm(D ○ ι X))
    ```
    where `Y_D := (mul' ∘ TP.map (○B) id)(cm D)`.

    Combined with 3.9.iv (rearranged: `(A ○ Y_D) ○ ι X = A ○ (Y_D · ι X) + A ○ (Y_D ○ ι X)`),
    this is what closes the Q2 succ case `(A ○ B) ○ (D · ι X) = A ○ ((mul' ∘ ...)(cm(D · ι X)))`.

    Proof: TP.induction_on `cm D`. Pure case `cm D = d₁ ⊗ d₂` reduces algebraically
    to 3.9.iv applied at `(B, d₁, X)`. -/
private theorem compat_mul_circ_mul_ι
    (B D : SymmetricAlgebra R L) (X : L) :
    (LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
       TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
       (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)
         (D * SymmetricAlgebra.ι R L X)) =
    (((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
         TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
         (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) D)) *
      SymmetricAlgebra.ι R L X) +
    (oudomGuinCirc (R := R)
        ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
            TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) D))
        (SymmetricAlgebra.ι R L X)) -
    (LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
       TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
       (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)
         (oudomGuinCirc (R := R) D (SymmetricAlgebra.ι R L X))) := by
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [Bialgebra.comul_mul, SymmetricAlgebra.comul_ι]
  rw [comul_circ D (SymmetricAlgebra.ι R L X), TensorProduct.map_tmul,
      SymmetricAlgebra.comul_ι]
  -- Generalize cm D → bsum and induct.
  generalize (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) D) = bsum
  induction bsum using TensorProduct.induction_on with
  | zero =>
    simp only [zero_mul, TensorProduct.zero_tmul, map_zero, sub_zero,
               LinearMap.zero_apply, mul_zero, zero_add]
  | tmul d₁ d₂ =>
    -- Distribute LHS: (d₁ ⊗ d₂) * (ιX ⊗ 1 + 1 ⊗ ιX) = (d₁·ιX) ⊗ d₂ + d₁ ⊗ (d₂·ιX).
    rw [show (d₁ ⊗ₜ[R] d₂) *
            (SymmetricAlgebra.ι R L X ⊗ₜ[R] (1 : SymmetricAlgebra R L) +
             (1 : SymmetricAlgebra R L) ⊗ₜ[R] SymmetricAlgebra.ι R L X) =
          (d₁ * SymmetricAlgebra.ι R L X) ⊗ₜ[R] d₂ +
          d₁ ⊗ₜ[R] (d₂ * SymmetricAlgebra.ι R L X) from by
        rw [mul_add, Algebra.TensorProduct.tmul_mul_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]]
    -- Distribute TTTC + TP.map (lift ○)(lift ○) on cm(D ○ ι X) part.
    rw [show (TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L))
              ((d₁ ⊗ₜ[R] d₂) ⊗ₜ[R]
                (SymmetricAlgebra.ι R L X ⊗ₜ[R] (1 : SymmetricAlgebra R L) +
                 (1 : SymmetricAlgebra R L) ⊗ₜ[R] SymmetricAlgebra.ι R L X)) =
          (d₁ ⊗ₜ[R] SymmetricAlgebra.ι R L X) ⊗ₜ[R]
            (d₂ ⊗ₜ[R] (1 : SymmetricAlgebra R L)) +
          (d₁ ⊗ₜ[R] (1 : SymmetricAlgebra R L)) ⊗ₜ[R]
            (d₂ ⊗ₜ[R] SymmetricAlgebra.ι R L X) from by
        rw [TensorProduct.tmul_add, map_add,
            TensorProduct.tensorTensorTensorComm_tmul,
            TensorProduct.tensorTensorTensorComm_tmul]]
    -- Apply TP.map, lift.tmul, mul'_apply, circ_one_right.
    simp only [map_add, TensorProduct.map_tmul, TensorProduct.lift.tmul,
               LinearMap.mul'_apply, LinearMap.id_coe, id_eq, circ_one_right]
    -- Apply Prop 2.7.iii on ((B ○ d₁) * d₂) ○ ι X (the RHS-2 term, oudomGuinCirc on a product).
    rw [circ_mul_distrib_via_comul
          (oudomGuinCirc (R := R) B d₁) d₂
          (SymmetricAlgebra.ι R L X)]
    simp only [LinearMap.coe_comp, Function.comp_apply,
               SymmetricAlgebra.comul_ι, map_add, TensorProduct.map_tmul,
               LinearMap.mul'_apply, circ_one_right]
    -- Apply 3.9.iv at B, d₁, X to bridge the d₁ side.
    rw [circ_general_mul_ι B d₁ X]
    ring
  | add y₁ y₂ ihy₁ ihy₂ =>
    simp only [add_mul, TensorProduct.add_tmul, map_add,
               LinearMap.add_apply, ihy₁, ihy₂]
    ring

/-- **Per-tprod form** of Prop 2.8 (v). Proves
    `(A ○ B) ○ algHomL (tprod_m a) = A ○ ((mul' ∘ TP.map (○B) id)(comul (algHomL (tprod_m a))))`
    by induction on `m`.

    Lifted to the full `circ_assoc_via_comul` via `algHomL_surjective` +
    `TA_linearMap_ext_tprod`.

    Proof structure (OG paper p. 155):
    - `m = 0` (`tprod_0 = 1`): both sides reduce to `A ○ B` via `circ_one_right`
      + `Bialgebra.comul_one`.
    - `m + 1` (`tprod_{m+1} a = tprod_m (Fin.init a) * ι (a (Fin.last m))`):
      apply `circ_general_mul_ι` (3.9.iv) to LHS, IH at `Fin.init a`,
      `circ_general_mul_ι` rearranged at `(A, Y_D, X)`,
      `oudomGuinCirc_algHomL_tprod_ι` + per-summand IH for the `D ○ ι X` term,
      `compat_mul_circ_mul_ι` for the final bridge. -/
private theorem circ_assoc_via_comul_tprod
    (A B : SymmetricAlgebra R L) :
    ∀ (m : ℕ) (a : Fin m → L),
      oudomGuinCirc (R := R) (oudomGuinCirc (R := R) A B)
          (OudomGuinCircConstruct.algHomL (TensorAlgebra.tprod R L m a)) =
        oudomGuinCirc (R := R) A
          ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
              TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)
              (OudomGuinCircConstruct.algHomL
                (TensorAlgebra.tprod R L m a)))) := by
  intro m
  induction m with
  | zero =>
    intro a
    -- `tprod_0 a = 1` in TA; `algHomL 1 = 1` in S(L).
    have h_tprod0 : TensorAlgebra.tprod R L 0 a = 1 := by
      rw [TensorAlgebra.tprod_apply]; simp [List.ofFn_zero]
    rw [h_tprod0,
        show OudomGuinCircConstruct.algHomL (R := R) (L := L)
              (1 : TensorAlgebra R L) = (1 : SymmetricAlgebra R L) from
          map_one (SymmetricAlgebra.algHom R L)]
    -- LHS: `(A ○ B) ○ 1 = A ○ B` via `circ_one_right`.
    rw [circ_one_right, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
    -- RHS: `A ○ (mul' (TP.map (○B) id (1 ⊗ 1))) = A ○ B` via simp chain.
    simp only [LinearMap.coe_comp, Function.comp_apply,
               TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
               LinearMap.mul'_apply, circ_one_right, mul_one]
  | succ m ih =>
    intro a
    -- Decompose `tprod_{m+1} a = tprod_m (Fin.init a) * ι (a (Fin.last m))`.
    have h_a_eq : a = Fin.snoc (Fin.init a) (a (Fin.last m)) :=
      (Fin.snoc_init_self a).symm
    have h_tprod_succ :
        TensorAlgebra.tprod R L (m + 1) a =
        TensorAlgebra.tprod R L m (Fin.init a) *
          TensorAlgebra.ι R (a (Fin.last m)) := by
      conv_lhs => rw [h_a_eq]
      rw [Fin.snoc_eq_append,
          OudomGuinCircConstruct.ι_eq_tprod_one,
          ← OudomGuinCircConstruct.tprod_mul_tprod]
      congr 1
    have h_algHomL_split :
        OudomGuinCircConstruct.algHomL (R := R) (L := L)
            (TensorAlgebra.tprod R L (m + 1) a) =
          OudomGuinCircConstruct.algHomL
              (TensorAlgebra.tprod R L m (Fin.init a)) *
            SymmetricAlgebra.ι R L (a (Fin.last m)) := by
      rw [h_tprod_succ]
      show (SymmetricAlgebra.algHom R L) _ = _
      rw [map_mul]; rfl
    rw [h_algHomL_split]
    -- Apply Prop 2.8.iv at `(A ○ B, D, X)` to LHS.
    rw [circ_general_mul_ι (oudomGuinCirc (R := R) A B)
          (OudomGuinCircConstruct.algHomL
            (TensorAlgebra.tprod R L m (Fin.init a)))
          (a (Fin.last m))]
    -- Apply IH at `Fin.init a` to convert `(A ○ B) ○ D = A ○ Y_D`.
    rw [ih (Fin.init a)]
    -- LHS now: `(A ○ Y_D) ○ ι X - (A ○ B) ○ (D ○ ι X)`
    -- where `D = algHomL (tprod_m (Fin.init a))`, `X = a (Fin.last m)`,
    --       `Y_D = (mul' ∘ TP.map (○B) id)(comul D)`.
    --
    -- Apply Prop 2.8.iv rearranged at `(A, Y_D, X)` to convert
    -- `(A ○ Y_D) ○ ι X = A ○ (Y_D * ι X) + A ○ (Y_D ○ ι X)`.
    have h_AYD_ιX :
        oudomGuinCirc (R := R)
            (oudomGuinCirc (R := R) A
              ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
                  TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
                (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)
                  (OudomGuinCircConstruct.algHomL
                    (TensorAlgebra.tprod R L m (Fin.init a))))))
            (SymmetricAlgebra.ι R L (a (Fin.last m))) =
          oudomGuinCirc (R := R) A
            ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
                TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
                (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)
                  (OudomGuinCircConstruct.algHomL
                    (TensorAlgebra.tprod R L m (Fin.init a)))) *
              SymmetricAlgebra.ι R L (a (Fin.last m))) +
          oudomGuinCirc (R := R) A
            (oudomGuinCirc (R := R)
              ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
                  TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
                  (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)
                    (OudomGuinCircConstruct.algHomL
                      (TensorAlgebra.tprod R L m (Fin.init a)))))
              (SymmetricAlgebra.ι R L (a (Fin.last m)))) := by
      linear_combination -(circ_general_mul_ι (R := R) A
        ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
            TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)
            (OudomGuinCircConstruct.algHomL
              (TensorAlgebra.tprod R L m (Fin.init a)))))
        (a (Fin.last m)))
    rw [h_AYD_ιX]
    -- Bridge: `(A ○ B) ○ (D ○ ι X) = A ○ (mul' ∘ ...)(comul (D ○ ι X))`
    -- via `oudomGuinCirc_algHomL_tprod_ι` + per-summand IH + linearity.
    have h_term2 :
        oudomGuinCirc (R := R) (oudomGuinCirc (R := R) A B)
            (oudomGuinCirc (R := R)
              (OudomGuinCircConstruct.algHomL
                (TensorAlgebra.tprod R L m (Fin.init a)))
              (SymmetricAlgebra.ι R L (a (Fin.last m)))) =
          oudomGuinCirc (R := R) A
            ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
                TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
                (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)
                  (oudomGuinCirc (R := R)
                    (OudomGuinCircConstruct.algHomL
                      (TensorAlgebra.tprod R L m (Fin.init a)))
                    (SymmetricAlgebra.ι R L (a (Fin.last m)))))) := by
      rw [oudomGuinCirc_algHomL_tprod_ι (a (Fin.last m)) m (Fin.init a)]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact ih (Function.update (Fin.init a) i
        ((Fin.init a) i * a (Fin.last m)))
    rw [h_term2]
    -- Apply `compat_mul_circ_mul_ι` via `oudomGuinCirc A` + linearity.
    have h_compat := compat_mul_circ_mul_ι B
      (OudomGuinCircConstruct.algHomL
        (TensorAlgebra.tprod R L m (Fin.init a)))
      (a (Fin.last m))
    have h_compat_A := congrArg (oudomGuinCirc (R := R) A) h_compat
    simp only [map_add, map_sub] at h_compat_A
    exact h_compat_A.symm

/-- **Prop 2.8 (v)** of Oudom-Guin (2008). The inductive key for Lemma
    2.10's proof of `★` associativity.

    `(A ○ B) ○ C = A ○ ((B ○ C₍₁₎) · C₍₂₎)`, Sweedler-summed over the
    coproduct of `C`.

    Proof: lift `circ_assoc_via_comul_tprod` (per-tprod claim) via
    `algHomL_surjective` + `TA_linearMap_ext_tprod`. -/
theorem circ_assoc_via_comul (A B C : SymmetricAlgebra R L) :
    oudomGuinCirc (R := R) (oudomGuinCirc A B) C =
      oudomGuinCirc A
        ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
          TensorProduct.map (oudomGuinCirc B) LinearMap.id)
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) C)) := by
  -- Reduce to TA-side LinearMap equality via `algHomL_surjective`.
  obtain ⟨z, hz⟩ := OudomGuinCircConstruct.algHomL_surjective C
  subst hz
  -- Both sides are linear maps `TA →ₗ S(L)` evaluated at `z`.
  set f_LHS : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
    (oudomGuinCirc (R := R) (oudomGuinCirc (R := R) A B)).comp
      OudomGuinCircConstruct.algHomL with hf_LHS
  set f_RHS : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
    (oudomGuinCirc (R := R) A).comp
      ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
          TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id).comp
        ((Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)).comp
          OudomGuinCircConstruct.algHomL)) with hf_RHS
  suffices h_LM : f_LHS = f_RHS by
    have := congrArg (fun (f : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L) => f z) h_LM
    simp only [hf_LHS, hf_RHS, LinearMap.comp_apply] at this
    exact this
  -- Apply `TA_linearMap_ext_tprod` and use the per-tprod lemma.
  apply OudomGuinCircConstruct.TA_linearMap_ext_tprod
  intro n a
  simp only [hf_LHS, hf_RHS, LinearMap.comp_apply]
  exact circ_assoc_via_comul_tprod A B n a

/-! ## §5: The Oudom-Guin ★ product on `S(L)` (Q3)

Oudom-Guin (2008) Definition 2.9 defines the `★` product on `S(L)`
by `A ★ B := (A ○ B₍₁₎) · B₍₂₎`, Sweedler-summed over the coproduct.

Lemma 2.10 shows `★` is associative (and makes `(S(L), ★, Δ)` a Hopf
algebra). The proof is 6 lines of algebra using Prop 2.7.iii
(`circ_mul_distrib_via_comul`), Prop 2.8.v (`circ_assoc_via_comul`,
Q2), and cocommutativity of `Δ` (`Coalgebra.IsCocomm` — landed
sorry-free in Q1a's Bialgebra file). -/

/-- The **Oudom-Guin ★ product** on `S(L)` (Oudom-Guin 2008 Def 2.9):
    `A ★ B := (A ○ B₍₁₎) · B₍₂₎`, Sweedler-summed over `Δ(B)`. -/
noncomputable def oudomGuinStar (A B : SymmetricAlgebra R L) :
    SymmetricAlgebra R L :=
  LinearMap.mul' R (SymmetricAlgebra R L)
    (TensorProduct.map (oudomGuinCirc (R := R) A) LinearMap.id
      (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B))

/-- Notation for the Oudom-Guin ★ product. -/
scoped infix:70 " ★ " => oudomGuinStar

@[simp]
theorem oudomGuinStar_def (A B : SymmetricAlgebra R L) :
    oudomGuinStar (R := R) A B =
      LinearMap.mul' R (SymmetricAlgebra R L)
        (TensorProduct.map (oudomGuinCirc (R := R) A) LinearMap.id
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B)) :=
  rfl

/-- **LinearMap form** of `oudomGuinStar A : S(L) → S(L)`. Since `★` is
    R-linear in its second argument (definition uses `mul'`, `TP.map`,
    and `Coalgebra.comul`, all R-linear), we can promote `A ↦ A ★ ·` to
    a `LinearMap`.

    Required for TA-side lifting (`algHomL_surjective` +
    `TA_linearMap_ext_tprod`): the lift framework operates on linear
    maps `TA → S(L)`, and `oudomGuinStarL` provides the right shape. -/
noncomputable def oudomGuinStarL (A : SymmetricAlgebra R L) :
    SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
  (LinearMap.mul' R (SymmetricAlgebra R L)).comp
    ((TensorProduct.map (oudomGuinCirc (R := R) A) LinearMap.id).comp
      (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)))

@[simp]
theorem oudomGuinStarL_apply (A B : SymmetricAlgebra R L) :
    oudomGuinStarL (R := R) A B = oudomGuinStar A B := rfl

/-! ### Helpers for `oudomGuinStar_assoc`

The proof of `★`-associativity follows the OG paper p. 7 algebraic chain.
Both `(A★B)★C` and `A★(B★C)` reduce to multilinear forms in `cm B` and a
Δ³-iterate on `C`. They differ by a 2-3 swap on the 4-tensor `Δ³(C)`,
which is killed by `comul_squared_TTTC_eq` (cocommutativity in Δ³ form). -/

/-- **Helper for Q3**: `cm(B ★ C)` in explicit fused form via
    `Bialgebra.comul_mul` + `TensorProduct.map_comp`. -/
private theorem comul_oudomGuinStar_eq (B C : SymmetricAlgebra R L) :
    Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) (oudomGuinStar B C) =
      (LinearMap.mul' R (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L))
        ((TensorProduct.map
            ((Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)).comp
              (oudomGuinCirc (R := R) B))
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)))
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) C)) := by
  rw [oudomGuinStar_def B C]
  -- Push cm through mul' via AlgHom.comp_mul' on Bialgebra.comulAlgHom.
  have h_push :
      (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)).comp
          (LinearMap.mul' R (SymmetricAlgebra R L)) =
        (LinearMap.mul' R (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)).comp
          (TensorProduct.map
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))) :=
    AlgHom.comp_mul' (Bialgebra.comulAlgHom R (SymmetricAlgebra R L))
  have h_push_at := congrArg
      (fun f : (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) →ₗ[R]
                  SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L =>
        f ((TensorProduct.map (oudomGuinCirc (R := R) B) LinearMap.id)
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) C)))
      h_push
  simp only [LinearMap.coe_comp, Function.comp_apply] at h_push_at
  rw [h_push_at]
  -- Fuse the two TP.maps: TP.map cm cm ∘ TP.map (○B) id = TP.map (cm ∘ ○B) (cm ∘ id) = TP.map (cm ∘ ○B) cm
  have h_fuse := congrArg
      (fun f : (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) →ₗ[R]
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) ⊗[R]
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) =>
        f (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) C))
      (TensorProduct.map_comp
        (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
        (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
        (oudomGuinCirc (R := R) B)
        LinearMap.id)
  simp only [LinearMap.coe_comp, Function.comp_apply] at h_fuse
  rw [← h_fuse]
  -- `cm.comp id = cm`.
  rw [LinearMap.comp_id]

/-- **Helper for Q3**: `X ★ 1 = X` for any `X : S(L)`.

    Direct: `X ★ 1 = (mul' ∘ TP.map (○X) id)(cm 1) = (mul' ∘ TP.map (○X) id)(1⊗1) =
    (X ○ 1) · 1 = X · 1 = X` (via `circ_one_right` and `mul_one`). -/
theorem oudomGuinStar_one (X : SymmetricAlgebra R L) :
    oudomGuinStar X 1 = X := by
  rw [oudomGuinStar_def X 1, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearMap.mul'_apply,
      circ_one_right, mul_one]

/-- **Helper for Q3**: `★` is linear in its second argument.

    `oudomGuinStar X (Y + Z) = oudomGuinStar X Y + oudomGuinStar X Z`. -/
theorem oudomGuinStar_add_right (X Y Z : SymmetricAlgebra R L) :
    oudomGuinStar X (Y + Z) = oudomGuinStar X Y + oudomGuinStar X Z := by
  simp only [oudomGuinStar_def, map_add]

/-- **Helper for Q3**: `★` distributes over scalar multiplication in its
    second argument. -/
theorem oudomGuinStar_smul_right (X Y : SymmetricAlgebra R L) (r : R) :
    oudomGuinStar X (r • Y) = r • oudomGuinStar X Y := by
  simp only [oudomGuinStar_def, map_smul]

/-- **Left zero**: `0 ★ B = 0`. Direct from linearity of `oudomGuinCirc` in
    its first argument. -/
theorem oudomGuinStar_zero_left (B : SymmetricAlgebra R L) :
    oudomGuinStar (R := R) (0 : SymmetricAlgebra R L) B = 0 := by
  rw [oudomGuinStar_def, map_zero, TensorProduct.map_zero_left,
      LinearMap.zero_apply, map_zero]

/-- **Left additivity**: `(A₁ + A₂) ★ B = A₁ ★ B + A₂ ★ B`. Direct from
    linearity of `oudomGuinCirc` in its first argument. -/
theorem oudomGuinStar_add_left (A₁ A₂ B : SymmetricAlgebra R L) :
    oudomGuinStar (R := R) (A₁ + A₂) B =
      oudomGuinStar A₁ B + oudomGuinStar A₂ B := by
  rw [oudomGuinStar_def, oudomGuinStar_def, oudomGuinStar_def, map_add,
      TensorProduct.map_add_left, LinearMap.add_apply, map_add]

/-- **Left scalar compatibility**: `(r • A) ★ B = r • (A ★ B)`. Direct from
    linearity of `oudomGuinCirc` in its first argument. -/
theorem oudomGuinStar_smul_left (r : R) (A B : SymmetricAlgebra R L) :
    oudomGuinStar (R := R) (r • A) B = r • oudomGuinStar A B := by
  rw [oudomGuinStar_def, oudomGuinStar_def, map_smul,
      TensorProduct.map_smul_left, LinearMap.smul_apply, map_smul]

/-- **Left unit**: `1 ★ B = B`. The Bialgebra counit-comul triangle.

    `1 ★ B = mul' (TP.map (○1) id (cm B))`. Using `one_circ`,
    `○1 = algebraMap ∘ algebraMapInv` (composition of counit and unit).
    Then the LHS reduces via `Coalgebra.rTensor_counit_comul`:
    `(algebraMapInv ⊗ id) (cm B) = 1 ⊗ B`, and `mul' ∘ (algebraMap ⊗ id)
    (1 ⊗ B) = algebraMap 1 * B = 1 * B = B`. -/
theorem oudomGuinStar_one_left (B : SymmetricAlgebra R L) :
    oudomGuinStar (R := R) (1 : SymmetricAlgebra R L) B = B := by
  rw [oudomGuinStar_def]
  -- ○1 = (Algebra.linearMap R SL) ∘ algebraMapInv.toLinearMap.
  have h_circ_one : oudomGuinCirc (R := R) (1 : SymmetricAlgebra R L) =
      (Algebra.linearMap R (SymmetricAlgebra R L)).comp
        (SymmetricAlgebra.algebraMapInv (R := R) (M := L)).toLinearMap := by
    ext X
    show oudomGuinCirc (R := R) 1 X =
         (Algebra.linearMap R (SymmetricAlgebra R L))
           (SymmetricAlgebra.algebraMapInv (R := R) (M := L) X)
    rw [one_circ]
    show SymmetricAlgebra.algebraMapInv (M := L) X • (1 : SymmetricAlgebra R L) =
         algebraMap R (SymmetricAlgebra R L)
           (SymmetricAlgebra.algebraMapInv (R := R) (M := L) X)
    rw [Algebra.algebraMap_eq_smul_one]
  rw [h_circ_one]
  -- TP.map (f ∘ g) id = TP.map f id ∘ TP.map g id (TP.map_comp + map_id).
  rw [show TensorProduct.map
            ((Algebra.linearMap R (SymmetricAlgebra R L)).comp
              (SymmetricAlgebra.algebraMapInv (R := R) (M := L)).toLinearMap)
            (LinearMap.id (R := R) (M := SymmetricAlgebra R L)) =
          (TensorProduct.map (Algebra.linearMap R (SymmetricAlgebra R L))
              (LinearMap.id (R := R) (M := SymmetricAlgebra R L))).comp
            (TensorProduct.map
              (SymmetricAlgebra.algebraMapInv (R := R) (M := L)).toLinearMap
              (LinearMap.id (R := R) (M := SymmetricAlgebra R L)))
        from by rw [← TensorProduct.map_comp, LinearMap.comp_id]]
  rw [LinearMap.comp_apply]
  -- TP.map algebraMapInv id (cm B) = 1 ⊗ B via Coalgebra.rTensor_counit_comul.
  have h_counit_eq : (SymmetricAlgebra.algebraMapInv (R := R) (M := L)).toLinearMap =
                     Coalgebra.counit (R := R) (A := SymmetricAlgebra R L) := rfl
  rw [show TensorProduct.map
            (SymmetricAlgebra.algebraMapInv (R := R) (M := L)).toLinearMap
            (LinearMap.id (R := R) (M := SymmetricAlgebra R L))
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B) =
          ((1 : R) ⊗ₜ[R] B : R ⊗[R] SymmetricAlgebra R L)
        from by rw [h_counit_eq]; exact Coalgebra.rTensor_counit_comul B]
  -- TP.map algebraMap id (1 ⊗ B) = (algebraMap 1) ⊗ B = 1 ⊗ B.
  rw [TensorProduct.map_tmul, Algebra.linearMap_apply, map_one,
      LinearMap.id_coe, id_eq]
  -- mul' (1 ⊗ B) = 1 * B = B.
  rw [LinearMap.mul'_apply, one_mul]

/-- **Bilinear LinearMap form** of `★ : S(L) × S(L) → S(L)`.

    Promotes `oudomGuinStar` to a doubly-linear `S →ₗ[R] S →ₗ[R] S`. Used as
    the input to `TensorProduct.lift` to build the `(S⊗S) → S` map
    `μ_★ := TP.lift oudomGuinStarBilin`, which in turn is the building block
    for `tprodStarMul` (the ★-multiplication on the tensor product Hopf
    algebra `S⊗S`).

    Right-linearity comes for free from `oudomGuinStar`'s definition (RHS
    is `mul'`, `TP.map`, `Coalgebra.comul` — all R-linear). Left-linearity
    is witnessed by `oudomGuinStar_add_left`, `oudomGuinStar_smul_left`. -/
noncomputable def oudomGuinStarBilin :
    SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
  LinearMap.mk₂ R oudomGuinStar
    oudomGuinStar_add_left
    oudomGuinStar_smul_left
    oudomGuinStar_add_right
    (fun r A B => oudomGuinStar_smul_right A B r)

@[simp]
theorem oudomGuinStarBilin_apply (A B : SymmetricAlgebra R L) :
    oudomGuinStarBilin (R := R) A B = oudomGuinStar A B := rfl

/-- **Tensor-product ★ multiplication** on `S(L) ⊗ S(L)`. Maps a 4-tensor
    `(a ⊗ b) ⊗ (c ⊗ d)` to `(a ★ c) ⊗ (b ★ d)`.

    Constructed as `(TP.map μ_★ μ_★) ∘ TTTC` where
    `μ_★ := TP.lift oudomGuinStarBilin : (S⊗S) →ₗ[R] S`. `TTTC` reshuffles
    the 4-tensor from `(a⊗b) ⊗ (c⊗d)` to `(a⊗c) ⊗ (b⊗d)`, then the
    pointwise `μ_★` collapses each pair.

    Used to state the Hopf axiom `Δ(x ★ y) = tprodStarMul((Δx) ⊗ (Δy))`. -/
noncomputable def tprodStarMul :
    (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) ⊗[R]
    (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) →ₗ[R]
    SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L :=
  (TensorProduct.map (TensorProduct.lift (oudomGuinStarBilin (R := R) (L := L)))
                     (TensorProduct.lift (oudomGuinStarBilin (R := R) (L := L)))).comp
    (TensorProduct.tensorTensorTensorComm R
      (SymmetricAlgebra R L) (SymmetricAlgebra R L)
      (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap

@[simp]
theorem tprodStarMul_tmul (a b c d : SymmetricAlgebra R L) :
    tprodStarMul (R := R) (L := L) ((a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d)) =
      (oudomGuinStar a c) ⊗ₜ[R] (oudomGuinStar b d) := by
  simp only [tprodStarMul, LinearMap.coe_comp, Function.comp_apply,
             LinearEquiv.coe_toLinearMap,
             TensorProduct.tensorTensorTensorComm_tmul,
             TensorProduct.map_tmul, TensorProduct.lift.tmul,
             oudomGuinStarBilin_apply]

/-- **Pure-tensor canonical form helper for `tprodStarMul_eq_canon`**.

    For pure tensors `(a₁ ⊗ a₂) ⊗ (X ⊗ Y)`, the ★ pair `(a₁ ★ X)·_S ⊗ (a₂ ★ Y)·_S`
    rearranges into the canonical G-form involving `mul'_{S⊗S}` of a TTTC-shuffled
    4-tensor. Proved by double TP.induction on `X, Y` reducing to pure-tensor
    case + `Algebra.TensorProduct.tmul_mul_tmul` for the inner `mul'_{S⊗S}` rule. -/
private lemma tprodStarMul_pure_canon
    (a₁ a₂ : SymmetricAlgebra R L)
    (X Y : SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) :
    (LinearMap.mul' R (SymmetricAlgebra R L)
        ((TensorProduct.map (oudomGuinCirc (R := R) a₁) LinearMap.id) X)) ⊗ₜ[R]
    (LinearMap.mul' R (SymmetricAlgebra R L)
        ((TensorProduct.map (oudomGuinCirc (R := R) a₂) LinearMap.id) Y)) =
      LinearMap.mul' R (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
        ((TensorProduct.map
            ((TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                                (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
              ((TensorProduct.tensorTensorTensorComm R
                  (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                  (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
                ((TensorProduct.mk R
                    (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
                    (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L))
                  (a₁ ⊗ₜ[R] a₂))))
            LinearMap.id)
          ((TensorProduct.tensorTensorTensorComm R
              (SymmetricAlgebra R L) (SymmetricAlgebra R L)
              (SymmetricAlgebra R L) (SymmetricAlgebra R L)) (X ⊗ₜ[R] Y))) := by
  induction X using TensorProduct.induction_on generalizing Y with
  | zero =>
    simp only [TensorProduct.zero_tmul, map_zero, TensorProduct.tmul_zero]
  | tmul x₁ x₂ =>
    induction Y using TensorProduct.induction_on with
    | zero =>
      simp only [TensorProduct.tmul_zero, map_zero]
    | tmul y₁ y₂ =>
      simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
                 LinearMap.mul'_apply, LinearMap.comp_apply,
                 TensorProduct.mk_apply, LinearEquiv.coe_toLinearMap,
                 TensorProduct.tensorTensorTensorComm_tmul,
                 TensorProduct.lift.tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add Y₁ Y₂ ihY₁ ihY₂ =>
      simp only [TensorProduct.tmul_add, map_add, ihY₁, ihY₂]
  | add X₁ X₂ ihX₁ ihX₂ =>
    simp only [TensorProduct.add_tmul, map_add, ihX₁ Y, ihX₂ Y]

/-- **Canonical 4-tensor form helper for `comul_oudomGuinStar_mul`**.

    Expresses `tprodStarMul(a ⊗ v)` in the form needed for the cocomm-step in
    the Hopf axiom proof: a `mul'_{S⊗S}` of a TTTC-shuffled 4-tensor involving
    `(TP.map cm cm) v`. The shape matches the LHS of `comul_oudomGuinStar_mul`
    (after `comul_oudomGuinStar_eq` + `comul_circ` substitution + cocomm).

    Proved by TP.induction on `a, v` reducing to pure-tensor case + the
    `tprodStarMul_pure_canon` sub-helper. -/
private lemma tprodStarMul_eq_canon
    (a v : SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) :
    tprodStarMul (R := R) (L := L) (a ⊗ₜ[R] v) =
      LinearMap.mul' R (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
        ((TensorProduct.map
            ((TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                                (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
              ((TensorProduct.tensorTensorTensorComm R
                  (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                  (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
                ((TensorProduct.mk R
                    (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
                    (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)) a)))
            LinearMap.id)
          ((TensorProduct.tensorTensorTensorComm R
              (SymmetricAlgebra R L) (SymmetricAlgebra R L)
              (SymmetricAlgebra R L) (SymmetricAlgebra R L))
            ((TensorProduct.map
                (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
                (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))) v))) := by
  induction a using TensorProduct.induction_on generalizing v with
  | zero =>
    simp only [TensorProduct.zero_tmul, map_zero, TensorProduct.mk_apply,
               LinearMap.comp_zero, TensorProduct.map_zero_left,
               LinearMap.zero_apply]
  | tmul a₁ a₂ =>
    induction v using TensorProduct.induction_on with
    | zero =>
      simp only [TensorProduct.tmul_zero, map_zero, TensorProduct.zero_tmul,
                 LinearMap.zero_apply]
    | tmul v₁ v₂ =>
      rw [tprodStarMul_tmul, oudomGuinStar_def, oudomGuinStar_def,
          TensorProduct.map_tmul]
      exact tprodStarMul_pure_canon a₁ a₂
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) v₁)
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) v₂)
    | add v₁ v₂ ihv₁ ihv₂ =>
      simp only [TensorProduct.tmul_add, map_add, ihv₁, ihv₂]
  | add a₁ a₂ iha₁ iha₂ =>
    simp only [TensorProduct.add_tmul, map_add, iha₁ v, iha₂ v,
               LinearMap.map_add, LinearMap.add_comp, LinearMap.comp_add,
               TensorProduct.map_add_left, LinearMap.add_apply]

theorem comul_oudomGuinStar_mul (x y : SymmetricAlgebra R L) :
    Coalgebra.comul (R := R) (oudomGuinStar x y) =
      tprodStarMul (R := R) (L := L)
        (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) x ⊗ₜ[R]
         Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) y) := by
  -- Step 1: rewrite LHS via comul_oudomGuinStar_eq.
  rw [comul_oudomGuinStar_eq]
  -- Step 2: rewrite RHS via tprodStarMul_eq_canon to expose TTTC at Δ²y.
  rw [tprodStarMul_eq_canon]
  -- Step 3: cocomm — TTTC fixes Δ²y, so we can drop it.
  have h_cocomm := congrArg
      (fun (f : SymmetricAlgebra R L →ₗ[R]
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) ⊗[R]
                  (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)) => f y)
      comul_squared_TTTC_eq
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h_cocomm
  rw [h_cocomm]
  -- Goal: mul'((TP.map (cm.comp(○x)) cm)(cm y)) =
  --       mul'((TP.map (G(cm x)) id)((TP.map cm cm)(cm y)))
  -- Step 4: factor LHS via comul_circ in LinearMap form + TP.map_comp.
  have h_cmcc_x_lm :
      (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)).comp
          (oudomGuinCirc (R := R) x) =
        ((TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                            (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
          ((TensorProduct.tensorTensorTensorComm R
              (SymmetricAlgebra R L) (SymmetricAlgebra R L)
              (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
            ((TensorProduct.mk R
                (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
                (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L))
              (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) x)))).comp
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)) := by
    ext B'
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply,
               LinearEquiv.coe_toLinearMap]
    rw [comul_circ x B', TensorProduct.map_tmul]
  rw [h_cmcc_x_lm]
  -- Goal: mul'((TP.map (G_x.comp cm) cm)(cm y)) =
  --       mul'((TP.map G_x id)((TP.map cm cm)(cm y)))
  -- where G_x := (TP.map μ μ).comp(TTTC.comp(mk (cm x))).
  -- By TP.map_comp: TP.map (G_x.comp cm) cm = (TP.map G_x id).comp(TP.map cm cm).
  set G_x :=
    (TensorProduct.map (TensorProduct.lift (oudomGuinCirc (R := R)))
                       (TensorProduct.lift (oudomGuinCirc (R := R)))).comp
      ((TensorProduct.tensorTensorTensorComm R
          (SymmetricAlgebra R L) (SymmetricAlgebra R L)
          (SymmetricAlgebra R L) (SymmetricAlgebra R L)).toLinearMap.comp
        ((TensorProduct.mk R
            (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L)
            (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L))
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) x)))
    with hG_x
  have h_factor :
      TensorProduct.map (G_x.comp
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)))
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L)) =
        (TensorProduct.map G_x LinearMap.id).comp
          (TensorProduct.map
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L))) := by
    rw [← TensorProduct.map_comp, LinearMap.id_comp]
  rw [h_factor]
  simp only [LinearMap.comp_apply]

/-- **Counit-multiplicativity for `★`**: `ε(A ★ B) = ε(A) · ε(B)`.

    Direct analog of `counit_circ` (counit-multiplicativity for `○`), and a
    consequence of `(S(L), ★, Δ)` being a Hopf algebra (OG Lemma 2.10).

    Strategy: no induction on `A` needed (unlike `counit_circ`). `★` is defined
    via `mul'`, `TP.map (○A) id`, and `cm`. Push `ε` through `mul'` via
    `AlgHom.comp_mul'`; fuse the nested `TP.map`s via `TP.map_comp`; substitute
    `ε ∘ₗ ○A = ε A • ε` via `counit_circ` in linear-map form; pull the scalar
    out of `TP.map`, then through `mul'`; close via `mul'_map_algebraMapInv_comul`
    (the counit-comul triangle).

    Independent value: required for the Q5c pairing-route closure (z = 1 base
    case of `gl_product_eq_oudomGuinStar_via_pairing` reduces to this). -/
theorem counit_oudomGuinStar (A B : SymmetricAlgebra R L) :
    SymmetricAlgebra.algebraMapInv (M := L) (oudomGuinStar (R := R) A B) =
      (SymmetricAlgebra.algebraMapInv (M := L) A) *
      (SymmetricAlgebra.algebraMapInv (M := L) B) := by
  rw [oudomGuinStar_def]
  -- Step 1: push ε through `mul'` via `AlgHom.comp_mul'`.
  have h_push := congrArg
      (fun (f : (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) →ₗ[R] R) =>
        f ((TensorProduct.map (oudomGuinCirc (R := R) A) LinearMap.id)
            (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B)))
      (AlgHom.comp_mul' (SymmetricAlgebra.algebraMapInv (M := L)))
  simp only [LinearMap.coe_comp, Function.comp_apply,
             AlgHom.toLinearMap_apply] at h_push
  rw [h_push]
  -- Step 2: fuse the two `TP.map`s; simplify `ε ∘ₗ id = ε`.
  have h_fuse := congrArg
    (fun (f : (SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) →ₗ[R] R ⊗[R] R) =>
      f (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B))
    (TensorProduct.map_comp
      (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap
      (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap
      (oudomGuinCirc (R := R) A)
      LinearMap.id)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.comp_id]
    at h_fuse
  rw [← h_fuse]
  -- Step 3: substitute `ε ∘ₗ ○A = ε A • ε` via `counit_circ` in LM form.
  rw [show (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap.comp
          (oudomGuinCirc (R := R) A) =
        (SymmetricAlgebra.algebraMapInv (M := L) A) •
          (SymmetricAlgebra.algebraMapInv (M := L)).toLinearMap from by
    ext B'
    simp only [LinearMap.comp_apply, LinearMap.smul_apply,
               AlgHom.toLinearMap_apply, smul_eq_mul]
    exact counit_circ A B']
  -- Step 4: pull the scalar out and close via the counit-comul triangle.
  rw [TensorProduct.map_smul_left, LinearMap.smul_apply, map_smul,
      mul'_map_algebraMapInv_comul, smul_eq_mul]

/-- **Helper for Q3 (ι T split)**: For any `X : S(L)` and `T : L`:
    `X ★ ι T = X ○ ι T + X · ι T`.

    Direct: unfold `X ★ ι T = mul'(TP.map (○X) id (cm ι T))` with primitive
    `cm ι T = ι T ⊗ 1 + 1 ⊗ ι T`, distribute, apply `circ_one_right` and
    `mul_one`. -/
theorem oudomGuinStar_ι_split (X : SymmetricAlgebra R L) (T : L) :
    oudomGuinStar X (SymmetricAlgebra.ι R L T) =
      oudomGuinCirc X (SymmetricAlgebra.ι R L T) + X * SymmetricAlgebra.ι R L T := by
  rw [oudomGuinStar_def X (SymmetricAlgebra.ι R L T)]
  simp only [SymmetricAlgebra.comul_ι, map_add, TensorProduct.map_tmul,
             LinearMap.id_coe, id_eq, LinearMap.mul'_apply, mul_one, circ_one_right]

/-- **Closed-form identity** for `Z ★ (X · ι T)`. Key for closing Q3's per-tprod
    `succ m` case.

    `Z ★ (X · ι T) = (Z ★ X) ○ ι T + (Z ★ X) · ι T - Z ★ (X ○ ι T)`.

    Derived by Sweedler bash on `cm X`: expand `cm(X·ιT) = cm X · cm(ιT)`,
    apply 3.9.iv (`circ_general_mul_ι`) on the `Z ○ (x₁·ιT)` summand, then
    identify the residual sums via 2.7.iii applied to `(Z★X)○ιT` and
    `comul_circ` applied to `Z★(X○ιT)`. The TP-induction on `cm X` is
    sound because both sides are linear in `cm X` (the structural
    relationship between `X` and `cm X` is irrelevant once both sides are
    expanded — they're equal as functions of `cm X` for ANY tensor).

    This identity expresses `Z★(X·ιT)` in terms of `Z★X` and `X○ιT`. In
    per-tprod context with `X = D = algHomL(tprod m a')`, `X ○ ι T` is a
    sum of tprods at the same `m` (via `oudomGuinCirc_algHomL_tprod_ι`),
    so Q3's m+1 case reduces to Q3 at m by linearity in C — no Sweedler
    cocomm bash needed at all. -/
theorem oudomGuinStar_mul_ι_split
    (Z X : SymmetricAlgebra R L) (T : L) :
    oudomGuinStar Z (X * SymmetricAlgebra.ι R L T) =
      oudomGuinCirc (oudomGuinStar Z X) (SymmetricAlgebra.ι R L T) +
      oudomGuinStar Z X * SymmetricAlgebra.ι R L T -
      oudomGuinStar Z (oudomGuinCirc X (SymmetricAlgebra.ι R L T)) := by
  -- Expand all four ★ occurrences + cm(X·ιT), cm(X○ιT) via the substrate
  -- lemmas, exposing `cm X` in all summands.
  rw [oudomGuinStar_def Z (X * SymmetricAlgebra.ι R L T),
      oudomGuinStar_def Z X,
      oudomGuinStar_def Z (oudomGuinCirc X (SymmetricAlgebra.ι R L T)),
      Bialgebra.comul_mul X (SymmetricAlgebra.ι R L T),
      comul_circ X (SymmetricAlgebra.ι R L T),
      TensorProduct.map_tmul,
      SymmetricAlgebra.comul_ι R L T]
  -- Generalize cm X → cmX and induct.
  generalize Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) X = cmX
  induction cmX using TensorProduct.induction_on with
  | zero =>
    simp only [zero_mul, map_zero, LinearMap.zero_apply,
               TensorProduct.zero_tmul, mul_zero, sub_zero,
               add_zero, sub_self, zero_add]
  | tmul x₁ x₂ =>
    -- Distribute (x₁⊗x₂) · (ιT⊗1 + 1⊗ιT) = (x₁·ιT)⊗x₂ + x₁⊗(x₂·ιT).
    rw [show (x₁ ⊗ₜ[R] x₂ :
             SymmetricAlgebra R L ⊗[R] SymmetricAlgebra R L) *
            (SymmetricAlgebra.ι R L T ⊗ₜ[R] (1 : SymmetricAlgebra R L) +
             (1 : SymmetricAlgebra R L) ⊗ₜ[R] SymmetricAlgebra.ι R L T) =
          (x₁ * SymmetricAlgebra.ι R L T) ⊗ₜ[R] x₂ +
          x₁ ⊗ₜ[R] (x₂ * SymmetricAlgebra.ι R L T) from by
        rw [mul_add, Algebra.TensorProduct.tmul_mul_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]]
    -- Distribute TTTC ((x₁⊗x₂) ⊗ (ιT⊗1 + 1⊗ιT)) on RHS₃ term.
    rw [show (TensorProduct.tensorTensorTensorComm R
                (SymmetricAlgebra R L) (SymmetricAlgebra R L)
                (SymmetricAlgebra R L) (SymmetricAlgebra R L))
              ((x₁ ⊗ₜ[R] x₂) ⊗ₜ[R]
                (SymmetricAlgebra.ι R L T ⊗ₜ[R] (1 : SymmetricAlgebra R L) +
                 (1 : SymmetricAlgebra R L) ⊗ₜ[R] SymmetricAlgebra.ι R L T)) =
          (x₁ ⊗ₜ[R] SymmetricAlgebra.ι R L T) ⊗ₜ[R]
            (x₂ ⊗ₜ[R] (1 : SymmetricAlgebra R L)) +
          (x₁ ⊗ₜ[R] (1 : SymmetricAlgebra R L)) ⊗ₜ[R]
            (x₂ ⊗ₜ[R] SymmetricAlgebra.ι R L T) from by
        rw [TensorProduct.tmul_add, map_add,
            TensorProduct.tensorTensorTensorComm_tmul,
            TensorProduct.tensorTensorTensorComm_tmul]]
    -- Reduce pure tensors via TP.map, lift.tmul, mul'_apply, circ_one_right.
    simp only [map_add, TensorProduct.map_tmul, TensorProduct.lift.tmul,
               LinearMap.mul'_apply, LinearMap.id_coe, id_eq, circ_one_right]
    -- Apply 2.7.iii on the first RHS term ((Z○x₁)·x₂)○ιT.
    rw [circ_mul_distrib_via_comul (oudomGuinCirc Z x₁) x₂
          (SymmetricAlgebra.ι R L T)]
    simp only [LinearMap.coe_comp, Function.comp_apply,
               SymmetricAlgebra.comul_ι, map_add, TensorProduct.map_tmul,
               LinearMap.mul'_apply, circ_one_right]
    -- Apply 3.9.iv at (Z, x₁, T): Z○(x₁·ιT) = (Z○x₁)○ιT - Z○(x₁○ιT).
    rw [circ_general_mul_ι Z x₁ T]
    -- Close by ring.
    ring
  | add a b iha ihb =>
    -- Linearity: distribute through both sides and combine IHs.
    simp only [add_mul, TensorProduct.add_tmul, map_add,
               LinearMap.add_apply, mul_add] at iha ihb ⊢
    linear_combination iha + ihb

/-- **Per-tprod form** of Lemma 2.10. Proves `(A★B) ★ algHomL(tprod m a) =
    A ★ (B ★ algHomL(tprod m a))` by induction on `m`.

    Lifted to the full `oudomGuinStar_assoc` via `algHomL_surjective` +
    `TA_linearMap_ext_tprod` (mirrors Q2's `circ_assoc_via_comul_tprod`
    structure).

    Proof:
    - `m = 0` (`tprod_0 = 1`): both sides equal `A ★ B` via
      `oudomGuinStar_one` applied twice.
    - `m + 1` (`tprod_{m+1} a = tprod_m (Fin.init a) * ι (a (Fin.last m))`):
      Let `D = algHomL(tprod m init)`, `X = a(last)`. Apply
      `oudomGuinStar_mul_ι_split` three times (once to LHS, twice to
      decompose RHS), apply IH at `Fin.init a` to close `(A★B)★D` →
      `A★(B★D)`, and reduce the residual difference to
      `(A★B)★(D○ιX) - A★(B★(D○ιX))`. By `oudomGuinCirc_algHomL_tprod_ι`,
      `D ○ ι X = Σᵢ algHomL(tprod m (update init i (init i * X)))` — a
      sum of m tprods at the SAME m. By IH (universally quantified over
      `a`) applied to each summand, plus linearity of both sides of Q3
      in `C`, the residual difference vanishes. -/
private theorem oudomGuinStar_assoc_tprod (A B : SymmetricAlgebra R L) :
    ∀ (m : ℕ) (a : Fin m → L),
      oudomGuinStar (oudomGuinStar A B)
          (OudomGuinCircConstruct.algHomL (TensorAlgebra.tprod R L m a)) =
        oudomGuinStar A (oudomGuinStar B
          (OudomGuinCircConstruct.algHomL (TensorAlgebra.tprod R L m a))) := by
  intro m
  induction m with
  | zero =>
    intro a
    -- `tprod_0 a = 1` in TA; `algHomL 1 = 1` in S(L).
    have h_tprod0 : TensorAlgebra.tprod R L 0 a = 1 := by
      rw [TensorAlgebra.tprod_apply]; simp [List.ofFn_zero]
    rw [h_tprod0,
        show OudomGuinCircConstruct.algHomL (R := R) (L := L)
              (1 : TensorAlgebra R L) = (1 : SymmetricAlgebra R L) from
          map_one (SymmetricAlgebra.algHom R L)]
    -- Both sides = A ★ B via `oudomGuinStar_one` (twice on RHS, once on LHS).
    rw [oudomGuinStar_one, oudomGuinStar_one]
  | succ m ih =>
    intro a
    -- Decompose `tprod_{m+1} a = tprod_m (Fin.init a) * ι (a (Fin.last m))`.
    have h_a_eq : a = Fin.snoc (Fin.init a) (a (Fin.last m)) :=
      (Fin.snoc_init_self a).symm
    have h_tprod_succ :
        TensorAlgebra.tprod R L (m + 1) a =
        TensorAlgebra.tprod R L m (Fin.init a) *
          TensorAlgebra.ι R (a (Fin.last m)) := by
      conv_lhs => rw [h_a_eq]
      rw [Fin.snoc_eq_append,
          OudomGuinCircConstruct.ι_eq_tprod_one,
          ← OudomGuinCircConstruct.tprod_mul_tprod]
      congr 1
    have h_algHomL_split :
        OudomGuinCircConstruct.algHomL (R := R) (L := L)
            (TensorAlgebra.tprod R L (m + 1) a) =
          OudomGuinCircConstruct.algHomL
              (TensorAlgebra.tprod R L m (Fin.init a)) *
            SymmetricAlgebra.ι R L (a (Fin.last m)) := by
      rw [h_tprod_succ]
      show (SymmetricAlgebra.algHom R L) _ = _
      rw [map_mul]; rfl
    rw [h_algHomL_split]
    -- Let D = algHomL(tprod m init), X = a(last).
    set D : SymmetricAlgebra R L :=
      OudomGuinCircConstruct.algHomL (TensorAlgebra.tprod R L m (Fin.init a))
      with hD
    set X : L := a (Fin.last m) with hX
    -- Linearity of `oudomGuinStar Z` in 2nd arg (over add, sub, and finite sums)
    -- via the LinearMap form `oudomGuinStarL`.
    have h_star_sub : ∀ Z u v : SymmetricAlgebra R L,
        oudomGuinStar Z (u - v) = oudomGuinStar Z u - oudomGuinStar Z v := by
      intro Z u v
      rw [← oudomGuinStarL_apply Z u, ← oudomGuinStarL_apply Z v,
          ← oudomGuinStarL_apply Z (u - v), map_sub]
    have h_star_sum : ∀ Z : SymmetricAlgebra R L, ∀ (f : Fin m → SymmetricAlgebra R L),
        oudomGuinStar Z (∑ i, f i) = ∑ i, oudomGuinStar Z (f i) := by
      intro Z f
      rw [← oudomGuinStarL_apply Z _, map_sum]
      simp only [oudomGuinStarL_apply]
    -- Compute `D ○ ι X` as a finite sum of tprods at the same `m`
    -- (via `oudomGuinCirc_algHomL_tprod_ι`).
    have h_DcircιX :
        oudomGuinCirc D (SymmetricAlgebra.ι R L X) =
          ∑ i : Fin m,
            OudomGuinCircConstruct.algHomL
              (TensorAlgebra.tprod R L m
                (Function.update (Fin.init a) i (Fin.init a i * X))) := by
      rw [hD]
      exact oudomGuinCirc_algHomL_tprod_ι X m (Fin.init a)
    -- Q3 holds at `D ○ ι X` by IH-summand-wise + linearity.
    have h_Q3_DcircιX :
        oudomGuinStar (oudomGuinStar A B) (oudomGuinCirc D (SymmetricAlgebra.ι R L X)) =
          oudomGuinStar A (oudomGuinStar B
            (oudomGuinCirc D (SymmetricAlgebra.ι R L X))) := by
      rw [h_DcircιX, h_star_sum (oudomGuinStar A B), h_star_sum B, h_star_sum A]
      apply Finset.sum_congr rfl
      intro i _
      exact ih (Function.update (Fin.init a) i (Fin.init a i * X))
    -- LHS via split + IH(D)
    have h_LHS :
        oudomGuinStar (oudomGuinStar A B) (D * SymmetricAlgebra.ι R L X) =
          oudomGuinCirc (oudomGuinStar A (oudomGuinStar B D))
              (SymmetricAlgebra.ι R L X) +
          oudomGuinStar A (oudomGuinStar B D) * SymmetricAlgebra.ι R L X -
          oudomGuinStar (oudomGuinStar A B) (oudomGuinCirc D (SymmetricAlgebra.ι R L X)) := by
      rw [oudomGuinStar_mul_ι_split (oudomGuinStar A B) D X, ih (Fin.init a)]
    -- RHS via split (on B's side), linearity, then split (on A's side).
    have h_RHS :
        oudomGuinStar A (oudomGuinStar B (D * SymmetricAlgebra.ι R L X)) =
          oudomGuinCirc (oudomGuinStar A (oudomGuinStar B D))
              (SymmetricAlgebra.ι R L X) +
          oudomGuinStar A (oudomGuinStar B D) * SymmetricAlgebra.ι R L X -
          oudomGuinStar A (oudomGuinStar B
            (oudomGuinCirc D (SymmetricAlgebra.ι R L X))) := by
      rw [oudomGuinStar_mul_ι_split B D X]
      rw [show oudomGuinStar A
                (oudomGuinCirc (oudomGuinStar B D) (SymmetricAlgebra.ι R L X) +
                  oudomGuinStar B D * SymmetricAlgebra.ι R L X -
                  oudomGuinStar B (oudomGuinCirc D (SymmetricAlgebra.ι R L X))) =
              oudomGuinStar A
                  (oudomGuinCirc (oudomGuinStar B D) (SymmetricAlgebra.ι R L X) +
                    oudomGuinStar B D * SymmetricAlgebra.ι R L X) -
              oudomGuinStar A
                  (oudomGuinStar B (oudomGuinCirc D (SymmetricAlgebra.ι R L X))) from
            h_star_sub A _ _]
      rw [oudomGuinStar_add_right A _ _]
      rw [oudomGuinStar_mul_ι_split A (oudomGuinStar B D) X]
      ring
    rw [h_LHS, h_RHS, h_Q3_DcircιX]

/-- **Oudom-Guin Lemma 2.10**: the `★` product is associative.

    Lifted from per-tprod (`oudomGuinStar_assoc_tprod`) via
    `algHomL_surjective` + `TA_linearMap_ext_tprod`. Mirrors Q2's
    lifting pattern (`circ_assoc_via_comul`).

    Both sides are R-linear maps in `C`, so checking on tprods suffices.

    Note: the previous proof structure used `SymmetricAlgebra.induction`
    on `C` with `algebraMap r`, `ι T`, `add`, `mul` cases. The first
    three closed sorry-free; the `mul X Y` case had no closed-form
    decomposition (the IHs for X and Y don't compose multiplicatively
    via ★, and TP-induction on `cm(X·Y)` is unsound — counterexample:
    `A = ι T, B = 1, cmC' = ι X ⊗ ι Y` gives LHS = ι(T·X)·ι Y ≠ 0 = RHS).
    The per-tprod approach gives a cleaner structural induction where
    each m+1 step adds exactly one ι generator. -/
theorem oudomGuinStar_assoc (A B C : SymmetricAlgebra R L) :
    oudomGuinStar (oudomGuinStar A B) C = oudomGuinStar A (oudomGuinStar B C) := by
  -- Reduce to TA-side LinearMap equality via `algHomL_surjective`.
  obtain ⟨z, hz⟩ := OudomGuinCircConstruct.algHomL_surjective C
  subst hz
  -- Both sides are R-linear maps `TA →ₗ S(L)` at `z`.
  set f_LHS : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
    (oudomGuinStarL (R := R) (oudomGuinStar A B)).comp
      OudomGuinCircConstruct.algHomL with hf_LHS
  set f_RHS : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
    ((oudomGuinStarL (R := R) A).comp (oudomGuinStarL (R := R) B)).comp
      OudomGuinCircConstruct.algHomL with hf_RHS
  suffices h_LM : f_LHS = f_RHS by
    have := congrArg (fun (f : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L) => f z) h_LM
    simp only [hf_LHS, hf_RHS, LinearMap.comp_apply, oudomGuinStarL_apply] at this
    exact this
  -- Apply `TA_linearMap_ext_tprod` and use the per-tprod lemma.
  apply OudomGuinCircConstruct.TA_linearMap_ext_tprod
  intro m a
  simp only [hf_LHS, hf_RHS, LinearMap.comp_apply, oudomGuinStarL_apply]
  exact oudomGuinStar_assoc_tprod A B m a

end OudomGuinCirc

end PreLie
