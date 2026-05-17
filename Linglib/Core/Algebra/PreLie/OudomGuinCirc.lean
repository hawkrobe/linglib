/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.PreLie.GuinOudom
import Linglib.Core.Algebra.PreLie.OudomGuinCircTotal
import Linglib.Core.RingTheory.Bialgebra.SymmetricAlgebra
import Linglib.Core.RingTheory.Coalgebra.Convolution
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

set_option autoImplicit false

/-!
# The Oudom-Guin ○ operation on `SymmetricAlgebra R L`
@cite{oudom-guin-2008}

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
(`LinearMap.convAlgebra` in `Linglib.Core.RingTheory.Coalgebra.Convolution`)
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

* @cite{oudom-guin-2008} — original construction, §2.
* @cite{manchon-2011} — survey, Theorem 1.1 (Manchon route, alternative).
* @cite{chapoton-livernet-2001} — free pre-Lie algebra = rooted trees.

## Convention

Right pre-Lie (`RightPreLieAlgebra` from Tapia 2025), matching
`GuinOudom.lean`. Pre-Lie product written as `*` on `L`. Oudom-Guin's
`○` notation is reserved for the extension to `S(L)`.
-/

namespace PreLie

namespace OudomGuinCirc

open WithConv
open scoped TensorProduct

variable {R : Type} [CommRing R]
variable {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]

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
uniquely characterize `○`. We state each as a theorem. With the
construction sorry-fenced, these are also sorry-fenced (they witness
that the construction satisfies the defining equations). -/

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
private theorem oudomGuinCirc_mul_ι (A B : SymmetricAlgebra R L) (X : L) :
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
    + `comul_ι` + `circ_one_right` + `circ_ι_ι`. -/
private theorem oudomGuinCirc_algHomL_tprod_ι (X : L) :
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

/-! **Prop 2.8 (iii)**: `Δ` commutes with `○` — `Δ(A ○ B) = Σ (A₍₁₎ ○ B₍₁₎)
⊗ (A₍₂₎ ○ B₍₂₎)`, Sweedler-summed over both coproducts.

This is the OG paper's Sweedler identity used in Prop 2.8.v's `mul` case
to identify LHS and RHS expansions; combined with `IsCocomm`
(cocommutativity, now available from
`Linglib/Core/RingTheory/Bialgebra/SymmetricAlgebra.lean`) to swap inner
indexing.

**Lean statement deferred** pending the right mathlib idiom for the
4-fold tensor reshuffling `(S⊗S) ⊗ (S⊗S) → S⊗S`. The natural form would
be:

```
Coalgebra.comul (A ○ B) =
  (TensorProduct.map oudomGuinCirc oudomGuinCirc).comp
    (Algebra.TensorProduct.tensorTensorTensorComm ...).comp
    ... (Coalgebra.comul A, Coalgebra.comul B)
```

but mathlib's `tensorTensorTensorComm` is in `TensorProduct.AssocLeft`
or similar and the exact composition needs care. Future cleanup. -/

/-! ## §4: Prop 2.8.v — the key inductive lemma

`(A ○ B) ○ C = A ○ ((B ○ C₍₁₎) · C₍₂₎)`. Proved by induction on the
length of `A` (Oudom-Guin paper page 7).

This is THE substantive lemma needed for Lemma 2.10's proof of `★`
associativity.

### Proof structure (per OG paper p. 7)

By `SymmetricAlgebra.induction` on `A`:

- **`algebraMap r` (rank 0, A = r · 1)**: both sides reduce to
  `r · ε(B) · ε(C) · 1` via `one_circ` (Prop 2.8.i), `counit_circ`
  (Prop 2.8.ii), and the counit law `ε(C₍₁₎) · ε(C₍₂₎) = ε(C)`.

- **`ι T` (rank 1, A = ι(T) for T ∈ L)**: the rank-1 OG identity. By
  Def 2.4 + Prop 2.7.ii (`circ_T_mul`), inductive on B's length. This
  is the deepest sub-case; depends on the construction of
  `oudomGuinCirc` at `T ∈ L`.

- **`mul A₁ A₂` (with IH on both)**: OG's main chain (p. 7):
  ```
  ((A₁ * A₂) ○ B) ○ C
    = ((A₁ ○ B₍₁₎)(A₂ ○ B₍₂₎)) ○ C         [Prop 2.7.iii]
    = ((A₁ ○ B₍₁₎) ○ C₍₁₎)((A₂ ○ B₍₂₎) ○ C₍₂₎)  [Prop 2.7.iii again]
    = (A₁ ○ ((B₍₁₎ ○ C₍₁₎₍₁₎) C₍₁₎₍₂₎))(A₂ ○ ((B₍₂₎ ○ C₍₂₎₍₁₎) C₍₂₎₍₂₎))  [IH]
    = (A₁ * A₂) ○ ((B ○ C₍₁₎) C₍₂₎)         [Prop 2.7.iii reversed + Δ identity]
  ```
  The final step uses Prop 2.8.iii (`comul_circ`) + `IsCocomm`:
  `Δ((C ○ D₁)D₂) = (C₁ ○ D₁)D₂ ⊗ (C₂ ○ D₃)D₄` after cocommutative
  reindexing.

- **`add A₁ A₂` (with IH on both)**: linearity of `oudomGuinCirc`. -/

/-- **Prop 2.8 (v)** of Oudom-Guin (2008). The inductive key for Lemma
    2.10's proof of `★` associativity.

    `(A ○ B) ○ C = A ○ ((B ○ C₍₁₎) · C₍₂₎)`, Sweedler-summed over the
    coproduct of `C`. -/
theorem circ_assoc_via_comul (A B C : SymmetricAlgebra R L) :
    oudomGuinCirc (R := R) (oudomGuinCirc A B) C =
      oudomGuinCirc A
        ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
          TensorProduct.map (oudomGuinCirc B) LinearMap.id)
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) C)) := by
  -- See proof structure docstring above. Each induction case is its own
  -- sub-sorry — modular when `oudomGuinCirc` (Q1b) and Prop 2.7.iii
  -- (`circ_mul_distrib_via_comul`) are constructed.
  induction A using SymmetricAlgebra.induction with
  | algebraMap r =>
    -- A = r · 1. Both sides reduce to `r · ε(B) · ε(C) · 1` via
    -- one_circ, counit_circ, and the counit law `ε(C₁)·ε(C₂) = ε(C)`.
    sorry
  | ι T =>
    -- A = ι(T) for T ∈ L. Rank-1 OG identity. Inductive on B's length
    -- using Prop 2.7.ii (`circ_T_mul`). Deepest sub-case.
    sorry
  | mul A₁ A₂ ih₁ ih₂ =>
    -- A = A₁ * A₂. Main chain from OG p. 7: uses Prop 2.7.iii (twice)
    -- + IH on A₁ and A₂ + Prop 2.8.iii (`comul_circ`) + `IsCocomm`.
    sorry
  | add A₁ A₂ ih₁ ih₂ =>
    -- Linearity of `oudomGuinCirc` in the first argument.
    simp only [map_add, LinearMap.add_apply]
    rw [ih₁, ih₂]

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

/-- **Oudom-Guin Lemma 2.10**: the `★` product is associative.

    Proof structure (6-line algebraic chain from OG paper p. 7):
    ```
    (A ★ B) ★ C
      = (((A ○ B₁) · B₂) ○ C₁) · C₂                [def of ★]
      = ((A ○ B₁) ○ C₁) · (B₂ ○ C₂) · C₃          [Prop 2.7.iii]
      = (A ○ ((B₁ ○ C₁) · C₂)) · (B₂ ○ C₃) · C₄   [Prop 2.8.v / Q2]
      = (A ○ ((B₁ ○ C₁) · C₃)) · (B₂ ○ C₂) · C₄   [cocomm of Δ — Q1a]
      = A ★ ((B ○ C₁) · C₂)                        [def of ★ + Prop 2.7.iii]
      = A ★ (B ★ C)                                [def of ★]
    ```

    Sorry-fenced: depends on `circ_mul_distrib_via_comul` (Prop 2.7.iii)
    and `circ_assoc_via_comul` (Prop 2.8.v / Q2). Both are sorry'd
    pending the construction of `oudomGuinCirc` (Q1b). Once Q1b lands,
    the 6-line chain becomes concrete Sweedler manipulations
    (~50-100 LOC in Lean, given Lean's verbosity with TensorProduct). -/
theorem oudomGuinStar_assoc (A B C : SymmetricAlgebra R L) :
    oudomGuinStar (oudomGuinStar A B) C = oudomGuinStar A (oudomGuinStar B C) := by
  sorry

end OudomGuinCirc

end PreLie
