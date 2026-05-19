/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar
import Mathlib.RingTheory.Coalgebra.Convolution

set_option autoImplicit false

/-!
# Insertion Lie algebra ≅ primitives in the dual Hopf algebra (MCB Lemma 1.7.3)
@cite{marcolli-chomsky-berwick-2025}

The architectural payoff of Phase E.3 (R.5–R.9): the GL/CK duality
framework is designed precisely to make MCB Lemma 1.7.3 expressible.

> **MCB Lemma 1.7.3** (book p. 78): The insertion Lie algebra of
> Lemma 1.7.2 is the Lie algebra of primitive elements in the dual
> Hopf algebra of the Hopf algebra of workspaces.

Proof sketch (book p. 79): take dual basis `δ_F` (delta on forests);
primitives in `H^∨` are the `δ_T` (single-tree only); the dual product
`δ_{T_1} ⋆ δ_{T_2}` expands as `Σ_T c^T_{T_1,T_2} δ_T` where
`c^T_{T_1,T_2}` counts insertions; the Lie bracket on primitives
matches the insertion bracket from §1.7.2.

## Substrate (general, mathlib upstream candidate)

* `Bialgebra.IsDualPrimitive` — a linear functional `L : H →ₗ[R] R` is
  "primitive in the dual" iff `L(xy) = L(x)·ε(y) + ε(x)·L(y)`. Equivalent
  to being primitive in `H^∨` viewed as a coalgebra dual to `H`'s algebra.
* `Bialgebra.dualPrimitives` — the submodule of dual primitives.
* `Bialgebra.convBracket` — the convolution Lie bracket
  `[L₁, L₂] := L₁ ⋆ L₂ - L₂ ⋆ L₁` using mathlib's `WithConv`.

These are sorry-free general lemmas; potential mathlib upstream.

## Specialization to Connes-Kreimer

* `deltaSingleton T` — the dual basis element `δ_T : CK R (Nonplanar α)
  →ₗ[R] R` extracting the coefficient of the singleton forest `{T}`.
* `deltaSingleton_isDualPrimitive` — `δ_T` is a dual primitive. **Sorry**;
  proof requires direct computation from `comulAlgHomN`'s coproduct
  structure (single-tree forests pair only with single-cut summands).
* `mcb_lemma_1_7_3` — the convolution Lie bracket of two single-tree
  deltas. **Sorry**; full proof requires the combinatorial bijection
  from book Figure 1.6, plus R.5.5 (`GrossmanLarson.mul_assoc_basis`)
  and R.7 (`pairing_gl_eq_pairing_coproduct_C`) sorry-free.

## What this file does NOT do

* Does not formalize the 1-α quotient (would make `H` a genuine
  connected Hopf algebra; not needed for the statement on the bialgebra).
* Does not state a full Lie algebra isomorphism between the insertion
  Lie algebra and dual primitives (only the per-pair bracket identity).
* Does not close the deep combinatorial proofs.

## Status

`[UPSTREAM]` candidate for the `Bialgebra.IsDualPrimitive` /
`dualPrimitives` / `convBracket` substrate (sorry-free).

`mcb_lemma_1_7_3` is sorry-fenced; statement is the load-bearing
API for downstream consumers.
-/

namespace Bialgebra

open scoped TensorProduct
open Coalgebra

/-! ## §1: Dual primitives — general Bialgebra substrate -/

variable {R : Type*} [CommSemiring R] {H : Type*} [Semiring H] [Bialgebra R H]

/-- A linear functional `L : H →ₗ[R] R` is **primitive in the dual** of
    a bialgebra `H` if it satisfies the derivation-like identity:
    `L(x * y) = L(x) · counit(y) + counit(x) · L(y)`.

    Equivalently, `L` is primitive in the bialgebra-theoretic sense when
    viewed as an element of the dual `H^∨`: the coproduct on `H^∨` is
    dual to the product on `H`, so `Δ_{H^∨}(L) = L ⊗ ε + ε ⊗ L` reads
    as the above identity after pairing against `x ⊗ y`. -/
def IsDualPrimitive (L : H →ₗ[R] R) : Prop :=
  ∀ x y : H, L (x * y) = L x * counit y + counit x * L y

/-- The submodule of dual primitives in `H →ₗ[R] R`. -/
def dualPrimitives : Submodule R (H →ₗ[R] R) where
  carrier := {L | IsDualPrimitive (R := R) L}
  zero_mem' := by
    intro x y
    show (0 : H →ₗ[R] R) (x * y) =
         (0 : H →ₗ[R] R) x * counit y + counit x * (0 : H →ₗ[R] R) y
    simp
  add_mem' {L₁ L₂} h₁ h₂ := by
    intro x y
    show (L₁ + L₂) (x * y) =
         (L₁ + L₂) x * counit y + counit x * (L₁ + L₂) y
    simp only [LinearMap.add_apply, h₁ x y, h₂ x y]
    ring
  smul_mem' c L hL := by
    intro x y
    show (c • L) (x * y) =
         (c • L) x * counit y + counit x * (c • L) y
    simp only [LinearMap.smul_apply, smul_eq_mul, hL x y]
    ring

@[simp] theorem mem_dualPrimitives (L : H →ₗ[R] R) :
    L ∈ dualPrimitives (R := R) (H := H) ↔ IsDualPrimitive L := Iff.rfl

end Bialgebra

/-! ## §2: Convolution Lie bracket -/

namespace Bialgebra

open scoped TensorProduct
open Coalgebra WithConv

variable {R : Type*} [CommRing R] {H : Type*} [Semiring H] [Bialgebra R H]

/-- The convolution Lie bracket on linear functionals `H →ₗ[R] R`,
    using mathlib's `WithConv` convolution product:
    `[L₁, L₂] := L₁ ⋆ L₂ - L₂ ⋆ L₁`. -/
noncomputable def convBracket (L₁ L₂ : H →ₗ[R] R) : H →ₗ[R] R :=
  ((toConv L₁ * toConv L₂ : WithConv (H →ₗ[R] R)) -
    toConv L₂ * toConv L₁).ofConv

/-- Closure of dual primitives under the convolution Lie bracket.

    **Sorry**: proof requires verifying that the convolution product of
    two dual primitives satisfies the dual-primitive identity. This is
    a Sweedler-style computation: expand `(L₁ ⋆ L₂)(xy)` using the
    coproduct's coassociativity and the algebra-hom property; rearrange
    using bialgebra axioms. Standard textbook result. -/
theorem IsDualPrimitive.convBracket_mem
    {L₁ L₂ : H →ₗ[R] R}
    (_h₁ : IsDualPrimitive (R := R) L₁) (_h₂ : IsDualPrimitive (R := R) L₂) :
    IsDualPrimitive (convBracket L₁ L₂) := by
  sorry

end Bialgebra

/-! ## §3: Specialization to Connes-Kreimer + MCB Lemma 1.7.3 -/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct
open Coalgebra Bialgebra

variable {R : Type*} [CommRing R] [CharZero R] [NoZeroDivisors R] {α : Type*}

/-- The **delta functional on a singleton forest**: extracts the
    coefficient of `{T}` (the forest containing only `T`) from a
    Connes-Kreimer element. -/
noncomputable def deltaSingleton (T : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] R :=
  Finsupp.lapply ({T} : Forest (Nonplanar α))

set_option linter.unusedSectionVars false in
@[simp] theorem deltaSingleton_of'_self (T : Nonplanar α) :
    deltaSingleton (R := R) T (of' ({T} : Forest (Nonplanar α))) = 1 := by
  show Finsupp.lapply ({T} : Forest (Nonplanar α))
        (Finsupp.single ({T} : Forest (Nonplanar α)) 1) = 1
  rw [Finsupp.lapply_apply, Finsupp.single_eq_same]

set_option linter.unusedSectionVars false in
theorem deltaSingleton_of'_other (T : Nonplanar α)
    (F : Forest (Nonplanar α)) (hF : F ≠ {T}) :
    deltaSingleton (R := R) T (of' F) = 0 := by
  classical
  show Finsupp.lapply ({T} : Forest (Nonplanar α)) (Finsupp.single F 1) = 0
  rw [Finsupp.lapply_apply, Finsupp.single_apply]
  exact if_neg hF

/-- The delta functional on a single tree is a **dual primitive** —
    i.e., it satisfies `δ_T(x * y) = δ_T(x) · ε(y) + ε(x) · δ_T(y)`.

    This is the bialgebraic content of MCB's observation (book p. 79)
    that primitives in `H^∨` are exactly the single-tree deltas.

    **Sorry**. Proof structure (conceptually straightforward but
    Lean-elaboration-heavy):

    1. **Bilinear reduction** to basis pairs `x = of' F`, `y = of' G`.
       Both sides are linear in `x` and `y` (via algebra-hom-ness of
       `counit` and linearity of `deltaSingleton`). Implementation needs
       explicit type management — `ConnesKreimer R (Nonplanar α)` is a
       def alias for `Forest →₀ R`, and mathlib's `Finsupp.induction_linear`
       motive types as `Finsupp`, dropping the algebra structure.

    2. **Basis pair**: `of' F * of' G = of' (F + G)` (`of'_add`). Case
       on `F + G = {T}`:
       * Yes: `card F + card G = 1`, so one side is `0`, the other is
         `{T}`; LHS = 1, RHS = 1 (exactly one term contributes 1).
       * No: LHS = 0 by `deltaSingleton_of'_other`; RHS = 0 by case
         analysis (both terms would force `F + G = {T}`, contradiction).

    Deferred to a follow-up session that builds bilinear-reduction
    infrastructure for the `ConnesKreimer` algebra alias. -/
theorem deltaSingleton_isDualPrimitive (T : Nonplanar α) :
    IsDualPrimitive (deltaSingleton (R := R) T) := by
  sorry

/-- **MCB Lemma 1.7.3** (dual-primitive closure corollary): the
    convolution Lie bracket of two single-tree deltas is again a dual
    primitive, by `IsDualPrimitive.convBracket_mem` applied to
    `deltaSingleton_isDualPrimitive`. -/
theorem mcb_lemma_1_7_3_dualPrimitive (T₁ T₂ : Nonplanar α) :
    IsDualPrimitive
      (convBracket (deltaSingleton (R := R) T₁) (deltaSingleton T₂)) :=
  IsDualPrimitive.convBracket_mem
    (deltaSingleton_isDualPrimitive T₁)
    (deltaSingleton_isDualPrimitive T₂)

/-! ### What's deferred to a future session

The **full** MCB Lemma 1.7.3 (per book p. 79):

  `[δ_{T_1}, δ_{T_2}](of' {T}) = c^T_{T_1,T_2} − c^T_{T_2,T_1}`

where `c^T_{T_1,T_2} = #{v ∈ V(T) | T_v ≃ T_1 ∧ T/T_v ≃ T_2}` (Δ^c
quotient on the right channel). Equivalently:

  `[δ_{T_1}, δ_{T_2}] = δ_{T_1 ▷ T_2 − T_2 ▷ T_1}`

(extended linearly). Formalizing this requires building:
* The vertex-match count `c^T_{T_1,T_2} : Nonplanar α → Nonplanar α →
  Nonplanar α → ℕ` (subtree-at-vertex + Δ^c quotient + isomorphism).
* The linear extension of `δ` to formal sums of trees.

These extensions are tractable but exceed this session's scope. The
substrate built here (`IsDualPrimitive`, `dualPrimitives`,
`convBracket`, `deltaSingleton`) is the load-bearing API; the count
substrate + per-test-tree statement go in a follow-up. -/

end ConnesKreimer

end RootedTree
