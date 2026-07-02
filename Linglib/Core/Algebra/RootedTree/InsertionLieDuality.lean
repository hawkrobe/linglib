/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningDuality
import Mathlib.RingTheory.Coalgebra.Convolution

set_option autoImplicit false

/-!
# Insertion Lie algebra ≅ primitives in the dual Hopf algebra (MCB Lemma 1.7.3)
[marcolli-chomsky-berwick-2025]

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
* `deltaSingleton_isDualPrimitive` — `δ_T` is a dual primitive
  (sorry-free).
* `mcb_lemma_1_7_3_dualPrimitive` — corollary that the convolution Lie
  bracket of two single-tree deltas is again a dual primitive
  (sorry-free).
* `mcb_lemma_1_7_3_explicit` — the **full** Lemma 1.7.3 in Δ^ρ form:
  `[δ_{T₁}, δ_{T₂}](of' {T}) = countSingleCutsRho T T₁ T₂ −
  countSingleCutsRho T T₂ T₁`. Substrate-faithful analog of MCB's
  `c^T_{T₁,T₂} − c^T_{T₂,T₁}` using Δ^ρ (deletion) semantics rather
  than Δ^c (trace-leaf). The Δ^c version follows via the strip
  bijection in `Coproduct/DeletionNonplanar.lean`.

## What this file does NOT do

* Does not formalize the 1-α quotient (would make `H` a genuine
  connected Hopf algebra; not needed for the statement on the bialgebra).
* Does not state a full Lie algebra isomorphism between the insertion
  Lie algebra and dual primitives (only closure under bracket).
* Does not establish the bijection of book Figure 1.6 (would require
  R.5.5 + R.7 sorries to close first).

## Status

`[UPSTREAM]` candidate for the `Bialgebra.IsDualPrimitive` /
`dualPrimitives` / `convBracket` substrate (sorry-free, including
`IsDualPrimitive.convBracket_mem` — closure under bracket).
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

/-! ### Sweedler representation of a product

`Coalgebra.Repr.mul` builds a Repr for `x * y` in a `Bialgebra` from
Reprs of `x` and `y`, via the bialgebra axiom `comul (xy) = comul x *
comul y`. This is the key helper for any Sweedler-style proof that
works with products in a bialgebra; missing from mathlib. -/

/-- **Sweedler representation of `x * y`**: given Reprs `𝓡x : Repr R x`
    and `𝓡y : Repr R y` in a bialgebra `H`, the product `x * y` has
    Repr indexed by `𝓡x.index ×ˢ 𝓡y.index` with
    `left (i, j) = 𝓡x.left i * 𝓡y.left j` and
    `right (i, j) = 𝓡x.right i * 𝓡y.right j`.

    Mathlib gap. -/
noncomputable def Coalgebra.Repr.mul {R H : Type*}
    [CommSemiring R] [Semiring H] [Bialgebra R H]
    {x y : H} {ιx ιy : Type*} (𝓡x : Coalgebra.Repr R x ιx) (𝓡y : Coalgebra.Repr R y ιy) :
    Coalgebra.Repr R (x * y) (ιx × ιy) where
  index := 𝓡x.index ×ˢ 𝓡y.index
  left := fun p => 𝓡x.left p.1 * 𝓡y.left p.2
  right := fun p => 𝓡x.right p.1 * 𝓡y.right p.2
  eq := by
    rw [Bialgebra.comul_mul, ← 𝓡x.eq, ← 𝓡y.eq, Finset.sum_product,
        Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

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

    **Proof structure** (Sweedler-style, standard textbook result).
    Using `IsDualPrimitive` on `L₁` and `L₂`, expand
    `(L₁ ⋆ L₂)(xy) = (L₁ ⋆ L₂)(x) · ε(y) + ε(x) · (L₁ ⋆ L₂)(y) +
                     L₁(x) · L₂(y) + L₂(x) · L₁(y)`
    via Sweedler notation (Lemma `IsDualPrimitive.convMul_apply_mul`).
    The "cross terms" `L₁(x)·L₂(y) + L₂(x)·L₁(y)` are symmetric in
    `(L₁, L₂)`, so they cancel in the difference
    `(L₁ ⋆ L₂)(xy) - (L₂ ⋆ L₁)(xy)`. The remaining terms are exactly
    `((L₁ ⋆ L₂) - (L₂ ⋆ L₁))(x) · ε(y) + ε(x) · ((L₁ ⋆ L₂) - (L₂ ⋆ L₁))(y)`,
    which is `[L₁, L₂](x) · ε(y) + ε(x) · [L₁, L₂](y)`. ∎ -/
theorem IsDualPrimitive.convBracket_mem
    {L₁ L₂ : H →ₗ[R] R}
    (h₁ : IsDualPrimitive (R := R) L₁) (h₂ : IsDualPrimitive (R := R) L₂) :
    IsDualPrimitive (convBracket L₁ L₂) := by
  classical
  intro x y
  -- Sweedler reprs for x, y, and x*y (via Coalgebra.Repr.mul).
  let 𝓡x := Coalgebra.Repr.arbitrary R x
  let 𝓡y := Coalgebra.Repr.arbitrary R y
  let 𝓡xy := 𝓡x.mul 𝓡y
  -- Step 1. Express convBracket via any Repr. Universe-monomorphic helpers
  -- (local `have` cannot be universe-polymorphic in Lean 4).
  have br_eq_xy : convBracket L₁ L₂ (x * y) =
      (∑ i ∈ 𝓡xy.index, L₁ (𝓡xy.left i) * L₂ (𝓡xy.right i)) -
      (∑ i ∈ 𝓡xy.index, L₂ (𝓡xy.left i) * L₁ (𝓡xy.right i)) := by
    show ((toConv L₁ * toConv L₂ - toConv L₂ * toConv L₁ : WithConv _).ofConv) (x * y) = _
    show (toConv L₁ * toConv L₂ : WithConv _).ofConv (x * y) -
         (toConv L₂ * toConv L₁ : WithConv _).ofConv (x * y) = _
    exact congrArg₂ (· - ·)
      (𝓡xy.convMul_apply (toConv L₁) (toConv L₂))
      (𝓡xy.convMul_apply (toConv L₂) (toConv L₁))
  have br_eq_x : convBracket L₁ L₂ x =
      (∑ i ∈ 𝓡x.index, L₁ (𝓡x.left i) * L₂ (𝓡x.right i)) -
      (∑ i ∈ 𝓡x.index, L₂ (𝓡x.left i) * L₁ (𝓡x.right i)) := by
    show ((toConv L₁ * toConv L₂ - toConv L₂ * toConv L₁ : WithConv _).ofConv) x = _
    show (toConv L₁ * toConv L₂ : WithConv _).ofConv x -
         (toConv L₂ * toConv L₁ : WithConv _).ofConv x = _
    exact congrArg₂ (· - ·)
      (𝓡x.convMul_apply (toConv L₁) (toConv L₂))
      (𝓡x.convMul_apply (toConv L₂) (toConv L₁))
  have br_eq_y : convBracket L₁ L₂ y =
      (∑ i ∈ 𝓡y.index, L₁ (𝓡y.left i) * L₂ (𝓡y.right i)) -
      (∑ i ∈ 𝓡y.index, L₂ (𝓡y.left i) * L₁ (𝓡y.right i)) := by
    show ((toConv L₁ * toConv L₂ - toConv L₂ * toConv L₁ : WithConv _).ofConv) y = _
    show (toConv L₁ * toConv L₂ : WithConv _).ofConv y -
         (toConv L₂ * toConv L₁ : WithConv _).ofConv y = _
    exact congrArg₂ (· - ·)
      (𝓡y.convMul_apply (toConv L₁) (toConv L₂))
      (𝓡y.convMul_apply (toConv L₂) (toConv L₁))
  -- Step 2. Counit-collapse helpers (via `mul_one`, `one_mul`, `1*1=1` in WithConv).
  have right_collapse_x : ∀ L : H →ₗ[R] R,
      ∑ i ∈ 𝓡x.index, L (𝓡x.left i) * counit (𝓡x.right i) = L x := fun L => by
    have happly : (toConv L * (1 : WithConv (H →ₗ[R] R))) x = L x := by rw [mul_one]
    rw [𝓡x.convMul_apply (toConv L) (1 : WithConv (H →ₗ[R] R))] at happly
    simpa [LinearMap.convOne_apply] using happly
  have right_collapse_y : ∀ L : H →ₗ[R] R,
      ∑ i ∈ 𝓡y.index, L (𝓡y.left i) * counit (𝓡y.right i) = L y := fun L => by
    have happly : (toConv L * (1 : WithConv (H →ₗ[R] R))) y = L y := by rw [mul_one]
    rw [𝓡y.convMul_apply (toConv L) (1 : WithConv (H →ₗ[R] R))] at happly
    simpa [LinearMap.convOne_apply] using happly
  have left_collapse_x : ∀ L : H →ₗ[R] R,
      ∑ i ∈ 𝓡x.index, counit (𝓡x.left i) * L (𝓡x.right i) = L x := fun L => by
    have happly : ((1 : WithConv (H →ₗ[R] R)) * toConv L) x = L x := by rw [one_mul]
    rw [𝓡x.convMul_apply (1 : WithConv (H →ₗ[R] R)) (toConv L)] at happly
    simpa [LinearMap.convOne_apply] using happly
  have left_collapse_y : ∀ L : H →ₗ[R] R,
      ∑ i ∈ 𝓡y.index, counit (𝓡y.left i) * L (𝓡y.right i) = L y := fun L => by
    have happly : ((1 : WithConv (H →ₗ[R] R)) * toConv L) y = L y := by rw [one_mul]
    rw [𝓡y.convMul_apply (1 : WithConv (H →ₗ[R] R)) (toConv L)] at happly
    simpa [LinearMap.convOne_apply] using happly
  have counit_collapse_x :
      ∑ i ∈ 𝓡x.index, counit (R := R) (𝓡x.left i) * counit (𝓡x.right i) = counit x := by
    have happly : ((1 : WithConv (H →ₗ[R] R)) * (1 : WithConv (H →ₗ[R] R))) x =
        (1 : WithConv (H →ₗ[R] R)) x := by rw [one_mul]
    rw [𝓡x.convMul_apply (1 : WithConv (H →ₗ[R] R)) (1 : WithConv (H →ₗ[R] R))] at happly
    simpa [LinearMap.convOne_apply] using happly
  have counit_collapse_y :
      ∑ i ∈ 𝓡y.index, counit (R := R) (𝓡y.left i) * counit (𝓡y.right i) = counit y := by
    have happly : ((1 : WithConv (H →ₗ[R] R)) * (1 : WithConv (H →ₗ[R] R))) y =
        (1 : WithConv (H →ₗ[R] R)) y := by rw [one_mul]
    rw [𝓡y.convMul_apply (1 : WithConv (H →ₗ[R] R)) (1 : WithConv (H →ₗ[R] R))] at happly
    simpa [LinearMap.convOne_apply] using happly
  -- Step 3. Sweedler-expand `(M ⋆ N)(x·y)` for any primitives M, N.
  -- Using h_M (resp. h_N) on L_*(x.l · y.l) (resp. L_*(x.r · y.r))
  -- + `Finset.sum_product` + binomial expansion + `Finset.sum_mul_sum`
  -- + collapse helpers.
  have expand : ∀ (M N : H →ₗ[R] R),
      IsDualPrimitive (R := R) M → IsDualPrimitive (R := R) N →
      (∑ p ∈ 𝓡x.index ×ˢ 𝓡y.index,
          M (𝓡x.left p.1 * 𝓡y.left p.2) * N (𝓡x.right p.1 * 𝓡y.right p.2)) =
        (∑ i ∈ 𝓡x.index, M (𝓡x.left i) * N (𝓡x.right i)) * counit y +
        M x * N y + N x * M y +
        counit x * (∑ j ∈ 𝓡y.index, M (𝓡y.left j) * N (𝓡y.right j)) := by
    intro M N hM hN
    -- Apply hM, hN inside the sum to expand M(x.l·y.l) and N(x.r·y.r).
    have step1 : (∑ p ∈ 𝓡x.index ×ˢ 𝓡y.index,
          M (𝓡x.left p.1 * 𝓡y.left p.2) * N (𝓡x.right p.1 * 𝓡y.right p.2)) =
        ∑ p ∈ 𝓡x.index ×ˢ 𝓡y.index,
          (M (𝓡x.left p.1) * counit (𝓡y.left p.2) +
              counit (𝓡x.left p.1) * M (𝓡y.left p.2)) *
          (N (𝓡x.right p.1) * counit (𝓡y.right p.2) +
              counit (𝓡x.right p.1) * N (𝓡y.right p.2)) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [hM, hN]
    rw [step1]
    -- Split the double sum into separate i and j sums, then expand the binomial.
    rw [Finset.sum_product]
    -- Now: Σ_i Σ_j [(a + b) · (c + d)] where
    --   a = M(x.l i) · ε(y.l j),  b = ε(x.l i) · M(y.l j)
    --   c = N(x.r i) · ε(y.r j),  d = ε(x.r i) · N(y.r j)
    -- We rearrange each summand into 4 i-j-separable products, then split the sum.
    -- Each summand becomes:
    --   (M(x.l i) · N(x.r i)) · (ε(y.l j) · ε(y.r j)) +
    --   (M(x.l i) · ε(x.r i)) · (ε(y.l j) · N(y.r j)) +
    --   (ε(x.l i) · N(x.r i)) · (M(y.l j) · ε(y.r j)) +
    --   (ε(x.l i) · ε(x.r i)) · (M(y.l j) · N(y.r j))
    have step2 : ∀ i ∈ 𝓡x.index, ∀ j ∈ 𝓡y.index,
        (M (𝓡x.left i) * counit (𝓡y.left j) +
            counit (𝓡x.left i) * M (𝓡y.left j)) *
        (N (𝓡x.right i) * counit (𝓡y.right j) +
            counit (𝓡x.right i) * N (𝓡y.right j)) =
        (M (𝓡x.left i) * N (𝓡x.right i)) * (counit (𝓡y.left j) * counit (𝓡y.right j)) +
        (M (𝓡x.left i) * counit (𝓡x.right i)) * (counit (𝓡y.left j) * N (𝓡y.right j)) +
        (counit (𝓡x.left i) * N (𝓡x.right i)) * (M (𝓡y.left j) * counit (𝓡y.right j)) +
        (counit (𝓡x.left i) * counit (𝓡x.right i)) * (M (𝓡y.left j) * N (𝓡y.right j)) := by
      intro i _ j _
      ring
    -- Apply step2 inside the double sum.
    rw [show (∑ i ∈ 𝓡x.index, ∑ j ∈ 𝓡y.index,
              (M (𝓡x.left i) * counit (𝓡y.left j) +
                  counit (𝓡x.left i) * M (𝓡y.left j)) *
              (N (𝓡x.right i) * counit (𝓡y.right j) +
                  counit (𝓡x.right i) * N (𝓡y.right j))) =
            ∑ i ∈ 𝓡x.index, ∑ j ∈ 𝓡y.index,
              ((M (𝓡x.left i) * N (𝓡x.right i)) *
                  (counit (𝓡y.left j) * counit (𝓡y.right j)) +
                (M (𝓡x.left i) * counit (𝓡x.right i)) *
                  (counit (𝓡y.left j) * N (𝓡y.right j)) +
                (counit (𝓡x.left i) * N (𝓡x.right i)) *
                  (M (𝓡y.left j) * counit (𝓡y.right j)) +
                (counit (𝓡x.left i) * counit (𝓡x.right i)) *
                  (M (𝓡y.left j) * N (𝓡y.right j))) from
          Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => step2 i hi j hj))]
    -- Split sums via add distribution and factor i-vs-j parts via sum_mul_sum.
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    -- Now each of the 4 terms is of the form (Σ_i f i) * (Σ_j g j). Apply collapse on y-sums.
    rw [counit_collapse_y, left_collapse_y N, right_collapse_y M]
    -- The fourth term's inner-j-sum stays as a sum; the i-side collapses for terms 2/3/4.
    rw [right_collapse_x M, left_collapse_x N, counit_collapse_x]
  -- Step 4. Rewrite goal via br_eq, unfold 𝓡xy = 𝓡x.mul 𝓡y, apply expand twice, ring.
  rw [br_eq_xy, br_eq_x, br_eq_y]
  change (∑ p ∈ 𝓡x.index ×ˢ 𝓡y.index,
            L₁ (𝓡x.left p.1 * 𝓡y.left p.2) * L₂ (𝓡x.right p.1 * 𝓡y.right p.2)) -
         (∑ p ∈ 𝓡x.index ×ˢ 𝓡y.index,
            L₂ (𝓡x.left p.1 * 𝓡y.left p.2) * L₁ (𝓡x.right p.1 * 𝓡y.right p.2)) =
         ((∑ i ∈ 𝓡x.index, L₁ (𝓡x.left i) * L₂ (𝓡x.right i)) -
          (∑ i ∈ 𝓡x.index, L₂ (𝓡x.left i) * L₁ (𝓡x.right i))) * counit y +
         counit x *
         ((∑ j ∈ 𝓡y.index, L₁ (𝓡y.left j) * L₂ (𝓡y.right j)) -
          (∑ j ∈ 𝓡y.index, L₂ (𝓡y.left j) * L₁ (𝓡y.right j)))
  rw [expand L₁ L₂ h₁ h₂, expand L₂ L₁ h₂ h₁]
  ring

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
  (Finsupp.lapply ({T} : Forest (Nonplanar α))).comp
    (toFinsuppAlgEquiv (R := R) (T := Nonplanar α)).toLinearEquiv.toLinearMap

set_option linter.unusedSectionVars false in
@[simp] theorem deltaSingleton_of'_self (T : Nonplanar α) :
    deltaSingleton (R := R) T (of' ({T} : Forest (Nonplanar α))) = 1 := by
  simp only [deltaSingleton, LinearMap.comp_apply, LinearEquiv.coe_coe,
    toFinsuppAlgEquiv_apply, Finsupp.lapply_apply]
  exact Finsupp.single_eq_same

set_option linter.unusedSectionVars false in
theorem deltaSingleton_of'_other (T : Nonplanar α)
    (F : Forest (Nonplanar α)) (hF : F ≠ {T}) :
    deltaSingleton (R := R) T (of' F) = 0 := by
  classical
  simp only [deltaSingleton, LinearMap.comp_apply, LinearEquiv.coe_coe,
    toFinsuppAlgEquiv_apply, Finsupp.lapply_apply]
  show (Finsupp.single F (1 : R) : Forest (Nonplanar α) →₀ R) {T} = 0
  rw [Finsupp.single_apply]
  exact if_neg hF

/-- The delta functional on a single tree is a **dual primitive** —
    i.e., it satisfies `δ_T(x * y) = δ_T(x) · ε(y) + ε(x) · δ_T(y)`.

    This is the bialgebraic content of MCB's observation (book p. 79)
    that primitives in `H^∨` are exactly the single-tree deltas.

    Proof: bilinear `suffices` reduction to a basis-pair statement,
    then `smul_mul_smul_comm` + `← of'_add` factors the scalars out,
    leaving an unscaled basis identity. The basis identity is closed
    by case-split on `F + G = {T}` via Multiset cardinality (singleton
    forces one factor to be empty, the other to be `{T}`). -/
theorem deltaSingleton_isDualPrimitive (T : Nonplanar α) :
    IsDualPrimitive (deltaSingleton (R := R) T) := by
  classical
  -- Step 1: reduce to a basis-pair + scalars statement.
  suffices h : ∀ F G : Forest (Nonplanar α), ∀ r s : R,
      deltaSingleton (R := R) T
          ((r • of' F : ConnesKreimer R (Nonplanar α)) * (s • of' G)) =
        deltaSingleton T (r • of' F : ConnesKreimer R (Nonplanar α)) *
          counit (s • of' G : ConnesKreimer R (Nonplanar α)) +
        counit (r • of' F : ConnesKreimer R (Nonplanar α)) *
          deltaSingleton T (s • of' G : ConnesKreimer R (Nonplanar α)) by
    intro x y
    refine ConnesKreimer.induction_linear x ?_ ?_ ?_
    · -- x = 0
      show deltaSingleton T ((0 : ConnesKreimer R (Nonplanar α)) * y) =
           deltaSingleton T (0 : ConnesKreimer R (Nonplanar α)) * counit y +
           counit (0 : ConnesKreimer R (Nonplanar α)) * deltaSingleton T y
      simp
    · -- x = x₁ + x₂
      intro x₁ x₂ ih₁ ih₂
      let x₁' : ConnesKreimer R (Nonplanar α) := x₁
      let x₂' : ConnesKreimer R (Nonplanar α) := x₂
      show deltaSingleton T ((x₁' + x₂') * y) =
           deltaSingleton T (x₁' + x₂') * counit y +
           counit (x₁' + x₂') * deltaSingleton T y
      rw [add_mul, map_add, map_add, map_add, ih₁, ih₂]
      -- Unify `CoalgebraStruct.counit` (from ih) ↔ `counit` (from show);
      -- both are defeq via `Coalgebra.counit` projection. `show` forces
      -- the goal into a single normalized form, then `ring` closes.
      show deltaSingleton T x₁ * counit y + counit x₁ * deltaSingleton T y +
           (deltaSingleton T x₂ * counit y + counit x₂ * deltaSingleton T y) =
           (deltaSingleton T x₁ + deltaSingleton T x₂) * counit y +
           (counit x₁ + counit x₂) * deltaSingleton T y
      ring
    · -- x = single F r
      intro F r
      refine ConnesKreimer.induction_linear y ?_ ?_ ?_
      · -- y = 0
        let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
        show deltaSingleton T (x_single * (0 : ConnesKreimer R (Nonplanar α))) =
             deltaSingleton T x_single * counit (0 : ConnesKreimer R (Nonplanar α)) +
             counit x_single * deltaSingleton T (0 : ConnesKreimer R (Nonplanar α))
        simp
      · -- y = y₁ + y₂
        intro y₁ y₂ ih₁ ih₂
        let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
        let y₁' : ConnesKreimer R (Nonplanar α) := y₁
        let y₂' : ConnesKreimer R (Nonplanar α) := y₂
        show deltaSingleton T (x_single * (y₁' + y₂')) =
             deltaSingleton T x_single * counit (y₁' + y₂') +
             counit x_single * deltaSingleton T (y₁' + y₂')
        rw [mul_add, map_add, map_add, map_add, ih₁, ih₂]
        show deltaSingleton T x_single * counit y₁ + counit x_single * deltaSingleton T y₁ +
             (deltaSingleton T x_single * counit y₂ + counit x_single * deltaSingleton T y₂) =
             deltaSingleton T x_single * (counit y₁ + counit y₂) +
             counit x_single * (deltaSingleton T y₁ + deltaSingleton T y₂)
        ring
      · -- y = single G s
        intro G s
        let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
        let y_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single G s
        show deltaSingleton T (x_single * y_single) =
             deltaSingleton T x_single * counit y_single +
             counit x_single * deltaSingleton T y_single
        have hx : x_single = r • (of' (R := R) F) :=
          ConnesKreimer.smul_single_one F r
        have hy : y_single = s • (of' (R := R) G) :=
          ConnesKreimer.smul_single_one G s
        rw [hx, hy]
        exact h F G r s
  -- Step 2: scalars factor out; reduce to the unscaled basis identity.
  intro F G r s
  suffices hbasis : deltaSingleton (R := R) T
        (of' (F + G) : ConnesKreimer R (Nonplanar α)) =
      deltaSingleton T (of' F : ConnesKreimer R (Nonplanar α)) * counit (of' G) +
      counit (of' F : ConnesKreimer R (Nonplanar α)) * deltaSingleton T (of' G) by
    rw [smul_mul_smul_comm, ← of'_add]
    simp only [map_smul, smul_eq_mul, hbasis]
    ring
  -- Step 3: unscaled basis identity. Case-split on F + G = {T}.
  by_cases hFG : F + G = ({T} : Forest (Nonplanar α))
  · -- F + G = {T}. Card sum = 1; one of F, G is empty, the other is {T}.
    have hcard : F.card + G.card = 1 := by
      have := congrArg Multiset.card hFG
      simpa [Multiset.card_add, Multiset.card_singleton] using this
    have h0_ne : (0 : Forest (Nonplanar α)) ≠ {T} := by
      intro h
      have := congrArg Multiset.card h
      simp [Multiset.card_singleton] at this
    rcases Nat.add_eq_one_iff.mp hcard with ⟨hF, hG⟩ | ⟨hF, hG⟩
    · -- F = 0, G = {T}
      have hF0 : F = 0 := Multiset.card_eq_zero.mp hF
      have hG_T : G = {T} := by rw [hF0, zero_add] at hFG; exact hFG
      subst hF0; subst hG_T
      -- Reorder: kill δ_T (of' 0) FIRST (before of'_zero rewrites of' 0 away).
      rw [zero_add, deltaSingleton_of'_self, deltaSingleton_of'_other T 0 h0_ne,
          of'_zero, map_one, counit_of', Multiset.card_singleton]
      simp
    · -- F = {T}, G = 0
      have hG0 : G = 0 := Multiset.card_eq_zero.mp hG
      have hF_T : F = {T} := by rw [hG0, add_zero] at hFG; exact hFG
      subst hG0; subst hF_T
      rw [add_zero, deltaSingleton_of'_self, deltaSingleton_of'_other T 0 h0_ne,
          of'_zero, map_one, counit_of', Multiset.card_singleton]
      simp
  · -- F + G ≠ {T}. Both sides reduce to 0.
    rw [deltaSingleton_of'_other T (F + G) hFG]
    have hT1 : deltaSingleton T (of' F : ConnesKreimer R (Nonplanar α)) *
               counit (of' G : ConnesKreimer R (Nonplanar α)) = 0 := by
      by_cases hF : F = {T}
      · by_cases hG : G.card = 0
        · exfalso
          have hG0 : G = 0 := Multiset.card_eq_zero.mp hG
          exact hFG (by rw [hF, hG0, add_zero])
        · rw [counit_of', if_neg hG, mul_zero]
      · rw [deltaSingleton_of'_other T F hF, zero_mul]
    have hT2 : counit (of' F : ConnesKreimer R (Nonplanar α)) *
               deltaSingleton T (of' G : ConnesKreimer R (Nonplanar α)) = 0 := by
      by_cases hG : G = {T}
      · by_cases hF : F.card = 0
        · exfalso
          have hF0 : F = 0 := Multiset.card_eq_zero.mp hF
          exact hFG (by rw [hF0, hG, zero_add])
        · rw [counit_of', if_neg hF, zero_mul]
      · rw [deltaSingleton_of'_other T G hG, mul_zero]
    rw [hT1, hT2, zero_add]

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

/-! ## §4: MCB Lemma 1.7.3 (full) — explicit count formula

The substantive bracket-counting form of MCB Lemma 1.7.3. Since our
Bialgebra structure uses Δ^ρ (deletion remainder), the count is in
terms of Δ^ρ cut summands rather than MCB's Δ^c (trace-leaf) version:

  `[δ_{T₁}, δ_{T₂}](of' {T}) = countSingleCutsRho T T₁ T₂
                              − countSingleCutsRho T T₂ T₁`

where `countSingleCutsRho T T₁ T₂` counts the Δ^ρ cut summands of `T`
whose cut forest is exactly `{T₁}` and whose remainder is exactly `T₂`.

This is the substrate-faithful analog of MCB's `c^T_{T₁,T₂}`. The
Δ^c-quotient version (with trace leaves at cut sites) would yield the
same count under the bijection between Δ^ρ remainders and Δ^c trunks
established in `Coproduct/DeletionNonplanar.lean`. -/

section MCBLemma_1_7_3_Full

open WithConv Classical

attribute [local instance] Classical.propDecidable

/-- **Δ^ρ single-cut count**: number of Δ^ρ cut summands of `T` whose
    cut forest equals `{T₁}` and whose remainder tree equals `T₂`. -/
noncomputable def countSingleCutsRho (T T₁ T₂ : Nonplanar α) : ℕ :=
  (cutSummandsN T).countP
    (fun p => p.1 = ({T₁} : Forest (Nonplanar α)) ∧ p.2 = T₂)

/-- A delta on a singleton forest applied to `of' F`: returns `1` if
    `F = {T}` and `0` otherwise (rephrased as an indicator). -/
private theorem deltaSingleton_of'_indicator (T : Nonplanar α)
    (F : Forest (Nonplanar α)) :
    deltaSingleton (R := R) T (of' F) =
      (if F = ({T} : Forest (Nonplanar α)) then (1 : R) else 0) := by
  classical
  by_cases hF : F = ({T} : Forest (Nonplanar α))
  · subst hF
    rw [if_pos rfl, deltaSingleton_of'_self]
  · rw [if_neg hF, deltaSingleton_of'_other T F hF]

/-- `δ_{T₂}` applied to a singleton-tree basis vector `ofTree T'` is
    the indicator `[T' = T₂]`. -/
private theorem deltaSingleton_ofTree_indicator (T₂ T' : Nonplanar α) :
    deltaSingleton (R := R) T₂ (ofTree T') =
      (if T' = T₂ then (1 : R) else 0) := by
  classical
  show deltaSingleton (R := R) T₂
        (of' ({T'} : Forest (Nonplanar α))) = _
  rw [deltaSingleton_of'_indicator]
  by_cases h : T' = T₂
  · subst h
    rw [if_pos rfl, if_pos rfl]
  · have h' : ({T'} : Forest (Nonplanar α)) ≠ {T₂} := by
      intro heq
      have := Multiset.singleton_inj.mp heq
      exact h this
    rw [if_neg h', if_neg h]

/-- The convolution `(toConv δ_{T₁} * toConv δ_{T₂}).ofConv` evaluated
    on a single-tree basis vector `of' {T}` equals the count of Δ^ρ
    cut summands of `T` extracting `{T₁}` and leaving `T₂`. -/
theorem deltaSingleton_conv_apply_singleton (T T₁ T₂ : Nonplanar α) :
    ((toConv (deltaSingleton (R := R) T₁) *
        toConv (deltaSingleton T₂) :
        WithConv (ConnesKreimer R (Nonplanar α) →ₗ[R] R))).ofConv
        (of' ({T} : Forest (Nonplanar α))) =
      (countSingleCutsRho T T₁ T₂ : R) := by
  -- Unfold convolution: `(f * g).ofConv z = mul' (TensorProduct.map f g (comul z))`.
  rw [show ((toConv (deltaSingleton (R := R) T₁) *
            toConv (deltaSingleton T₂) :
            WithConv (ConnesKreimer R (Nonplanar α) →ₗ[R] R))).ofConv
              (of' ({T} : Forest (Nonplanar α))) =
            (toConv (deltaSingleton (R := R) T₁) *
              toConv (deltaSingleton T₂) :
                WithConv (ConnesKreimer R (Nonplanar α) →ₗ[R] R))
              (of' ({T} : Forest (Nonplanar α))) from rfl,
      LinearMap.convMul_apply]
  -- `comul (of' {T}) = comulAlgHomN (of' {T}) = comulForestN {T} = comulTreeN T`.
  show LinearMap.mul' R R
        (TensorProduct.map (deltaSingleton (R := R) T₁) (deltaSingleton T₂)
          (Coalgebra.comul (R := R) (of' ({T} : Forest (Nonplanar α))))) = _
  rw [show (Coalgebra.comul (R := R)
              (of' ({T} : Forest (Nonplanar α))) :
              ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) =
            comulTreeN T from by
    show comulAlgHomN (R := R) (of' ({T} : Forest (Nonplanar α))) = _
    rw [comulAlgHomN_apply_of']
    show comulForestN (R := R) ({T} : Forest (Nonplanar α)) = comulTreeN T
    unfold comulForestN
    rw [Multiset.map_singleton, Multiset.prod_singleton]]
  -- Unfold `comulTreeN T = ofTree T ⊗ 1 + Σ cuts`.
  unfold comulTreeN
  rw [map_add, map_add]
  -- First summand: `mul' R R (δ_{T₁}(ofTree T) ⊗ δ_{T₂}(1)) = δ_{T₁}(ofTree T) * 0 = 0`.
  rw [show LinearMap.mul' R R
        (TensorProduct.map (deltaSingleton (R := R) T₁) (deltaSingleton T₂)
          (ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))) =
            (0 : R) from by
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply,
        show deltaSingleton (R := R) T₂
              (1 : ConnesKreimer R (Nonplanar α)) = 0 from by
          show deltaSingleton (R := R) T₂
                (of' (0 : Forest (Nonplanar α))) = 0
          rw [deltaSingleton_of'_indicator]
          have h : (0 : Forest (Nonplanar α)) ≠ {T₂} := by
            intro h
            have := congrArg Multiset.card h
            simp [Multiset.card_singleton] at this
          rw [if_neg h]]
    rw [mul_zero]]
  rw [zero_add]
  -- Second summand: distribute over the multiset sum, reduce each summand to indicator.
  rw [map_multiset_sum (TensorProduct.map (deltaSingleton (R := R) T₁)
        (deltaSingleton T₂)),
      map_multiset_sum (LinearMap.mul' R R)]
  simp only [Multiset.map_map]
  -- Each summand: `mul' R R (TP.map δ_{T₁} δ_{T₂} (of' p.1 ⊗ ofTree p.2))
  --                = δ_{T₁}(of' p.1) * δ_{T₂}(ofTree p.2)`.
  rw [show ((LinearMap.mul' R R) ∘
            (TensorProduct.map (deltaSingleton (R := R) T₁) (deltaSingleton T₂)) ∘
            (fun p : Forest (Nonplanar α) × Nonplanar α =>
              (of' (R := R) p.1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R] ofTree p.2)) =
            (fun p : Forest (Nonplanar α) × Nonplanar α =>
              deltaSingleton (R := R) T₁ (of' p.1) *
                deltaSingleton T₂ (ofTree p.2)) from by
    funext p
    show LinearMap.mul' R R (TensorProduct.map (deltaSingleton (R := R) T₁)
          (deltaSingleton T₂) (of' p.1 ⊗ₜ[R] ofTree p.2)) = _
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]]
  -- Replace each summand by the indicator `[p.1 = {T₁} ∧ p.2 = T₂]`.
  have step_indicator :
      ((cutSummandsN T).map
        (fun p : Forest (Nonplanar α) × Nonplanar α =>
          deltaSingleton (R := R) T₁ (of' p.1) *
            deltaSingleton T₂ (ofTree p.2))) =
      ((cutSummandsN T).map
        (fun p : Forest (Nonplanar α) × Nonplanar α =>
          (if p.1 = ({T₁} : Forest (Nonplanar α)) ∧ p.2 = T₂
            then (1 : R) else 0))) := by
    apply Multiset.map_congr rfl
    intro p _
    rw [deltaSingleton_of'_indicator, deltaSingleton_ofTree_indicator]
    by_cases h1 : p.1 = ({T₁} : Forest (Nonplanar α))
    · by_cases h2 : p.2 = T₂
      · have h12 : p.1 = ({T₁} : Forest (Nonplanar α)) ∧ p.2 = T₂ := ⟨h1, h2⟩
        rw [if_pos h1, if_pos h2, if_pos h12, mul_one]
      · have h12 : ¬(p.1 = ({T₁} : Forest (Nonplanar α)) ∧ p.2 = T₂) := by
          intro h; exact h2 h.2
        rw [if_pos h1, if_neg h2, if_neg h12, one_mul]
    · have h12 : ¬(p.1 = ({T₁} : Forest (Nonplanar α)) ∧ p.2 = T₂) := by
        intro h; exact h1 h.1
      rw [if_neg h1, if_neg h12, zero_mul]
  rw [step_indicator]
  -- Sum of indicators = countP cast to R.
  have step_count :
      ((cutSummandsN T).map
        (fun p : Forest (Nonplanar α) × Nonplanar α =>
          (if p.1 = ({T₁} : Forest (Nonplanar α)) ∧ p.2 = T₂
            then (1 : R) else 0))).sum =
      ((countSingleCutsRho T T₁ T₂ : ℕ) : R) := by
    unfold countSingleCutsRho
    rw [Multiset.countP_eq_card_filter]
    induction (cutSummandsN T) using Multiset.induction with
    | empty =>
      rw [Multiset.map_zero, Multiset.sum_zero, Multiset.filter_zero,
          Multiset.card_zero, Nat.cast_zero]
    | cons p s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons, ih]
      by_cases h : p.1 = ({T₁} : Forest (Nonplanar α)) ∧ p.2 = T₂
      · rw [if_pos h, if_pos h, Multiset.card_add, Multiset.card_singleton,
            Nat.cast_add, Nat.cast_one, add_comm]
      · simp only [if_neg h, zero_add]
  exact step_count

/-- **MCB Lemma 1.7.3** (Δ^ρ explicit form): the convolution Lie bracket
    of two single-tree deltas evaluated on a single-tree basis vector
    is the antisymmetrized count of single-tree Δ^ρ cuts:

    `[δ_{T₁}, δ_{T₂}](of' {T}) = countSingleCutsRho T T₁ T₂
                                − countSingleCutsRho T T₂ T₁`

    Substrate-faithful analog of the book's `c^T_{T₁,T₂} − c^T_{T₂,T₁}`.
    The Δ^c-quotient version (with trace leaves) would yield the same
    count via the strip bijection in `Coproduct/DeletionNonplanar.lean`. -/
theorem mcb_lemma_1_7_3_explicit (T T₁ T₂ : Nonplanar α) :
    convBracket (deltaSingleton (R := R) T₁) (deltaSingleton T₂)
        (of' ({T} : Forest (Nonplanar α))) =
      (countSingleCutsRho T T₁ T₂ : R) - (countSingleCutsRho T T₂ T₁ : R) := by
  show ((toConv (deltaSingleton (R := R) T₁) *
        toConv (deltaSingleton T₂) -
        toConv (deltaSingleton T₂) * toConv (deltaSingleton T₁) :
        WithConv (ConnesKreimer R (Nonplanar α) →ₗ[R] R))).ofConv
        (of' ({T} : Forest (Nonplanar α))) = _
  rw [show ((toConv (deltaSingleton (R := R) T₁) *
              toConv (deltaSingleton T₂) -
              toConv (deltaSingleton T₂) * toConv (deltaSingleton T₁) :
              WithConv (ConnesKreimer R (Nonplanar α) →ₗ[R] R))).ofConv
              (of' ({T} : Forest (Nonplanar α))) =
            ((toConv (deltaSingleton (R := R) T₁) *
              toConv (deltaSingleton T₂) :
                WithConv (ConnesKreimer R (Nonplanar α) →ₗ[R] R))).ofConv
                (of' ({T} : Forest (Nonplanar α))) -
            ((toConv (deltaSingleton (R := R) T₂) *
              toConv (deltaSingleton T₁) :
                WithConv (ConnesKreimer R (Nonplanar α) →ₗ[R] R))).ofConv
                (of' ({T} : Forest (Nonplanar α))) from by
    show _ = _
    rfl]
  rw [deltaSingleton_conv_apply_singleton, deltaSingleton_conv_apply_singleton]

end MCBLemma_1_7_3_Full

end ConnesKreimer

end RootedTree
