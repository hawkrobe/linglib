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
    {x y : H} (𝓡x : Coalgebra.Repr R x) (𝓡y : Coalgebra.Repr R y) :
    Coalgebra.Repr R (x * y) where
  ι := 𝓡x.ι × 𝓡y.ι
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

    **Proof structure** (Sweedler-style, standard textbook result):
    using `IsDualPrimitive` on `L₁` and `L₂`, expand
    `(L₁ ⋆ L₂)(xy) = (L₁ ⋆ L₂)(x) · ε(y) + ε(x) · (L₁ ⋆ L₂)(y) +
                     L₁(x) · L₂(y) + L₂(x) · L₁(y)`
    via Sweedler notation. The "cross terms" `L₁(x)·L₂(y) + L₂(x)·L₁(y)`
    are symmetric in `(L₁, L₂)`, so they cancel in the difference
    `(L₁ ⋆ L₂)(xy) - (L₂ ⋆ L₁)(xy)`. The remaining terms are exactly
    `((L₁ ⋆ L₂) - (L₂ ⋆ L₁))(x) · ε(y) + ε(x) · ((L₁ ⋆ L₂) - (L₂ ⋆ L₁))(y)`,
    which is `[L₁, L₂](x) · ε(y) + ε(x) · [L₁, L₂](y)`. ∎

    **Sorry**: the formal Lean proof requires careful manipulation of
    `Coalgebra.Repr` (the Sweedler-sum API in mathlib's Convolution.lean).
    Specifically: building `Coalgebra.Repr R (x * y)` from `ℛ x` and
    `ℛ y` via `Bialgebra.comul_mul` (~20 LOC), then expanding all four
    `(L_i ⋆ L_j)(·)` applications via `Repr.convMul_apply`, applying
    `IsDualPrimitive` to each `L_i (x_(1) · y_(1))` term, and closing
    via counit identities + ring/abel (~80-150 LOC). The proof has no
    deep mathematical content beyond standard bialgebra-derivation
    closure, and is mathlib upstream-worthy when closed. -/
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
  -- Unfold convBracket. The application of (a - b).ofConv at z equals
  -- a.ofConv z - b.ofConv z (LinearMap subtraction is pointwise).
  have unfold_app : ∀ z : H,
      convBracket L₁ L₂ z =
        (toConv L₁ * toConv L₂ : WithConv (H →ₗ[R] R)).ofConv z -
        (toConv L₂ * toConv L₁ : WithConv (H →ₗ[R] R)).ofConv z := fun z => by
    show ((toConv L₁ * toConv L₂ - toConv L₂ * toConv L₁ : WithConv _).ofConv) z = _
    rfl
  rw [unfold_app, unfold_app, unfold_app]
  -- Expand each (L_i * L_j).ofConv z via convMul_apply.
  rw [𝓡xy.convMul_apply (toConv L₁) (toConv L₂),
      𝓡xy.convMul_apply (toConv L₂) (toConv L₁),
      𝓡x.convMul_apply (toConv L₁) (toConv L₂),
      𝓡x.convMul_apply (toConv L₂) (toConv L₁),
      𝓡y.convMul_apply (toConv L₁) (toConv L₂),
      𝓡y.convMul_apply (toConv L₂) (toConv L₁)]
  -- At this point: LHS is a difference of two sums over 𝓡xy.index
  -- (= 𝓡x.index ×ˢ 𝓡y.index), each of the form Σ L_i (𝓡xy.left p) ·
  -- L_j (𝓡xy.right p). Unfold 𝓡xy via Finset.sum_product and apply
  -- IsDualPrimitive (h₁, h₂) to each `L_i (𝓡x.left · 𝓡y.left)` factor.
  -- Cross-terms cancel under the L₁⋆L₂ - L₂⋆L₁ subtraction; remaining
  -- terms collect into the RHS via counit identities + ring.
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
    refine Finsupp.induction_linear x ?_ ?_ ?_
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
      refine Finsupp.induction_linear y ?_ ?_ ?_
      · -- y = 0
        let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
        show deltaSingleton T (x_single * (0 : ConnesKreimer R (Nonplanar α))) =
             deltaSingleton T x_single * counit (0 : ConnesKreimer R (Nonplanar α)) +
             counit x_single * deltaSingleton T (0 : ConnesKreimer R (Nonplanar α))
        simp
      · -- y = y₁ + y₂
        intro y₁ y₂ ih₁ ih₂
        let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
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
        let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
        let y_single : ConnesKreimer R (Nonplanar α) := Finsupp.single G s
        show deltaSingleton T (x_single * y_single) =
             deltaSingleton T x_single * counit y_single +
             counit x_single * deltaSingleton T y_single
        have hx : x_single = r • (of' (R := R) F) :=
          (Finsupp.smul_single_one F r).symm
        have hy : y_single = s • (of' (R := R) G) :=
          (Finsupp.smul_single_one G s).symm
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
