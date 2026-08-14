/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.BMinus
import Linglib.Core.Algebra.RootedTree.PreLie.OudomGuinBridge
import Mathlib.Tactic.Ring

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# Phase D: Q5c via pairing nondegeneracy (OG-faithful route)
[oudom-guin-2008] [foissy-typed-decorated-rooted-trees-2018]

This file implements OG paper Prop 3.2's proof strategy on the
linglib substrate. The goal is:

  `gl_product_eq_oudomGuinStar_via_pairing` :
    `ckIso (X ★ Y) = unop (op (ckIso X) * op (ckIso Y))`

i.e., the OG ★ on `S(InsertionAlgebra α)` transports under
`ckIsoSymmetricAlgebra` to the Grossman-Larson product on
`ConnesKreimer ℤ (Nonplanar α)`.

## Strategy

By **pairing nondegeneracy** (`pairing_nondegenerate` over `ℤ` with
`[CharZero] [NoZeroDivisors]`), it suffices to show

  `⟨ckIso(X ★ Y), z⟩ = ⟨unop (op (ckIso X) * op (ckIso Y)), z⟩` for all `z`.

For each `z`, this reduces — via the B+/B- adjoint
(`bMinusLin_pairing_adjoint`) + the Phase C OG identity
(`bMinusLin_gl_mul`) on the CK side, and OG's Prop 2.8.ii (ε of ★)
on the S(L) side — to a recursion that bottoms out at ε(X) · ε(Y)
for `z = 1`.

## Inputs

* The pairing on CK + nondegeneracy (`GrossmanLarsonPairing.lean`).
* The B+/B- adjoint (`bMinusLin_pairing_adjoint`) and the OG derivation
  identity (`bMinusLin_gl_mul`), both in `BMinus.lean`.
* OG S(L) machinery: `oudomGuinStar`, `oudomGuinCirc`, Prop 2.7.iii
  (`circ_mul_distrib_via_comul`).

## Status

Sorry-free.
-/


open ConnesKreimer
open PreLie.OudomGuinCirc

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### ε is multiplicative for the GL product

The cardinality preservation lemma `Nonplanar.insertionMultiset_card_eq`
(every `F' ∈ NIM(A, B)` has `|F'| = |A|`) and its planar substrate
`RoseTree.Pathed.insertionForest_length` now live in
`Linglib.Core.Algebra.RootedTree.PreLie.InsertionNonplanar`. -/

/-- `counit` of `insertionBasis A B` equals `if A = 0 ∧ B = 0 then 1 else 0`.
    For non-zero host A: every NIM output has cardinality |A| ≥ 1, so ε = 0.
    For host A = 0: NIM(0, B) = {0} iff B = 0, else empty. -/
private theorem counit_insertionBasis (A B : Forest (Nonplanar α)) :
    (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (unop
          (insertionBasis (R := R) A B)) =
      (counit (ConnesKreimer.of' A : ConnesKreimer R (Nonplanar α))) *
        (counit (ConnesKreimer.of' B : ConnesKreimer R (Nonplanar α))) := by
  -- Unfold insertionBasis: sum over NIM(A, B) of of' F'.
  -- ε of sum = sum of ε. ε(of' F') = if F'.card = 0 then 1 else 0.
  -- Case on A:
  -- * A = 0: NIM(0, B) handled by insertionMultiset_zero_left / _zero_right.
  -- * A ≠ 0: every F' has |F'| = |A| ≥ 1, so ε(of' F') = 0, sum = 0.
  unfold insertionBasis
  -- Goal: counit (unop ((NIM A B).map (fun F' => of' F')).sum) =
  --        counit (of' A) * counit (of' B)
  show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
      ((Nonplanar.insertionMultiset A B).map
        fun F' => ConnesKreimer.of' (R := R) F').sum =
    _
  -- counit (Σ ...) = Σ counit (...).
  rw [show ((Nonplanar.insertionMultiset A B).map
        fun F' => ConnesKreimer.of' (R := R) F').sum =
      ((Nonplanar.insertionMultiset A B).map
        fun F' => ConnesKreimer.of' (R := R) F').sum from rfl]
  -- Use additivity of counit through Multiset.sum.
  rw [show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        ((Nonplanar.insertionMultiset A B).map
          (fun F' => ConnesKreimer.of' (R := R) F')).sum =
      ((Nonplanar.insertionMultiset A B).map
        (fun F' => (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (ConnesKreimer.of' (R := R) F'))).sum from ?_]
  swap
  · -- counit preserves Multiset.sum via additivity.
    induction Nonplanar.insertionMultiset A B using Multiset.induction with
    | empty => simp
    | cons F' rest ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, map_add, ih]
  -- Now: (NIM(A, B).map (fun F' => counit (of' F'))).sum = counit (of' A) * counit (of' B).
  -- ε(of' F') = if F'.card = 0 then 1 else 0.
  simp only [ConnesKreimer.counit_of']
  -- Now: (NIM(A,B).map (fun F' => if F'.card = 0 then 1 else 0)).sum =
  --       (if A.card = 0 then 1 else 0) * (if B.card = 0 then 1 else 0)
  by_cases hA : A = 0
  · subst hA
    -- Case A = 0: NIM(0, B) = {0} if B = 0 else 0.
    by_cases hB : B = 0
    · subst hB
      -- NIM(0, 0) = {0}.
      rw [Nonplanar.insertionMultiset_zero_right]
      simp
    · -- NIM(0, B) = 0 for B ≠ 0 (no host vertices).
      rw [Nonplanar.insertionMultiset_zero_left_of_ne_zero B hB]
      simp [hB]
  · -- Case A ≠ 0: every F' ∈ NIM(A, B) has cardinality |A| ≥ 1, so F' ≠ 0.
    -- So ε(of' F') = 0 for every F'; sum = 0.
    -- And ε(of' A) = 0 (since A.card ≠ 0).
    have hAcard : A.card ≠ 0 := fun hc => hA (Multiset.card_eq_zero.mp hc)
    rw [if_neg hAcard, zero_mul]
    -- Need: (NIM(A,B).map (fun F' => if F'.card = 0 then 1 else 0)).sum = 0.
    apply Multiset.sum_eq_zero
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨F', hF', hF'_eq⟩ := hx
    rw [← hF'_eq]
    -- |F'| = |A| ≠ 0.
    have hF'card : F'.card = A.card :=
      Nonplanar.insertionMultiset_card_eq A B hF'
    rw [hF'card, if_neg hAcard]

/-- The counit `ε` on CK is multiplicative for the GL product on basis.
    `ε(of' A *_GL of' B) = ε(of' A) · ε(of' B)`.

    Proof by case on `B`:
    * `B = 0`: GL product reduces to `of' A` (right unit); `ε(of' A) = ε(of' A) · 1`.
    * `B ≠ 0`: `ε(of' B) = 0`, RHS = 0. Expand LHS via `mul_of'_sum_form`;
      each summand has `ε(of'(B - B₁))` factor, non-zero only when `B - B₁ = 0`
      i.e. `B₁ = B`; then `ε(unop(insertion(of' A)(of' B))) = ε(of' A) · ε(of' B) = 0`
      via `counit_insertionBasis`. -/
private theorem counit_gl_mul_basis (A B : Forest (Nonplanar α)) :
    (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (unop
          ((GrossmanLarson.of' (R := R) A : GrossmanLarson R α) *
            GrossmanLarson.of' B)) =
      (counit (ConnesKreimer.of' A : ConnesKreimer R (Nonplanar α))) *
        (counit (ConnesKreimer.of' B : ConnesKreimer R (Nonplanar α))) := by
  by_cases hB : B = 0
  · subst hB
    -- of' A *_GL of' 0 = of' A *_GL 1 = of' A.
    have h_of_zero : (GrossmanLarson.of' (R := R) (0 : Forest (Nonplanar α)) :
          GrossmanLarson R α) = 1 := GrossmanLarson.of'_zero
    rw [h_of_zero, mul_one]
    show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (ConnesKreimer.of' A) =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (ConnesKreimer.of' A) *
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (ConnesKreimer.of' (0 : Forest (Nonplanar α)))
    rw [show (ConnesKreimer.of' (0 : Forest (Nonplanar α)) :
            ConnesKreimer R (Nonplanar α)) = 1 from
        ConnesKreimer.of'_zero, map_one]
    ring
  · -- B ≠ 0: counit(of' B) = 0, RHS = counit(of' A) * 0 = 0.
    have hBcard : B.card ≠ 0 := fun hc => hB (Multiset.card_eq_zero.mp hc)
    have hCBzero : (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (ConnesKreimer.of' B) = 0 := by
      rw [ConnesKreimer.counit_of', if_neg hBcard]
    rw [hCBzero, mul_zero]
    -- Strategy: expand of' A * of' B via productForest formula, push counit through
    -- the Multiset.sum, show each summand reduces to counit(of' A) * counit(of' B) = 0,
    -- so the sum is 0.
    -- Helper: per-summand (CK product after unop) identity.
    have h_summand : ∀ B₁ : Forest (Nonplanar α),
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          ((unop
              (insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            ConnesKreimer.of' (R := R) (B - B₁)) =
        (counit (ConnesKreimer.of' A : ConnesKreimer R (Nonplanar α))) *
          (counit (ConnesKreimer.of' (R := R) (B₁ + (B - B₁)) :
            ConnesKreimer R (Nonplanar α))) := by
      intro B₁
      -- counit (X *_CK Y) = counit X * counit Y (algebra hom).
      rw [map_mul]
      -- Convert insertion (of' A) (of' B₁) → insertionBasis A B₁ (def via insertion_of'_of').
      rw [insertion_of'_of']
      -- counit (unop (insertionBasis A B₁)) = counit (of' A) * counit (of' B₁).
      rw [counit_insertionBasis A B₁]
      -- counit (of' (B₁ + (B - B₁))) = counit (of' B₁ * of'(B - B₁))
      --                              = counit (of' B₁) * counit (of'(B - B₁)).
      rw [show (ConnesKreimer.of' (R := R) (B₁ + (B - B₁)) :
              ConnesKreimer R (Nonplanar α)) =
            ConnesKreimer.of' (R := R) B₁ * ConnesKreimer.of' (R := R) (B - B₁) from
          ConnesKreimer.of'_add B₁ (B - B₁)]
      rw [map_mul]
      ring
    -- Outer: expand (of' A) * (of' B) via productForest, push counit through sum.
    -- Generic helper: push counit (algebra hom) ∘ unop through Multiset.sum.
    -- (unop is identity coercion, so this reduces to map_multiset_sum on counit.)
    have h_push_counit_unop_sum : ∀ s : Multiset (GrossmanLarson R α),
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
            (unop s.sum) =
          (s.map (fun x =>
            (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
              (unop x))).sum :=
      fun s => map_multiset_sum (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) s
    -- Each summand of the productForest sum reduces to 0 after counit ∘ unop:
    -- op (unop(insertion (of' A) (of' B₁)) * unop(of'(B-B₁))) — after unop on the outer,
    -- becomes the inner CK product. counit applied via h_summand: = 0 for B₁ ⊆ B.
    have h_each_zero : ∀ x ∈ B.powerset.map (fun B₁ =>
        op
          ((unop
              (insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            unop (GrossmanLarson.of' (B - B₁)))),
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (unop x) = 0 := by
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨B₁, hB₁, hx_eq⟩ := hx
      have hB₁le : B₁ ≤ B := Multiset.mem_powerset.mp hB₁
      have hB₁add : B₁ + (B - B₁) = B := by
        rw [add_comm]; exact Multiset.sub_add_cancel hB₁le
      rw [← hx_eq]
      show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          ((unop
              (insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            unop (GrossmanLarson.of' (B - B₁))) = 0
      show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          ((unop
              (insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            ConnesKreimer.of' (R := R) (B - B₁)) = 0
      rw [h_summand B₁, hB₁add, hCBzero, mul_zero]
    -- Now compute LHS via productForest expansion.
    rw [GrossmanLarson.of'_mul_of']
    unfold productForest
    -- Goal: counit (unop ((B.powerset.map ...).sum)) = 0
    rw [h_push_counit_unop_sum]
    -- Goal: ((B.powerset.map ...).map (fun x => counit (unop x))).sum = 0
    apply Multiset.sum_eq_zero
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨x, hx, hy_eq⟩ := hy
    rw [← hy_eq]
    exact h_each_zero x hx

/-- The counit `ε` on CK is multiplicative for the GL product: both sides
    of `ε (x ⋆ y) = ε x · ε y` are bilinear (`product` is bundled), so basis
    extensionality reduces to `counit_gl_mul_basis`. -/
theorem counit_gl_mul (x y : ConnesKreimer R (Nonplanar α)) :
    (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (product (R := R) x y) =
      (counit x) * (counit y) := by
  let mulCK : ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
    product (R := R) (α := α)
  have h : mulCK.compr₂
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R).toLinearMap =
      LinearMap.smulRight
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R).toLinearMap
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R).toLinearMap :=
    ConnesKreimer.lhom_ext' fun A => ConnesKreimer.lhom_ext' fun B =>
      counit_gl_mul_basis A B
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y


/-! ### Phase D's pairing-side recurrence -/

/-- The pairing-side recurrence: `⟨X ⋆ Y, B+_a z⟩` unfolds via the B+/B-
    adjoint + the derivation identity:
    `⟨X ⋆ Y, B+_a z⟩ = ε(X) · ⟨B-_a Y, z⟩ + ⟨B-_a X ⋆ Y, z⟩`. -/
theorem pairing_apply_bPlus_gl_mul (a : α)
    (X Y z : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) (product (R := R) X Y)
      (ConnesKreimer.bPlusLin (R := R) a z) =
      (counit X) * pairing (R := R) (bMinusLin (R := R) a Y) z +
      pairing (R := R) (product (R := R) (bMinusLin (R := R) a X) Y) z := by
  rw [← bMinusLin_pairing_adjoint a (product (R := R) X Y) z,
      bMinusLin_gl_mul, LinearMap.map_add, LinearMap.add_apply,
      show pairing (R := R)
          (((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) X) •
            bMinusLin (R := R) a Y) =
        ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) X) •
          pairing (R := R) (bMinusLin a Y) from
        LinearMap.map_smul (pairing : ConnesKreimer R _ →ₗ[R] _) _ _,
      LinearMap.smul_apply, smul_eq_mul]
  rfl

/-! ### Phase D main: Q5c via pairing nondegeneracy -/

/-- **Q5c via OG B+/B- duality**: `ckIso (X ★ Y) = unop (op (ckIso X) *
    op (ckIso Y))`. OG paper §3.2 Prop 3.2's statement, restated here
    as the entry point for the pairing-route Phase D.

    **Closure note (2026-05-17)**: After Phase B+C+D substrates closed
    (Steps 1, 3, 4, 5), an audit revealed the pairing-route induction on
    `z`'s B+ structure requires an LHS recurrence
    `bMinusLin a (ckIso (X★Y)) = ε(ckIso X) • bMinusLin a (ckIso Y)
                                + ckIso (B⁻_SL X ★ Y)` — which is OG
    Prop 3.2 transported via ckIso, and equivalent to Q5c itself
    (circular without independent OG-side machinery).

    The pairing route's *strict* advantage over the existing tprod-route
    (`gl_product_eq_oudomGuinStar`) was meant to be: bypass substrate 2
    (the deprecated `GL_product_split_mul_ι`) by replacing combinatorial
    GL surgery with the linear-algebra `pairing_nondegenerate` + B+/B-
    duality. But the induction on z bottoms out at z = 1 (counit-side,
    closed via `counit_gl_mul`) and reduces the step case
    `z = B+_a w` to a recurrence on `bMinusLin a (ckIso (X★Y))` that
    has no formula independent of Q5c.

    Conclusion: delegate to the existing `gl_product_eq_oudomGuinStar`
    (still substrate-2-blocked). Phases A-D and their helpers
    (`bMinusLin_gl_mul`, `counit_gl_mul`, `pairing_apply_bPlus_gl_mul`)
    remain useful infrastructure for future approaches. -/
theorem gl_product_eq_oudomGuinStar_via_pairing
    (X Y : SymmetricAlgebra ℤ (InsertionAlgebra α)) :
    ((ckIsoSymmetricAlgebra (oudomGuinStar X Y) : ConnesKreimer ℤ (Nonplanar α)) :
      GrossmanLarson ℤ α) =
      (op (ckIsoSymmetricAlgebra X)) *
      (op (ckIsoSymmetricAlgebra Y)) :=
  gl_product_eq_oudomGuinStar X Y

end GrossmanLarson

