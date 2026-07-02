/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.BMinus
import Linglib.Core.Algebra.RootedTree.PreLie.OudomGuinBridge
import Mathlib.Tactic.Ring

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

* Phase A: pairing on CK + nondegeneracy (`GrossmanLarsonPairing.lean`).
* Phase B: B+/B- adjoint (`BMinus.lean::bMinusLin_pairing_adjoint`).
* Phase C: OG identity (`BMinus.lean::bMinusLin_gl_mul`), currently
  sorry-fenced with substrate gap at `singleton_node_a_insertion_eq_bPlus_gl_mul`.
* OG S(L) machinery: `oudomGuinStar`, `oudomGuinCirc`, sorry-free
  Prop 2.7.iii (`circ_mul_distrib_via_comul`) etc.

## Status

Skeleton only. Sub-proofs sorry-fenced for incremental closure.
-/

namespace RootedTree

open ConnesKreimer
open PreLie.OudomGuinCirc

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq (Nonplanar α)]

/-! ### ε is multiplicative for the GL product

The cardinality preservation lemma `Nonplanar.insertionMultiset_card_eq`
(every `F' ∈ NIM(A, B)` has `|F'| = |A|`) and its planar substrate
`RoseTree.Pathed.insertionForest_length` now live in
`Linglib.Core.Combinatorics.RootedTree.Nonplanar.Insertion`. -/

/-- `counit` of `insertionBasis A B` equals `if A = 0 ∧ B = 0 then 1 else 0`.
    For non-zero host A: every NIM output has cardinality |A| ≥ 1, so ε = 0.
    For host A = 0: NIM(0, B) = {0} iff B = 0, else empty. -/
private theorem counit_insertionBasis (A B : Forest (Nonplanar α)) :
    (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (GrossmanLarson.unop
          (GrossmanLarson.insertionBasis (R := R) A B)) =
      (counit (ConnesKreimer.of' A : ConnesKreimer R (Nonplanar α))) *
        (counit (ConnesKreimer.of' B : ConnesKreimer R (Nonplanar α))) := by
  -- Unfold insertionBasis: sum over NIM(A, B) of of' F'.
  -- ε of sum = sum of ε. ε(of' F') = if F'.card = 0 then 1 else 0.
  -- Case on A:
  -- * A = 0: NIM(0, B) handled by insertionMultiset_zero_left / _zero_right.
  -- * A ≠ 0: every F' has |F'| = |A| ≥ 1, so ε(of' F') = 0, sum = 0.
  unfold GrossmanLarson.insertionBasis
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
        (GrossmanLarson.unop
          ((GrossmanLarson.of' (R := R) A : GrossmanLarson R α) *
            GrossmanLarson.of' B)) =
      (counit (ConnesKreimer.of' A : ConnesKreimer R (Nonplanar α))) *
        (counit (ConnesKreimer.of' B : ConnesKreimer R (Nonplanar α))) := by
  by_cases hB : B = 0
  · subst hB
    -- of' A *_GL of' 0 = of' A *_GL 1 = of' A.
    have h_of_zero : (GrossmanLarson.of' (R := R) (0 : Forest (Nonplanar α)) :
          GrossmanLarson R α) = 1 := GrossmanLarson.of'_zero
    rw [h_of_zero, GrossmanLarson.mul_one]
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
    -- Override DecidableEq with Classical so that B.powerset, B - B₁, etc. match
    -- the instance used in productForest's `letI : DecidableEq ... := Classical.decEq _`.
    letI : DecidableEq (Nonplanar α) := Classical.decEq _
    -- Strategy: expand of' A * of' B via productForest formula, push counit through
    -- the Multiset.sum, show each summand reduces to counit(of' A) * counit(of' B) = 0,
    -- so the sum is 0.
    -- Helper: per-summand (CK product after unop) identity.
    have h_summand : ∀ B₁ : Forest (Nonplanar α),
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          ((GrossmanLarson.unop
              (GrossmanLarson.insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            ConnesKreimer.of' (R := R) (B - B₁)) =
        (counit (ConnesKreimer.of' A : ConnesKreimer R (Nonplanar α))) *
          (counit (ConnesKreimer.of' (R := R) (B₁ + (B - B₁)) :
            ConnesKreimer R (Nonplanar α))) := by
      intro B₁
      -- counit (X *_CK Y) = counit X * counit Y (algebra hom).
      rw [map_mul]
      -- Convert insertion (of' A) (of' B₁) → insertionBasis A B₁ (def via insertion_of'_of').
      rw [GrossmanLarson.insertion_of'_of']
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
            (GrossmanLarson.unop s.sum) =
          (s.map (fun x =>
            (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
              (GrossmanLarson.unop x))).sum :=
      fun s => map_multiset_sum (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) s
    -- Each summand of the productForest sum reduces to 0 after counit ∘ unop:
    -- op (unop(insertion (of' A) (of' B₁)) * unop(of'(B-B₁))) — after unop on the outer,
    -- becomes the inner CK product. counit applied via h_summand: = 0 for B₁ ⊆ B.
    have h_each_zero : ∀ x ∈ B.powerset.map (fun B₁ =>
        GrossmanLarson.op
          ((GrossmanLarson.unop
              (GrossmanLarson.insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            GrossmanLarson.unop (GrossmanLarson.of' (B - B₁)))),
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (GrossmanLarson.unop x) = 0 := by
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨B₁, hB₁, hx_eq⟩ := hx
      have hB₁le : B₁ ≤ B := Multiset.mem_powerset.mp hB₁
      have hB₁add : B₁ + (B - B₁) = B := by
        rw [add_comm]; exact Multiset.sub_add_cancel hB₁le
      rw [← hx_eq]
      show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          ((GrossmanLarson.unop
              (GrossmanLarson.insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            GrossmanLarson.unop (GrossmanLarson.of' (B - B₁))) = 0
      show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          ((GrossmanLarson.unop
              (GrossmanLarson.insertion (R := R) (GrossmanLarson.of' A)
                (GrossmanLarson.of' B₁)) : ConnesKreimer R (Nonplanar α)) *
            ConnesKreimer.of' (R := R) (B - B₁)) = 0
      rw [h_summand B₁, hB₁add, hCBzero, mul_zero]
    -- Now compute LHS via productForest expansion.
    rw [GrossmanLarson.of'_mul_of']
    unfold GrossmanLarson.productForest
    -- Goal: counit (unop ((B.powerset.map ...).sum)) = 0
    rw [h_push_counit_unop_sum]
    -- Goal: ((B.powerset.map ...).map (fun x => counit (unop x))).sum = 0
    apply Multiset.sum_eq_zero
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨x, hx, hy_eq⟩ := hy
    rw [← hy_eq]
    exact h_each_zero x hx

/-- The counit `ε` on CK is multiplicative for the GL product.
    Bilinear extension of `counit_gl_mul_basis`. -/
theorem counit_gl_mul (x y : ConnesKreimer R (Nonplanar α)) :
    (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (GrossmanLarson.unop
          ((GrossmanLarson.op x : GrossmanLarson R α) * GrossmanLarson.op y)) =
      (counit x) * (counit y) := by
  refine ConnesKreimer.induction_linear x ?_ ?_ ?_
  · -- x = 0
    change (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (GrossmanLarson.unop
          ((0 : GrossmanLarson R α) * GrossmanLarson.op y)) =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) 0 *
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) y
    rw [GrossmanLarson.zero_mul_gl,
        show GrossmanLarson.unop (0 : GrossmanLarson R α) =
            (0 : ConnesKreimer R (Nonplanar α)) from rfl,
        map_zero, zero_mul]
  · -- x = x₁ + x₂
    intro x₁ x₂ ih₁ ih₂
    let x₁' : ConnesKreimer R (Nonplanar α) := x₁
    let x₂' : ConnesKreimer R (Nonplanar α) := x₂
    show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
        (GrossmanLarson.unop
          ((GrossmanLarson.op (x₁' + x₂') : GrossmanLarson R α) *
            GrossmanLarson.op y)) =
      (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) (x₁' + x₂') *
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) y
    rw [show (GrossmanLarson.op (x₁' + x₂') : GrossmanLarson R α) =
          GrossmanLarson.op x₁' + GrossmanLarson.op x₂' from rfl,
        add_mul,
        show GrossmanLarson.unop
              ((GrossmanLarson.op x₁' : GrossmanLarson R α) * GrossmanLarson.op y +
                GrossmanLarson.op x₂' * GrossmanLarson.op y) =
            GrossmanLarson.unop
                ((GrossmanLarson.op x₁' : GrossmanLarson R α) * GrossmanLarson.op y) +
              GrossmanLarson.unop
                (GrossmanLarson.op x₂' * GrossmanLarson.op y) from rfl,
        show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
              (GrossmanLarson.unop
                  ((GrossmanLarson.op x₁' : GrossmanLarson R α) * GrossmanLarson.op y) +
                GrossmanLarson.unop
                  (GrossmanLarson.op x₂' * GrossmanLarson.op y)) =
            counit (GrossmanLarson.unop
                  ((GrossmanLarson.op x₁' : GrossmanLarson R α) * GrossmanLarson.op y)) +
              counit (GrossmanLarson.unop
                (GrossmanLarson.op x₂' * GrossmanLarson.op y)) from
          map_add _ _ _]
    rw [ih₁, ih₂, map_add (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x₁' x₂']
    ring
  · -- x = single F r
    intro F r
    refine ConnesKreimer.induction_linear y ?_ ?_ ?_
    · -- y = 0
      let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
      change (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (GrossmanLarson.unop
            ((GrossmanLarson.op x_single : GrossmanLarson R α) *
              (0 : GrossmanLarson R α))) =
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x_single *
          (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) 0
      rw [GrossmanLarson.mul_zero_gl,
          show GrossmanLarson.unop (0 : GrossmanLarson R α) =
              (0 : ConnesKreimer R (Nonplanar α)) from rfl,
          map_zero, mul_zero]
    · -- y = y₁ + y₂
      intro y₁ y₂ ih₁ ih₂
      let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
      let y₁' : ConnesKreimer R (Nonplanar α) := y₁
      let y₂' : ConnesKreimer R (Nonplanar α) := y₂
      show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (GrossmanLarson.unop
            ((GrossmanLarson.op x_single : GrossmanLarson R α) *
              GrossmanLarson.op (y₁' + y₂'))) =
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x_single *
          (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) (y₁' + y₂')
      rw [show (GrossmanLarson.op (y₁' + y₂') : GrossmanLarson R α) =
            GrossmanLarson.op y₁' + GrossmanLarson.op y₂' from rfl,
          mul_add,
          show GrossmanLarson.unop
              ((GrossmanLarson.op x_single : GrossmanLarson R α) * GrossmanLarson.op y₁' +
                GrossmanLarson.op x_single * GrossmanLarson.op y₂') =
            GrossmanLarson.unop
                ((GrossmanLarson.op x_single : GrossmanLarson R α) * GrossmanLarson.op y₁') +
              GrossmanLarson.unop
                (GrossmanLarson.op x_single * GrossmanLarson.op y₂') from rfl,
          show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
                (GrossmanLarson.unop
                    ((GrossmanLarson.op x_single : GrossmanLarson R α) *
                      GrossmanLarson.op y₁') +
                  GrossmanLarson.unop
                    (GrossmanLarson.op x_single * GrossmanLarson.op y₂')) =
              counit (GrossmanLarson.unop
                    ((GrossmanLarson.op x_single : GrossmanLarson R α) *
                      GrossmanLarson.op y₁')) +
                counit (GrossmanLarson.unop
                  (GrossmanLarson.op x_single * GrossmanLarson.op y₂')) from
            map_add _ _ _]
      rw [ih₁, ih₂, map_add (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) y₁' y₂']
      ring
    · -- y = single G s: factor r, s, apply counit_gl_mul_basis F G
      intro G s
      let x_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single F r
      let y_single : ConnesKreimer R (Nonplanar α) := ConnesKreimer.single G s
      show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (GrossmanLarson.unop
            ((GrossmanLarson.op x_single : GrossmanLarson R α) *
              GrossmanLarson.op y_single)) =
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) x_single *
          (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) y_single
      have hx : x_single = r • (ConnesKreimer.of' (R := R) F) := by
        show (ConnesKreimer.single F r : ConnesKreimer R (Nonplanar α)) =
            r • (ConnesKreimer.single F (1 : R) : ConnesKreimer R (Nonplanar α))
        exact ConnesKreimer.smul_single_one F r
      have hy : y_single = s • (ConnesKreimer.of' (R := R) G) := by
        show (ConnesKreimer.single G s : ConnesKreimer R (Nonplanar α)) =
            s • (ConnesKreimer.single G (1 : R) : ConnesKreimer R (Nonplanar α))
        exact ConnesKreimer.smul_single_one G s
      rw [hx, hy]
      -- Pull r, s through op and *.
      rw [show (GrossmanLarson.op (r • ConnesKreimer.of' (R := R) F) :
            GrossmanLarson R α) =
          r • GrossmanLarson.op (ConnesKreimer.of' (R := R) F) from rfl,
          show (GrossmanLarson.op (s • ConnesKreimer.of' (R := R) G) :
            GrossmanLarson R α) =
          s • GrossmanLarson.op (ConnesKreimer.of' (R := R) G) from rfl,
          GrossmanLarson.smul_mul_gl, GrossmanLarson.mul_smul_gl]
      -- unop is linear (rfl), counit is linear → pull r, s out.
      rw [show GrossmanLarson.unop (r • s • ((GrossmanLarson.op
              (ConnesKreimer.of' (R := R) F) : GrossmanLarson R α) *
                GrossmanLarson.op (ConnesKreimer.of' (R := R) G))) =
            r • s • GrossmanLarson.unop ((GrossmanLarson.op
                (ConnesKreimer.of' (R := R) F) : GrossmanLarson R α) *
                GrossmanLarson.op (ConnesKreimer.of' (R := R) G)) from rfl,
          show (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
              (r • s • GrossmanLarson.unop ((GrossmanLarson.op
                  (ConnesKreimer.of' (R := R) F) : GrossmanLarson R α) *
                  GrossmanLarson.op (ConnesKreimer.of' (R := R) G))) =
            r • s • (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
              (GrossmanLarson.unop ((GrossmanLarson.op
                  (ConnesKreimer.of' (R := R) F) : GrossmanLarson R α) *
                  GrossmanLarson.op (ConnesKreimer.of' (R := R) G))) from by
          rw [map_smul (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R),
              map_smul (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)]]
      -- Apply counit_gl_mul_basis F G via `change` to bridge op (CK.of' _) → GL.of' _.
      change r • s • (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (GrossmanLarson.unop
            ((GrossmanLarson.of' (R := R) F : GrossmanLarson R α) *
              GrossmanLarson.of' G)) =
        (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
            (r • ConnesKreimer.of' (R := R) F) *
          (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
            (s • ConnesKreimer.of' (R := R) G)
      rw [counit_gl_mul_basis F G,
          map_smul (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R),
          map_smul (counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)]
      -- Now both sides are r • s • (counit_F * counit_G) (with coefficient gymnastics).
      simp only [smul_eq_mul]
      ring

/-! ### Phase D's pairing-side recurrence -/

omit [DecidableEq (Nonplanar α)] in
/-- Phase D RHS recurrence: `⟨unop (op X * op Y), bPlusLin a z⟩` unfolds
    via B+/B- adjoint + Phase C `bMinusLin_gl_mul`.

    Specifically:
    `⟨unop (op X * op Y), B+_a z⟩ = ε(X) · ⟨B-_a Y, z⟩ + ⟨unop (op (B-_a X) * op Y), z⟩`. -/
theorem pairing_apply_bPlus_gl_mul (a : α)
    (X Y z : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) (GrossmanLarson.unop
        ((GrossmanLarson.op X : GrossmanLarson R α) * GrossmanLarson.op Y))
      (ConnesKreimer.bPlusLin (R := R) a z) =
      (counit X) * pairing (R := R) (bMinusLin (R := R) a Y) z +
      pairing (R := R) (GrossmanLarson.unop
          ((GrossmanLarson.op (bMinusLin (R := R) a X) : GrossmanLarson R α) *
            GrossmanLarson.op Y)) z := by
  -- Step 1: B+/B- adjoint: ⟨W, B+_a z⟩ = ⟨B-_a W, z⟩ with W = unop(op X * op Y).
  rw [← bMinusLin_pairing_adjoint a (GrossmanLarson.unop
        ((GrossmanLarson.op X : GrossmanLarson R α) * GrossmanLarson.op Y)) z]
  -- Step 2: Phase C identity: B-_a (unop (op X * op Y)) = ε(X) • B-_a Y + unop (op (B-_a X) * op Y).
  have hC := bMinusLin_gl_mul a X Y
  -- Express LHS bMinusLin a (op X * op Y).unop in form matching hC's LHS.
  have hLHS_form : bMinusLin (R := R) a
      (GrossmanLarson.unop
        ((GrossmanLarson.op X : GrossmanLarson R α) * GrossmanLarson.op Y)) =
    bMinusLin (R := R) a
      ((GrossmanLarson.op X : GrossmanLarson R α) * GrossmanLarson.op Y) := rfl
  rw [hLHS_form, hC]
  -- Step 3: pairing is additive in first arg.
  rw [LinearMap.map_add, LinearMap.add_apply]
  -- Step 4: pairing pulls out ε(X) scalar from the first summand.
  rw [show pairing (R := R)
        (((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) X) •
          bMinusLin (R := R) a Y) =
      ((counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) X) •
        pairing (R := R) (bMinusLin a Y) from
      LinearMap.map_smul (pairing : ConnesKreimer R _ →ₗ[R] _) _ _]
  rw [LinearMap.smul_apply]
  -- Goal: (counit X) • pairing (B-_a Y) z + pairing (unop (op (B-_a X) * op Y)) z
  --     = (counit X) * pairing (B-_a Y) z + pairing (unop (op (B-_a X) * op Y)) z
  rw [smul_eq_mul]

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
      (GrossmanLarson.op (ckIsoSymmetricAlgebra X)) *
      (GrossmanLarson.op (ckIsoSymmetricAlgebra Y)) :=
  gl_product_eq_oudomGuinStar X Y

end GrossmanLarson

end RootedTree
