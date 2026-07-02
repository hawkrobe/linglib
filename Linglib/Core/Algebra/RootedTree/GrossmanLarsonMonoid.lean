/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.GrossmanLarson
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonAssoc
import Linglib.Core.Algebra.RootedTree.PreLie.OudomGuinBridge

set_option autoImplicit false

/-!
# Grossman-Larson monoid structure
[grossman-larson-1989] [foissy-2021] [oudom-guin-2008]

Completes the multiplicative structure of `GrossmanLarson R α` (defined in
`GrossmanLarson.lean`) by lifting the integer-case associativity
`GrossmanLarson.mul_assoc_basis_via_oudom_guin_pbw` (proved sorry-free in
`OudomGuinBridge.lean` via Oudom-Guin + PBW) to arbitrary
`CommSemiring R`, then registering `Semigroup`/`Monoid` instances.

## Architecture

The lift uses the R-generic, basis-form closed expressions
`lhs_quadruple_form` and `rhs_quintuple_form` (in `GrossmanLarsonAssoc.lean`),
which present both sides of `(of' F₁) * (of' F₂) * (of' F₃) = (of' F₁) *
((of' F₂) * (of' F₃))` as `(M.map of').sum` for R-independent multisets `M
: Multiset (Forest (Nonplanar α))`. The integer case implies the indexing
multisets are equal (via `Finsupp` coefficient extraction + Nat→ℤ
injectivity), and that R-free equality re-applies for any R.

## Main results (all `α : Type*`-generic)

* `mul_assoc_basis` (R-generic) : `(of' F₁ * of' F₂) * of' F₃ =
  of' F₁ * (of' F₂ * of' F₃)` on basis vectors.
* `mul_assoc` (R-generic) : full associativity, by triple
  `ConnesKreimer.addHom_ext`.
* `instSemigroup`, `instMonoid` instances.

## Status

`[UPSTREAM]` candidate. All results sorry-free.
-/

namespace RootedTree

namespace GrossmanLarson

variable {α : Type*}

/-! ### `(M.map of').sum` coefficient extraction (multiset injectivity) -/

/-- Coefficient of `((M.map of').sum)` at `H` is `M.count H`, mapped from
    Nat to R. Holds for any `CommSemiring R`. Used to extract multiset
    equality from sum equality at `R = ℤ`. -/
private theorem sum_of'_apply
    {R : Type*} [CommSemiring R] [DecidableEq (Nonplanar α)]
    (M : Multiset (Forest (Nonplanar α))) (H : Forest (Nonplanar α)) :
    (((M.map (fun F => (of' (R := R) F : GrossmanLarson R α))).sum :
        GrossmanLarson R α) H : R) = (M.count H : R) := by
  induction M using Multiset.induction with
  | empty =>
    rw [Multiset.map_zero, Multiset.sum_zero, Multiset.count_zero, Nat.cast_zero]
    rfl
  | cons F M ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.count_cons]
    -- Step 1: split + through FunLike (Finsupp.add_apply).
    show ((of' (R := R) F : GrossmanLarson R α) +
            (M.map (fun F => (of' (R := R) F : GrossmanLarson R α))).sum) H =
          ((M.count H + (if H = F then 1 else 0) : ℕ) : R)
    rw [show ((of' (R := R) F : GrossmanLarson R α) +
              (M.map (fun F => (of' (R := R) F : GrossmanLarson R α))).sum) H =
            (of' (R := R) F : GrossmanLarson R α) H +
            ((M.map (fun F => (of' (R := R) F : GrossmanLarson R α))).sum) H
          from Finsupp.add_apply _ _ _]
    rw [ih]
    -- Step 2: of' F = Finsupp.single F 1.
    show (Finsupp.single F (1 : R)) H + (M.count H : R) =
          ((M.count H + (if H = F then 1 else 0) : ℕ) : R)
    rw [Finsupp.single_apply]
    -- Goal: (if F = H then (1 : R) else 0) + (M.count H : R)
    --     = ((M.count H + (if H = F then 1 else 0) : ℕ) : R)
    rw [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    by_cases hFH : F = H
    · rw [if_pos hFH, if_pos hFH.symm, add_comm]
    · rw [if_neg hFH, if_neg (fun h => hFH h.symm), add_comm]

/-- Multiset equality at `R = ℤ` from sum equality. -/
private theorem multiset_eq_of_sum_eq_int [DecidableEq (Nonplanar α)]
    (M₁ M₂ : Multiset (Forest (Nonplanar α)))
    (h : ((M₁.map (fun F => (of' (R := ℤ) F : GrossmanLarson ℤ α))).sum :
          GrossmanLarson ℤ α) =
         (M₂.map (fun F => (of' (R := ℤ) F : GrossmanLarson ℤ α))).sum) :
    M₁ = M₂ := by
  apply Multiset.ext.mpr
  intro H
  have h1 := sum_of'_apply (R := ℤ) M₁ H
  have h2 := sum_of'_apply (R := ℤ) M₂ H
  -- From h: the sums are equal as GL ℤ α, so their FunLike values at H agree.
  have heq : ((((M₁.map (fun F => (of' (R := ℤ) F : GrossmanLarson ℤ α))).sum :
                GrossmanLarson ℤ α) H : ℤ)) =
             (((M₂.map (fun F => (of' (R := ℤ) F : GrossmanLarson ℤ α))).sum :
                GrossmanLarson ℤ α) H : ℤ) := by
    rw [h]
  rw [h1, h2] at heq
  exact_mod_cast heq

/-- Map-then-sum of `of'` is preserved under multiset equality (R-generic). -/
private theorem sum_of'_congr
    {R : Type*} [CommSemiring R]
    {M₁ M₂ : Multiset (Forest (Nonplanar α))} (h : M₁ = M₂) :
    ((M₁.map (fun F => (of' (R := R) F : GrossmanLarson R α))).sum :
      GrossmanLarson R α) =
    (M₂.map (fun F => (of' (R := R) F : GrossmanLarson R α))).sum := by
  rw [h]

/-! ### `mul_assoc_basis` (R-generic) via the ℤ-case + multiset lift -/

/-- The LHS indexing multiset for `(of' F₁ * of' F₂) * of' F₃`.
    R-independent; abstracts `lhs_quadruple_form`'s closed form. -/
private noncomputable def lhsMultiset
    (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    Multiset (Forest (Nonplanar α)) :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  F₂.powerset.bind fun B₁ =>
    (Nonplanar.insertionMultiset F₁ B₁).bind fun X =>
      F₃.powerset.bind fun C₁ =>
        C₁.powerset.bind fun D =>
          ((Nonplanar.insertionMultiset X D) ×ˢ
            (Nonplanar.insertionMultiset (F₂ - B₁) (C₁ - D))).map
              fun p => p.1 + p.2 + (F₃ - C₁)

/-- The RHS indexing multiset for `of' F₁ * (of' F₂ * of' F₃)`. -/
private noncomputable def rhsMultiset
    (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    Multiset (Forest (Nonplanar α)) :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  F₃.powerset.bind fun C₁' =>
    (Nonplanar.insertionMultiset F₂ C₁').bind fun Z =>
      Z.powerset.bind fun P_Z =>
        (F₃ - C₁').powerset.bind fun P_F =>
          (Nonplanar.insertionMultiset F₁ (P_Z + P_F)).map
            fun W => W + ((Z - P_Z) + ((F₃ - C₁') - P_F))

/-- LHS = sum-of-`of'` over `lhsMultiset` (R-generic). -/
private theorem lhs_eq_sum_of'
    {R : Type*} [CommSemiring R]
    (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    ((of' F₁ : GrossmanLarson R α) * of' F₂) * of' F₃ =
      (((lhsMultiset F₁ F₂ F₃).map
          (fun F => (of' (R := R) F : GrossmanLarson R α))).sum :
        GrossmanLarson R α) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  rw [lhs_quadruple_form]
  -- Goal: nested-bind sum with `of'` inside = (lhsMultiset.map of').sum
  -- Push `map of'` outside by induction over the binds.
  unfold lhsMultiset
  -- The inner-most layer: `(...).map fun p => of' (p.1+p.2+(F₃-C₁))`
  --  vs. `((...).map fun p => p.1+p.2+(F₃-C₁)).map of'` — Multiset.map_map.
  -- We turn the nested binds into one bind via Multiset.map_bind on each layer.
  -- Equivalent: rewrite `(A.bind f).map g = A.bind (fun a => (f a).map g)`.
  simp only [Multiset.map_bind, Multiset.map_map, Function.comp]

/-- RHS = sum-of-`of'` over `rhsMultiset` (R-generic). -/
private theorem rhs_eq_sum_of'
    {R : Type*} [CommSemiring R]
    (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    (of' F₁ : GrossmanLarson R α) * (of' F₂ * of' F₃) =
      (((rhsMultiset F₁ F₂ F₃).map
          (fun F => (of' (R := R) F : GrossmanLarson R α))).sum :
        GrossmanLarson R α) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  rw [rhs_quintuple_form]
  unfold rhsMultiset
  simp only [Multiset.map_bind, Multiset.map_map, Function.comp]

/-- The LHS and RHS indexing multisets are equal (R-free). Proved by
    invoking the closed integer case `mul_assoc_basis_via_oudom_guin_pbw`
    and pulling out the multiset equality via `Finsupp` coefficient
    extraction. -/
private theorem lhsMultiset_eq_rhsMultiset [DecidableEq (Nonplanar α)]
    (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    lhsMultiset F₁ F₂ F₃ = rhsMultiset F₁ F₂ F₃ := by
  apply multiset_eq_of_sum_eq_int
  -- Reduce to associativity equation at ℤ.
  rw [← lhs_eq_sum_of' (R := ℤ), ← rhs_eq_sum_of' (R := ℤ)]
  exact mul_assoc_basis_via_oudom_guin_pbw F₁ F₂ F₃

/-- **Basis-level associativity** (R-generic, `α : Type*`). Lifts the
    integer case `mul_assoc_basis_via_oudom_guin_pbw` (Q6, proved
    sorry-free in `OudomGuinBridge.lean`) to arbitrary
    `CommSemiring R` via R-free multiset identification. -/
theorem mul_assoc_basis {R : Type*} [CommSemiring R]
    (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    ((of' F₁ : GrossmanLarson R α) * of' F₂) * of' F₃ =
      of' F₁ * (of' F₂ * of' F₃) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  rw [lhs_eq_sum_of' (R := R), rhs_eq_sum_of' (R := R),
      sum_of'_congr (lhsMultiset_eq_rhsMultiset F₁ F₂ F₃)]

/-! ### Full `mul_assoc` via triple `ConnesKreimer.addHom_ext` -/

/-- Right multiplication by `y` as an `AddMonoidHom`, additive in `x`. -/
private noncomputable def mulRightHom
    {R : Type*} [CommSemiring R] (y : GrossmanLarson R α) :
    GrossmanLarson R α →+ GrossmanLarson R α where
  toFun x := x * y
  map_zero' := by
    show product 0 y = 0
    rw [product.map_zero, LinearMap.zero_apply]
  map_add' x₁ x₂ := by
    show product (x₁ + x₂) y = product x₁ y + product x₂ y
    rw [product.map_add, LinearMap.add_apply]

/-- Left multiplication by `x` as an `AddMonoidHom`, additive in `y`. -/
private noncomputable def mulLeftHom
    {R : Type*} [CommSemiring R] (x : GrossmanLarson R α) :
    GrossmanLarson R α →+ GrossmanLarson R α where
  toFun y := x * y
  map_zero' := by
    show product x 0 = 0
    exact (product x).map_zero
  map_add' y₁ y₂ := by
    show product x (y₁ + y₂) = product x y₁ + product x y₂
    exact (product x).map_add y₁ y₂

@[simp] private theorem mulRightHom_apply
    {R : Type*} [CommSemiring R] (x y : GrossmanLarson R α) :
    mulRightHom y x = x * y := rfl

@[simp] private theorem mulLeftHom_apply
    {R : Type*} [CommSemiring R] (x y : GrossmanLarson R α) :
    mulLeftHom x y = x * y := rfl

/-- Scalar pull-out on the LEFT factor: `(c • x) * y = c • (x * y)`. -/
private theorem smul_mul_left
    {R : Type*} [CommSemiring R] (c : R) (x y : GrossmanLarson R α) :
    ((c • x : GrossmanLarson R α) * y) = c • (x * y) := by
  show product (c • x) y = c • product x y
  rw [product.map_smul, LinearMap.smul_apply]

/-- Scalar pull-out on the RIGHT factor: `x * (c • y) = c • (x * y)`. -/
private theorem mul_smul_right
    {R : Type*} [CommSemiring R] (c : R) (x y : GrossmanLarson R α) :
    (x * (c • y : GrossmanLarson R α)) = c • (x * y) := by
  show product x (c • y) = c • product x y
  exact (product x).map_smul c y

/-- AddMonoidHom for `x ↦ x * y * z`, additive in `x`. -/
private noncomputable def assocLHSHom
    {R : Type*} [CommSemiring R] (y z : GrossmanLarson R α) :
    GrossmanLarson R α →+ GrossmanLarson R α :=
  (mulRightHom z).comp (mulRightHom y)

/-- AddMonoidHom for `x ↦ x * (y * z)`, additive in `x`. -/
private noncomputable def assocRHSHom
    {R : Type*} [CommSemiring R] (y z : GrossmanLarson R α) :
    GrossmanLarson R α →+ GrossmanLarson R α :=
  mulRightHom (y * z)

@[simp] private theorem assocLHSHom_apply
    {R : Type*} [CommSemiring R] (x y z : GrossmanLarson R α) :
    assocLHSHom y z x = x * y * z := rfl

@[simp] private theorem assocRHSHom_apply
    {R : Type*} [CommSemiring R] (x y z : GrossmanLarson R α) :
    assocRHSHom y z x = x * (y * z) := rfl

/-- AddMonoidHom for `y ↦ x * y * z`, additive in `y`. -/
private noncomputable def assocLHSHomY
    {R : Type*} [CommSemiring R] (x z : GrossmanLarson R α) :
    GrossmanLarson R α →+ GrossmanLarson R α :=
  (mulRightHom z).comp (mulLeftHom x)

/-- AddMonoidHom for `y ↦ x * (y * z)`, additive in `y`. -/
private noncomputable def assocRHSHomY
    {R : Type*} [CommSemiring R] (x z : GrossmanLarson R α) :
    GrossmanLarson R α →+ GrossmanLarson R α :=
  (mulLeftHom x).comp (mulRightHom z)

@[simp] private theorem assocLHSHomY_apply
    {R : Type*} [CommSemiring R] (x y z : GrossmanLarson R α) :
    assocLHSHomY x z y = x * y * z := rfl

@[simp] private theorem assocRHSHomY_apply
    {R : Type*} [CommSemiring R] (x y z : GrossmanLarson R α) :
    assocRHSHomY x z y = x * (y * z) := by
  show (mulLeftHom x) ((mulRightHom z) y) = x * (y * z)
  rfl

/-- AddMonoidHom for `z ↦ x * y * z`, additive in `z`. -/
private noncomputable def assocLHSHomZ
    {R : Type*} [CommSemiring R] (x y : GrossmanLarson R α) :
    GrossmanLarson R α →+ GrossmanLarson R α :=
  (mulLeftHom (x * y))

/-- AddMonoidHom for `z ↦ x * (y * z)`, additive in `z`. -/
private noncomputable def assocRHSHomZ
    {R : Type*} [CommSemiring R] (x y : GrossmanLarson R α) :
    GrossmanLarson R α →+ GrossmanLarson R α :=
  (mulLeftHom x).comp (mulLeftHom y)

@[simp] private theorem assocLHSHomZ_apply
    {R : Type*} [CommSemiring R] (x y z : GrossmanLarson R α) :
    assocLHSHomZ x y z = x * y * z := rfl

@[simp] private theorem assocRHSHomZ_apply
    {R : Type*} [CommSemiring R] (x y z : GrossmanLarson R α) :
    assocRHSHomZ x y z = x * (y * z) := by
  show (mulLeftHom x) ((mulLeftHom y) z) = x * (y * z)
  rfl

/-- **Associativity** (R-generic, `α : Type*`). Triple bilinearity
    reduction to `mul_assoc_basis`. -/
theorem mul_assoc {R : Type*} [CommSemiring R]
    (F₁ F₂ F₃ : GrossmanLarson R α) :
    F₁ * F₂ * F₃ = F₁ * (F₂ * F₃) := by
  have h₁ : assocLHSHom F₂ F₃ = assocRHSHom F₂ F₃ := by
    refine ConnesKreimer.addHom_ext (T := Nonplanar α)
      (M := GrossmanLarson R α) fun T₁ a₁ => ?_
    set s₁ : GrossmanLarson R α := ConnesKreimer.single T₁ a₁ with s₁_def
    show assocLHSHom F₂ F₃ s₁ = assocRHSHom F₂ F₃ s₁
    rw [assocLHSHom_apply, assocRHSHom_apply]
    have h₂ : assocLHSHomY s₁ F₃ = assocRHSHomY s₁ F₃ := by
      refine ConnesKreimer.addHom_ext (T := Nonplanar α)
        (M := GrossmanLarson R α) fun T₂ a₂ => ?_
      set s₂ : GrossmanLarson R α := ConnesKreimer.single T₂ a₂ with s₂_def
      show assocLHSHomY s₁ F₃ s₂ = assocRHSHomY s₁ F₃ s₂
      rw [assocLHSHomY_apply, assocRHSHomY_apply]
      have h₃ : assocLHSHomZ s₁ s₂ = assocRHSHomZ s₁ s₂ := by
        refine ConnesKreimer.addHom_ext (T := Nonplanar α)
          (M := GrossmanLarson R α) fun T₃ a₃ => ?_
        set s₃ : GrossmanLarson R α := ConnesKreimer.single T₃ a₃ with s₃_def
        show assocLHSHomZ s₁ s₂ s₃ = assocRHSHomZ s₁ s₂ s₃
        rw [assocLHSHomZ_apply, assocRHSHomZ_apply]
        rw [show s₁ = a₁ • (of' T₁ : GrossmanLarson R α) from
              ConnesKreimer.smul_single_one T₁ a₁,
            show s₂ = a₂ • (of' T₂ : GrossmanLarson R α) from
              ConnesKreimer.smul_single_one T₂ a₂,
            show s₃ = a₃ • (of' T₃ : GrossmanLarson R α) from
              ConnesKreimer.smul_single_one T₃ a₃]
        simp only [smul_mul_left, mul_smul_right]
        rw [mul_assoc_basis T₁ T₂ T₃]
      have h₃App := DFunLike.congr_fun h₃ F₃
      rw [assocLHSHomZ_apply, assocRHSHomZ_apply] at h₃App
      exact h₃App
    have h₂App := DFunLike.congr_fun h₂ F₂
    rw [assocLHSHomY_apply, assocRHSHomY_apply] at h₂App
    exact h₂App
  have h₁App := DFunLike.congr_fun h₁ F₁
  rw [assocLHSHom_apply, assocRHSHom_apply] at h₁App
  exact h₁App

/-! ### `Semigroup` and `Monoid` instances

With associativity proved, register the typeclass instances. The
underlying `Mul` is the existing `instMul` from `GrossmanLarson.lean`
(so no `Semigroup.mul`-vs-`instMul` diamond). `One` is forwarded from
`ConnesKreimer` via `instOne` (also in `GrossmanLarson.lean`). -/

/- Low priority: `GrossmanLarson` is a semireducible alias of `ConnesKreimer`,
so these instances can capture `ConnesKreimer`-goals carrying metavariables
(hijacking the meta via alias unfolding). Low priority keeps CK-native
instances winning first. -/
noncomputable instance (priority := 50) instSemigroup {R : Type*} [CommSemiring R] :
    Semigroup (GrossmanLarson R α) where
  mul := (· * ·)
  mul_assoc := mul_assoc

noncomputable instance (priority := 50) instMonoid {R : Type*} [CommSemiring R] :
    Monoid (GrossmanLarson R α) where
  one := 1
  one_mul := one_mul
  mul_one := mul_one

end GrossmanLarson

end RootedTree
