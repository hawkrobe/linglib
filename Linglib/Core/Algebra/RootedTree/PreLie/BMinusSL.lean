/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.PreLie.OudomGuinCircTotal
import Linglib.Core.Algebra.RootedTree.PreLie.Basic
import Linglib.Core.Algebra.RootedTree.PreLie.OudomGuinBridge
import Linglib.Core.Algebra.RootedTree.BMinus
import Linglib.Core.Combinatorics.RootedTree.Nonplanar
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# The B⁻ operator on the symmetric algebra of the insertion algebra

For each color `a : α`, this file constructs the linear operator `B⁻_a` on
`SL = SymmetricAlgebra ℤ (InsertionAlgebra α)` from [oudom-guin-2008]: on a
generator `ι (ofTree t)` it returns the product
`∏ c ∈ rootChildren t, ι (ofTree c)` if `rootValue t = a` and `0` otherwise,
and it vanishes on scalars and on products of two or more generators. It is
the SL-side analog of `bMinusLin` on the Connes-Kreimer side (`BMinus.lean`).

The operator is built on the tensor algebra degree by degree and descended to
`SL` through `SymmetricAlgebra.algHom`.

## Main definitions

* `RootedTree.SymAlg.bMinusLin_SL`: the operator `B⁻_a : SL →ₗ[ℤ] SL`.

## Main results

* `bMinusLin_SL_ιTree`: the defining values on embedded trees.
* `iotaTree_node_via_circ`: every tree is the circle product of its singleton
  root with its children-forest, the root-grafting identity displayed in §3.1
  of [oudom-guin-2008].
* `bMinusLin_SL_oudomGuinStar`: the cocycle identity
  `B⁻_a (A ★ B) = ε(A) • B⁻_a B + B⁻_a A ★ B` from the proof of Prop 3.2 of
  [oudom-guin-2008].
* `bMinusLin_ckIso`: transport of `B⁻_a` along `ckIsoSymmetricAlgebra`.

`[UPSTREAM]` candidate.

## References

* [oudom-guin-2008]
-/

namespace RootedTree

namespace SymAlg

open TensorProduct
open scoped DirectSum
open PreLie.OudomGuinCirc

/-! ### Per-tree basis assignment -/

variable {α : Type*}

/-- `LL` (not `L`) avoids clashing with the named argument `(LL := ...)` in
    `algHomL`. -/
local notation "LL" => InsertionAlgebra α
local notation "SL" => SymmetricAlgebra ℤ LL

/-- Embedding of a single tree into `SL`: `SymmetricAlgebra.ι` applied to
    `InsertionAlgebra.ofTree`. -/
noncomputable def ιTree (t : Nonplanar α) : SL :=
  SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree t)

/-- The value of `B⁻_a` on a tree `t`: the SL-product of `ι (ofTree c)` over
    the root's children if `rootValue t = a`, else `0`. -/
noncomputable def psiA_basis (a : α) (t : Nonplanar α) : SL :=
  letI : Decidable (Nonplanar.rootValue t = a) := Classical.dec _
  if Nonplanar.rootValue t = a then
    ((Nonplanar.rootChildren t).map (fun c => ιTree c)).prod
  else 0

/-! ### Linear extension to the insertion algebra -/

/-- The `psiA` operator on `L`: linear extension of `psiA_basis` via
    `Finsupp.lift`. -/
noncomputable def psiA_L (a : α) : LL →ₗ[ℤ] SL :=
  Finsupp.lift SL ℤ (Nonplanar α) (psiA_basis a)

@[simp] theorem psiA_L_ofTree (a : α) (t : Nonplanar α) :
    psiA_L a (InsertionAlgebra.ofTree t) = psiA_basis a t := by
  show Finsupp.lift SL ℤ (Nonplanar α) _ (Finsupp.single t 1) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp

/-! ### Per-degree multilinear maps

`psiA_multi a n` is the `Fin n → LL` multilinear map that vanishes on
`n ≠ 1` and applies `psiA_L a` to the single argument when `n = 1`. -/

/-- The `n = 1` multilinear case: apply `psiA_L` to the single argument. -/
private noncomputable def psiA_multi_one (a : α) :
    MultilinearMap ℤ (fun _ : Fin 1 ↦ LL) SL :=
  MultilinearMap.ofSubsingleton ℤ LL SL 0 (psiA_L a)

@[simp] theorem psiA_multi_one_apply (a : α) (f : Fin 1 → LL) :
    psiA_multi_one a f = psiA_L a (f 0) := rfl

/-- Per-degree multilinear map. Vanishes outside `n = 1`. -/
noncomputable def psiA_multi (a : α) :
    ∀ n : ℕ, MultilinearMap ℤ (fun _ : Fin n ↦ LL) SL
  | 0 => 0
  | 1 => psiA_multi_one a
  | _ + 2 => 0

@[simp] theorem psiA_multi_zero (a : α) :
    psiA_multi a 0 = 0 := rfl

@[simp] theorem psiA_multi_one_eq (a : α) :
    psiA_multi a 1 = psiA_multi_one a := rfl

@[simp] theorem psiA_multi_succ_succ (a : α) (n : ℕ) :
    psiA_multi a (n + 2) = 0 := rfl

/-! ### Lifts to tensor powers -/

/-- Per-degree lift of `psiA_multi a n` to the `n`-th tensor power. -/
noncomputable def psiA_pi (a : α) (n : ℕ) : (⨂[ℤ]^n LL) →ₗ[ℤ] SL :=
  PiTensorProduct.lift (psiA_multi a n)

@[simp] theorem psiA_pi_tprod (a : α) (n : ℕ) (g : Fin n → LL) :
    psiA_pi a n (PiTensorProduct.tprod ℤ g) = psiA_multi a n g := by
  rw [psiA_pi, PiTensorProduct.lift.tprod]

/-! ### Assembly across degrees -/

/-- The maps `psiA_pi a n` assembled into a linear map from the direct sum
    of all tensor powers. -/
noncomputable def psiA_graded (a : α) :
    (⨁ n : ℕ, ⨂[ℤ]^n LL) →ₗ[ℤ] SL :=
  DirectSum.toModule ℤ ℕ SL (fun n => psiA_pi a n)

@[simp] theorem psiA_graded_of (a : α) (n : ℕ) (x : ⨂[ℤ]^n LL) :
    psiA_graded a (DirectSum.of (fun n : ℕ => ⨂[ℤ]^n LL) n x) =
      psiA_pi a n x :=
  DirectSum.toModule_lof (R := ℤ) (ι := ℕ) (M := fun n => ⨂[ℤ]^n LL)
    (N := SL) (φ := fun n => psiA_pi a n) n x

/-! ### The tensor-algebra-level operator -/

/-- The TA-side `psiA` operator, assembled from per-degree `psiA_pi` via
    `TensorAlgebra.equivDirectSum`. -/
noncomputable def psiA_tensor (a : α) : TensorAlgebra ℤ LL →ₗ[ℤ] SL :=
  (psiA_graded a).comp
    (TensorAlgebra.equivDirectSum (R := ℤ) (M := InsertionAlgebra α)).toLinearMap

@[simp] theorem psiA_tensor_tprod (a : α) (n : ℕ) (f : Fin n → LL) :
    psiA_tensor a (TensorAlgebra.tprod ℤ LL n f) = psiA_multi a n f := by
  unfold psiA_tensor
  -- After unfold: (psiA_graded a ∘ₗ equivDirectSum.toLinearMap) (TA.tprod n f).
  rw [LinearMap.comp_apply]
  -- equivDirectSum.toLinearMap = toDirectSum by definition; reduce via change.
  change (psiA_graded a) (TensorAlgebra.toDirectSum (TensorAlgebra.tprod ℤ LL n f)) = _
  -- toDirectSum on tprod gives DirectSum.of n (PiTensorProduct.tprod ...).
  rw [TensorAlgebra.toDirectSum_tensorPower_tprod]
  -- psiA_graded_of reduces toModule applied to of.
  rw [psiA_graded_of]
  -- psiA_pi on tprod = psiA_multi.
  rw [psiA_pi_tprod]

/-! ### Definitional bridges -/

open PreLie.OudomGuinCircConstruct in
/-- `algHomL` is `SymmetricAlgebra.algHom` as a linear map (definitional). -/
@[simp] private theorem algHomL_apply (z : TensorAlgebra ℤ LL) :
    algHomL (R := ℤ) (L := LL) z = SymmetricAlgebra.algHom ℤ LL z := rfl

/-- `SymmetricAlgebra.algHom` sends generators to generators (definitional). -/
@[simp] private theorem algHom_ι (x : LL) :
    SymmetricAlgebra.algHom ℤ LL (TensorAlgebra.ι ℤ x) =
      SymmetricAlgebra.ι ℤ LL x := rfl

open PreLie.OudomGuinCircConstruct in
/-- `algHomL` sends generators to generators (definitional). -/
private theorem algHomL_ι (x : LL) :
    algHomL (R := ℤ) (L := LL) (TensorAlgebra.ι ℤ x) =
      SymmetricAlgebra.ι ℤ LL x := rfl

/-- The empty tensor product is `1`. -/
private theorem tprod_zero (f : Fin 0 → LL) :
    TensorAlgebra.tprod ℤ LL 0 f = (1 : TensorAlgebra ℤ LL) := by
  rw [TensorAlgebra.tprod_apply]
  simp [List.ofFn_zero]

/-! ### Kernel vanishing

`psiA_tensor a` vanishes on `ker algHomL`: it is `0` on every tprod of
degree ≥ 2, and any wrapped `r * (ι X * ι Y) * d` element has degree ≥ 2,
so both swap-orderings map to `0`. -/

open PreLie.OudomGuinCircConstruct in
/-- A product `tprod m r' * (ι X * ι Y) * tprod n d'` is a single tprod of
    grade `m + 2 + n`. -/
private theorem tprod_mul_ι_pair_mul_tprod_inline
    (m n : ℕ) (r' : Fin m → InsertionAlgebra α)
    (d' : Fin n → InsertionAlgebra α) (X Y : InsertionAlgebra α) :
    (TensorAlgebra.tprod ℤ (InsertionAlgebra α) m r') *
      (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y) *
      (TensorAlgebra.tprod ℤ (InsertionAlgebra α) n d') =
    TensorAlgebra.tprod ℤ (InsertionAlgebra α) (m + 2 + n)
      (Fin.append (Fin.append r'
                    (Fin.append (fun _ : Fin 1 => X) (fun _ : Fin 1 => Y)))
                  d') := by
  rw [ι_eq_tprod_one X, ι_eq_tprod_one Y]
  rw [tprod_mul_tprod 1 1, tprod_mul_tprod m (1 + 1), tprod_mul_tprod (m + 2) n]

/-- For `k ≥ 2`, `psiA_multi a k` is the zero map. -/
private theorem psiA_multi_eq_zero_of_ge_two (a : α) {k : ℕ} (hk : 2 ≤ k) :
    psiA_multi a k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  exact psiA_multi_succ_succ a j

/-- `psiA_tensor a` vanishes on any `r * (ι X * ι Y) * d`: the result has
    grade ≥ 2. -/
private theorem psiA_tensor_grade_ge_two_vanish (a : α)
    {m n : ℕ} (r' : Fin m → InsertionAlgebra α)
    (d' : Fin n → InsertionAlgebra α) (X Y : InsertionAlgebra α) :
    psiA_tensor a
        ((TensorAlgebra.tprod ℤ (InsertionAlgebra α) m r') *
          (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y) *
          (TensorAlgebra.tprod ℤ (InsertionAlgebra α) n d')) = 0 := by
  rw [tprod_mul_ι_pair_mul_tprod_inline, psiA_tensor_tprod]
  -- psiA_multi a (m + 2 + n) is the zero map since m + 2 + n ≥ 2.
  rw [psiA_multi_eq_zero_of_ge_two a (by omega : 2 ≤ m + 2 + n)]
  rfl

open PreLie.OudomGuinCircConstruct in
/-- `psiA_tensor a` kills any `r * (ι X * ι Y) * d`: bilinear extension of
    `psiA_tensor_grade_ge_two_vanish` over `r` and `d`. -/
private theorem psiA_tensor_mul_ι_pair_mul (a : α) (X Y : LL)
    (r d : TensorAlgebra ℤ LL) :
    psiA_tensor a (r * (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y) * d) = 0 := by
  have h_d : ∀ m (r' : Fin m → LL),
      (psiA_tensor a).comp (LinearMap.mulLeft ℤ (TensorAlgebra.tprod ℤ LL m r' *
        (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y))) = 0 := fun m r' =>
    TA_linearMap_ext_tprod fun n d' => psiA_tensor_grade_ge_two_vanish a r' d' X Y
  have h_r : (psiA_tensor a).comp ((LinearMap.mulRight ℤ d).comp
      (LinearMap.mulRight ℤ (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y))) = 0 :=
    TA_linearMap_ext_tprod fun m r' => LinearMap.congr_fun (h_d m r') d
  exact LinearMap.congr_fun h_r r

/-- `psiA_tensor a` is invariant under swapping `X` and `Y` inside
    `r * (ι X * ι Y) * d`: both sides vanish. -/
private theorem psiA_tensor_swap_general (a : α) (X Y : LL)
    (r d : TensorAlgebra ℤ LL) :
    psiA_tensor a (r * (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y) * d) =
    psiA_tensor a (r * (TensorAlgebra.ι ℤ Y * TensorAlgebra.ι ℤ X) * d) :=
  (psiA_tensor_mul_ι_pair_mul a X Y r d).trans
    (psiA_tensor_mul_ι_pair_mul a Y X r d).symm

/-- `psiA_tensor a` respects the symmetrizing relation under arbitrary
    wrapping. -/
private theorem psiA_tensor_resp_Rel_strong (a : α) :
    ∀ {z₁ z₂ : TensorAlgebra ℤ LL},
    RingQuot.Rel (TensorAlgebra.SymRel ℤ LL) z₁ z₂ →
    ∀ r d : TensorAlgebra ℤ LL,
      psiA_tensor a (r * z₁ * d) = psiA_tensor a (r * z₂ * d) := by
  intro z₁ z₂ h
  induction h with
  | of h_sym =>
    induction h_sym with
    | mul_comm X Y =>
      intro r d
      exact psiA_tensor_swap_general a X Y r d
  | add_left _ ih =>
    intro r d
    simp only [mul_add, add_mul, map_add, ih r d]
  | @mul_left a' b c _ ih =>
    intro r d
    have hL : r * (a' * c) * d = r * a' * (c * d) := by
      simp only [mul_assoc]
    have hR : r * (b * c) * d = r * b * (c * d) := by
      simp only [mul_assoc]
    rw [hL, hR]
    exact ih r (c * d)
  | @mul_right a' b c _ ih =>
    intro r d
    have hL : r * (a' * b) * d = (r * a') * b * d := by
      simp only [mul_assoc]
    have hR : r * (a' * c) * d = (r * a') * c * d := by
      simp only [mul_assoc]
    rw [hL, hR]
    exact ih (r * a') d

private theorem psiA_tensor_resp_Rel (a : α) {z₁ z₂ : TensorAlgebra ℤ LL}
    (h : RingQuot.Rel (TensorAlgebra.SymRel ℤ LL) z₁ z₂) :
    psiA_tensor a z₁ = psiA_tensor a z₂ := by
  have := psiA_tensor_resp_Rel_strong a h 1 1
  simpa using this

private theorem psiA_tensor_resp_EqvGen (a : α) {z₁ z₂ : TensorAlgebra ℤ LL}
    (h : Relation.EqvGen (RingQuot.Rel (TensorAlgebra.SymRel ℤ LL)) z₁ z₂) :
    psiA_tensor a z₁ = psiA_tensor a z₂ := by
  induction h with
  | rel _ _ h => exact psiA_tensor_resp_Rel a h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

open PreLie.OudomGuinCircConstruct in
/-- `psiA_tensor a` vanishes on the kernel of `algHomL`. -/
private theorem psiA_tensor_vanishes_on_ker (a : α) :
    LinearMap.ker (algHomL (R := ℤ) (L := InsertionAlgebra α)) ≤
      LinearMap.ker (psiA_tensor a) := by
  intro z hz
  -- `hz : z ∈ algHomL.ker`; goal: `z ∈ (psiA_tensor a).ker`. Unfold both
  -- via explicit `show` (simp/rw on `_.ker` form is unreliable).
  rw [LinearMap.mem_ker] at hz
  show psiA_tensor a z = 0
  rw [← (algHomL (R := ℤ) (L := InsertionAlgebra α)).map_zero] at hz
  have h_quot : (Quot.mk (RingQuot.Rel (TensorAlgebra.SymRel ℤ LL)) z :
                  Quot (RingQuot.Rel (TensorAlgebra.SymRel ℤ LL))) =
                Quot.mk _ 0 := by
    have : (SymmetricAlgebra.algHom ℤ LL z).toQuot =
           (SymmetricAlgebra.algHom ℤ LL (0 : TensorAlgebra ℤ LL)).toQuot := by
      exact congrArg (·.toQuot) hz
    simp only [SymmetricAlgebra.algHom, RingQuot.mkAlgHom_def, RingQuot.mkRingHom_def] at this
    exact this
  have h_eqv : Relation.EqvGen (RingQuot.Rel (TensorAlgebra.SymRel ℤ LL)) z 0 :=
    Quot.eqvGen_exact h_quot
  have := psiA_tensor_resp_EqvGen a h_eqv
  rw [this, (psiA_tensor a).map_zero]

/-! ### Descent to the symmetric algebra -/

open PreLie.OudomGuinCircConstruct in
/-- The `B⁻_a` operator on `SL` ([oudom-guin-2008]), descended from
    `psiA_tensor a` through `algHomL` via `Submodule.liftQ`. -/
noncomputable def bMinusLin_SL (a : α) : SL →ₗ[ℤ] SL :=
  (Submodule.liftQ _ (psiA_tensor a) (psiA_tensor_vanishes_on_ker a)).comp
    (LinearMap.quotKerEquivOfSurjective algHomL algHomL_surjective).symm.toLinearMap

/-! ### Basic identities -/

open PreLie.OudomGuinCircConstruct in
/-- `bMinusLin_SL a` factors through `algHomL`:
    `bMinusLin_SL a (algHomL z) = psiA_tensor a z`. -/
theorem bMinusLin_SL_algHomL (a : α) (z : TensorAlgebra ℤ LL) :
    bMinusLin_SL a (algHomL z) = psiA_tensor a z := by
  show (Submodule.liftQ (LinearMap.ker (algHomL (R := ℤ) (L := InsertionAlgebra α)))
        (psiA_tensor a) (psiA_tensor_vanishes_on_ker a))
      ((LinearMap.quotKerEquivOfSurjective algHomL algHomL_surjective).symm
        (algHomL z)) = _
  rw [show (LinearMap.quotKerEquivOfSurjective
        (algHomL (R := ℤ) (L := InsertionAlgebra α)) algHomL_surjective).symm
        (algHomL z) =
      (Submodule.Quotient.mk z : TensorAlgebra ℤ LL ⧸
        LinearMap.ker (algHomL (R := ℤ) (L := InsertionAlgebra α))) from
    (LinearEquiv.symm_apply_eq _).mpr rfl]
  exact Submodule.liftQ_apply _ (psiA_tensor a) _

/-- `bMinusLin_SL a (ι x) = psiA_L a x`. -/
@[simp] theorem bMinusLin_SL_ι (a : α) (x : InsertionAlgebra α) :
    bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL x) = psiA_L a x := by
  rw [← algHomL_ι x, bMinusLin_SL_algHomL,
      PreLie.OudomGuinCircConstruct.ι_eq_tprod_one, psiA_tensor_tprod]
  rfl

/-- `bMinusLin_SL a (ιTree t) = psiA_basis a t`. -/
@[simp] theorem bMinusLin_SL_ιTree (a : α) (t : Nonplanar α) :
    bMinusLin_SL a (ιTree t) = psiA_basis a t := by
  show bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree t)) = _
  rw [bMinusLin_SL_ι, psiA_L_ofTree]

/-- `B⁻_a` vanishes on `1`. -/
@[simp] theorem bMinusLin_SL_one (a : α) :
    bMinusLin_SL a (1 : SL) = 0 := by
  rw [show (1 : SL) = PreLie.OudomGuinCircConstruct.algHomL (1 : TensorAlgebra ℤ LL) by
        rw [algHomL_apply, map_one],
      bMinusLin_SL_algHomL, ← tprod_zero Fin.elim0, psiA_tensor_tprod, psiA_multi_zero]
  rfl

/-! ### Length-one extraction

`bMinusLin_SL` extracts only the length-one component:

- `bMinusLin_SL_ι_mul_ι`: vanishing on products of two generators.
- `bMinusLin_SL_ι_mul_eps`:
  `bMinusLin_SL a (ι Z * Y) = ε(Y) • bMinusLin_SL a (ι Z)`.
- `bMinusLin_SL_ι_star`:
  `bMinusLin_SL a (ι Y ★ B) = psiA_L a (circByT_total Y B)`.
-/

/-- `B⁻_a` vanishes on a product of two generators. -/
private theorem bMinusLin_SL_ι_mul_ι (a : α) (Z W : LL) :
    bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL Z * SymmetricAlgebra.ι ℤ LL W) = 0 := by
  -- ι Z * ι W = algHom (ι_TA Z * ι_TA W). Push to TA side.
  have h_alg : SymmetricAlgebra.ι ℤ LL Z * SymmetricAlgebra.ι ℤ LL W =
      PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL)
        (TensorAlgebra.ι ℤ Z * TensorAlgebra.ι ℤ W) := by
    rw [algHomL_apply, map_mul, algHom_ι, algHom_ι]
  rw [h_alg, bMinusLin_SL_algHomL,
      PreLie.OudomGuinCircConstruct.ι_eq_tprod_one Z,
      PreLie.OudomGuinCircConstruct.ι_eq_tprod_one W,
      PreLie.OudomGuinCircConstruct.tprod_mul_tprod,
      psiA_tensor_tprod, psiA_multi_succ_succ]
  rfl

/-- `algebraMapInv ∘ algHomL` vanishes on positive-grade tprods: the image is
    a product of `n + 1` ι-elements, each killed by `algebraMapInv`. -/
private theorem algebraMapInv_algHom_tprod_succ (n : ℕ) (f : Fin (n+1) → LL) :
    SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)
        ((SymmetricAlgebra.algHom ℤ LL) (TensorAlgebra.tprod ℤ LL (n+1) f)) = 0 := by
  rw [TensorAlgebra.tprod_apply, _root_.map_list_prod, List.map_ofFn,
      _root_.map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, algHom_ι, SymmetricAlgebra.algebraMapInv_ι]
  rw [List.ofFn_const, List.prod_replicate]
  exact zero_pow (Nat.succ_ne_zero n)

/-- Per-tprod helper: the value of `bMinusLin_SL a (ι Z * algHomL (tprod n f))`
    and its match with the RHS. Splits on `n = 0` vs `n ≥ 1`. -/
private theorem bMinusLin_SL_ι_mul_algHom_tprod (a : α) (Z : LL)
    (n : ℕ) (f : Fin n → LL) :
    bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL Z *
                     (SymmetricAlgebra.algHom ℤ LL) (TensorAlgebra.tprod ℤ LL n f)) =
      SymmetricAlgebra.algebraMapInv (M := LL)
        ((SymmetricAlgebra.algHom ℤ LL) (TensorAlgebra.tprod ℤ LL n f)) •
        bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL Z) := by
  -- ι Z = algHom (ι_TA Z); push mul through algHom.
  rw [← algHom_ι Z, ← _root_.map_mul,
      PreLie.OudomGuinCircConstruct.ι_eq_tprod_one Z,
      PreLie.OudomGuinCircConstruct.tprod_mul_tprod,
      ← algHomL_apply, bMinusLin_SL_algHomL, psiA_tensor_tprod]
  cases n with
  | zero =>
    show psiA_multi a 1 (Fin.append (fun _ : Fin 1 => Z) f) = _
    rw [psiA_multi_one_eq, psiA_multi_one_apply,
        show (Fin.append (fun _ : Fin 1 => Z) f) 0 = Z from rfl]
    rw [tprod_zero f, _root_.map_one, _root_.map_one, one_smul]
    -- Convert RHS (algHom (tprod 1 ![Z])) back to (ι Z) and apply bMinusLin_SL_ι.
    simp only [← PreLie.OudomGuinCircConstruct.ι_eq_tprod_one, algHom_ι]
    exact (bMinusLin_SL_ι a Z).symm
  | succ k =>
    -- Both sides vanish: grade ≥ 2 on the left, positive grade on the right.
    have h_multi_zero : psiA_multi a (1 + (k+1)) = 0 :=
      psiA_multi_eq_zero_of_ge_two a (by omega)
    rw [h_multi_zero]
    show (0 : SL) = _
    rw [algebraMapInv_algHom_tprod_succ k f, zero_smul]

/-- `B⁻_a` extracts the length-one part of a left ι-multiplication:
    `bMinusLin_SL a (ι Z * Y) = ε(Y) • bMinusLin_SL a (ι Z)`. -/
private theorem bMinusLin_SL_ι_mul_eps (a : α) (Z : LL) (Y : SL) :
    bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL Z * Y) =
      SymmetricAlgebra.algebraMapInv (M := LL) Y •
        bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL Z) := by
  obtain ⟨z, rfl⟩ := PreLie.OudomGuinCircConstruct.algHomL_surjective Y
  -- Reduce to LinearMap equality F = G on TA.
  suffices h_eq :
      ((bMinusLin_SL a).comp
        ((LinearMap.mulLeft ℤ (SymmetricAlgebra.ι ℤ LL Z)).comp
          (PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL)))) =
      LinearMap.smulRight
        (((SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)).toLinearMap).comp
          (PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL)))
        (bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL Z)) by
    have := LinearMap.congr_fun h_eq z
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.smulRight_apply, AlgHom.toLinearMap_apply] at this
    exact this
  apply PreLie.OudomGuinCircConstruct.TA_linearMap_ext_tprod
  intro n f
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
             LinearMap.smulRight_apply, AlgHom.toLinearMap_apply]
  exact bMinusLin_SL_ι_mul_algHom_tprod a Z n f

/-- Counit-Leibniz rule for `B⁻_a`: since `B⁻_a` extracts the length-one
    component, it is an `ε`-twisted derivation on `*`. -/
private theorem bMinusLin_SL_mul_eps (a : α) (X Y : SL) :
    bMinusLin_SL a (X * Y) =
      SymmetricAlgebra.algebraMapInv (M := LL) X • bMinusLin_SL a Y +
      SymmetricAlgebra.algebraMapInv (M := LL) Y • bMinusLin_SL a X := by
  induction X using SymmetricAlgebra.induction generalizing Y with
  | algebraMap r =>
    -- X = r • 1; B⁻_a((r • 1) * Y) = r • B⁻_a Y.
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul,
        map_smul, map_smul, bMinusLin_SL_one, map_one, smul_zero, smul_zero,
        add_zero, smul_eq_mul, mul_one]
  | ι Z =>
    -- ε(ι Z) = 0, reduces to `bMinusLin_SL_ι_mul_eps`.
    rw [bMinusLin_SL_ι_mul_eps, SymmetricAlgebra.algebraMapInv_ι, zero_smul, zero_add]
  | mul X₁ X₂ ih₁ ih₂ =>
    -- Reassociate, apply ih₁ at Y' = X₂ * Y, then ih₂ at Y' = Y.
    rw [mul_assoc, ih₁ (X₂ * Y), ih₂ Y, ih₁ X₂, map_mul, mul_smul, smul_add,
        smul_comm (SymmetricAlgebra.algebraMapInv (M := LL) X₁)
          (SymmetricAlgebra.algebraMapInv (M := LL) Y),
        smul_comm (SymmetricAlgebra.algebraMapInv (M := LL) X₂)
          (SymmetricAlgebra.algebraMapInv (M := LL) Y),
        smul_add, show (SymmetricAlgebra.algebraMapInv (M := LL) (X₁ * X₂)) =
          SymmetricAlgebra.algebraMapInv (M := LL) X₁ *
            SymmetricAlgebra.algebraMapInv (M := LL) X₂ from map_mul _ _ _,
        mul_smul]
    abel
  | add X₁ X₂ ih₁ ih₂ =>
    -- Linearity in X.
    rw [add_mul, map_add, map_add, map_add, ih₁ Y, ih₂ Y]
    simp only [add_smul, smul_add]
    abel

/-- `oudomGuinCirc (ι T) B = ι (circByT_total T B)` (definitional through
    `circHom`). -/
private theorem oudomGuinCirc_ι_apply (T : LL) (B : SL) :
    oudomGuinCirc (R := ℤ) (SymmetricAlgebra.ι ℤ LL T) B =
      SymmetricAlgebra.ι ℤ LL
        (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) T B) := by
  rw [oudomGuinCirc_eq_ofConv, circHom_ι]
  rfl

/-- `bMinusLin_SL a (ι Y ★ B) = psiA_L a (circByT_total Y B)`. Unfolds `★`
    (Def 2.9 of [oudom-guin-2008]) and collapses the Sweedler sum via the
    counit-comul triangle. -/
private theorem bMinusLin_SL_ι_star (a : α) (Y : LL) (B : SL) :
    bMinusLin_SL a (oudomGuinStar (SymmetricAlgebra.ι ℤ LL Y) B) =
      psiA_L a
        ((PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) (L := LL) Y) B) := by
  -- LinearMap equality on SL ⊗ SL: both sides at cm B reduce to
  -- `ε(B₂) • psiA_L a (circByT_total Y B₁)` summed over Sweedler.
  have h_lm :
      (bMinusLin_SL a).comp ((LinearMap.mul' ℤ SL).comp
        (TensorProduct.map
          (oudomGuinCirc (R := ℤ) (SymmetricAlgebra.ι ℤ LL Y))
          (LinearMap.id : SL →ₗ[ℤ] SL))) =
      ((psiA_L a).comp
        (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) (L := LL) Y)).comp
        ((LinearMap.mul' ℤ SL).comp
          (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL)
            ((Algebra.linearMap ℤ SL).comp
              (SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)).toLinearMap))) := by
    apply TensorProduct.ext'
    intro b₁ b₂
    -- LHS reduces to ε(b₂) • psiA_L a (circByT_total Y b₁).
    have h_LHS :
        ((bMinusLin_SL a).comp ((LinearMap.mul' ℤ SL).comp
          (TensorProduct.map
            (oudomGuinCirc (R := ℤ) (SymmetricAlgebra.ι ℤ LL Y))
            (LinearMap.id : SL →ₗ[ℤ] SL)))) (b₁ ⊗ₜ[ℤ] b₂) =
        SymmetricAlgebra.algebraMapInv (M := LL) b₂ •
          psiA_L a (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) Y b₁) := by
      show (bMinusLin_SL a) ((LinearMap.mul' ℤ SL)
            (((oudomGuinCirc (R := ℤ) (SymmetricAlgebra.ι ℤ LL Y)) b₁) ⊗ₜ[ℤ] b₂)) = _
      rw [LinearMap.mul'_apply, oudomGuinCirc_ι_apply,
          bMinusLin_SL_ι_mul_eps, bMinusLin_SL_ι]
    -- RHS reduces to the same value.
    have h_RHS :
        (((psiA_L a).comp
          (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) (L := LL) Y)).comp
          ((LinearMap.mul' ℤ SL).comp
            (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL)
              ((Algebra.linearMap ℤ SL).comp
                (SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)).toLinearMap))))
            (b₁ ⊗ₜ[ℤ] b₂) =
        SymmetricAlgebra.algebraMapInv (M := LL) b₂ •
          psiA_L a (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) Y b₁) := by
      show (psiA_L a) ((PreLie.OudomGuinCircConstruct.circByT_total Y)
              ((LinearMap.mul' ℤ SL)
                (b₁ ⊗ₜ[ℤ] (algebraMap ℤ SL (SymmetricAlgebra.algebraMapInv (M := LL) b₂))))) = _
      rw [LinearMap.mul'_apply]
      conv_lhs => rw [show b₁ * algebraMap ℤ SL (SymmetricAlgebra.algebraMapInv (M := LL) b₂) =
                          (SymmetricAlgebra.algebraMapInv (M := LL) b₂) • b₁
                      from by rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]; rfl]
      rw [map_smul, map_smul]
    exact h_LHS.trans h_RHS.symm
  -- Use AlgHom-form comul (`Bialgebra.comulAlgHom`) so the `SL` notation doesn't
  -- block typeclass synthesis on the LinearMap-form `Coalgebra.comul`.
  set cmB : SL ⊗[ℤ] SL :=
    (Bialgebra.comulAlgHom ℤ (SymmetricAlgebra ℤ LL)).toLinearMap B with hcmB
  have h_at_B := LinearMap.congr_fun h_lm cmB
  simp only [LinearMap.comp_apply] at h_at_B
  -- LHS of goal ≡ h_at_B's LHS (definitionally via oudomGuinStar_def + comulAlgHom.toLinearMap = comul).
  -- Reduce RHS of h_at_B to RHS of goal via counit triangle.
  refine h_at_B.trans ?_
  -- Reduce mul' (map id (algebraMap ∘ counit) cmB) = B via the counit triangle.
  -- The `letI`s force the `CoalgebraStruct` on the unfolded type; without them
  -- instance synthesis fails on the `Coalgebra.comul` occurrences below.
  letI inst_B : Bialgebra ℤ (SymmetricAlgebra ℤ LL) := SymmetricAlgebra.instBialgebra ℤ LL
  letI inst_Co : Coalgebra ℤ (SymmetricAlgebra ℤ LL) := inst_B.toCoalgebra
  letI inst_C : CoalgebraStruct ℤ (SymmetricAlgebra ℤ LL) := inst_Co.toCoalgebraStruct
  have h_inner :
      (LinearMap.mul' ℤ SL)
          ((TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL)
              ((Algebra.linearMap ℤ SL).comp
                (SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)).toLinearMap))
            cmB) = B := by
    rw [show TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL)
            ((Algebra.linearMap ℤ SL).comp
              (SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)).toLinearMap) =
        (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL)
            (Algebra.linearMap ℤ SL)).comp
          (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL)
            (SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)).toLinearMap) from by
        rw [← TensorProduct.map_comp, LinearMap.comp_id]]
    rw [LinearMap.comp_apply, hcmB]
    -- cmB = (comulAlgHom).toLinearMap B = comul B definitionally.
    show (LinearMap.mul' ℤ SL)
          ((TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL)
              (Algebra.linearMap ℤ SL))
            ((TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL)
                (SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)).toLinearMap)
              (Coalgebra.comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B))) = B
    rw [show (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL)
              (SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)).toLinearMap)
              (Coalgebra.comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B) =
            B ⊗ₜ[ℤ] (1 : ℤ) from
          Coalgebra.lTensor_counit_comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B]
    rw [TensorProduct.map_tmul]
    show (LinearMap.mul' ℤ SL) (B ⊗ₜ[ℤ] (algebraMap ℤ SL 1)) = B
    rw [map_one]
    -- Now: mul' (B ⊗ₜ 1) = B
    show B * 1 = B
    exact mul_one B
  show (psiA_L a) ((PreLie.OudomGuinCircConstruct.circByT_total Y)
        ((LinearMap.mul' ℤ SL)
          ((TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL)
              ((Algebra.linearMap ℤ SL).comp
                (SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)).toLinearMap))
            cmB))) = _
  rw [h_inner]

/-! ### Transport along `ckIsoSymmetricAlgebra`

The transport identity `bMinusLin a (ckIso X) = ckIso (bMinusLin_SL a X)`,
via an ε-twisted Leibniz rule for the disjoint-union product on the
Connes-Kreimer side. -/

section CKTransport

open ConnesKreimer (counit counit_of' of'_add)
open GrossmanLarson (of' bMinusBasis bMinusBasis_zero bMinusBasis_singleton_node
  bMinusBasis_eq_zero_of_not_singleton_a bMinusLin bMinusLin_of')

/-! ### Counit-Leibniz rule on forests

`bMinusBasis a (F + G)` splits according to which of `F`, `G` is empty:
it equals `bMinusBasis a G` when `F` is empty, `bMinusBasis a F` when `G`
is empty, and `0` when both are nonempty. -/

private theorem bMinusBasis_add (a : α)
    (F G : Forest (Nonplanar α)) :
    bMinusBasis (R := ℤ) a (F + G) =
      (if F.card = 0 then bMinusBasis a G else 0) +
      (if G.card = 0 then bMinusBasis a F else 0) := by
  by_cases hF : F.card = 0
  · -- F = ∅; F + G = G.
    rw [Multiset.card_eq_zero] at hF
    subst hF
    simp only [zero_add, Multiset.card_zero, if_true]
    by_cases hG : G.card = 0
    · rw [Multiset.card_eq_zero] at hG
      subst hG
      simp only [Multiset.card_zero, if_true, bMinusBasis_zero, add_zero]
    · rw [if_neg hG, add_zero]
  · by_cases hG : G.card = 0
    · -- G = ∅; F + G = F.
      rw [Multiset.card_eq_zero] at hG
      subst hG
      simp only [add_zero, Multiset.card_zero, if_true]
      rw [if_neg hF, zero_add]
    · -- Both nonempty; F + G has card ≥ 2, bMinusBasis vanishes.
      rw [if_neg hF, if_neg hG, add_zero]
      apply bMinusBasis_eq_zero_of_not_singleton_a
      rintro ⟨G', hFG⟩
      have h_card : (F + G).card = 1 := by rw [hFG]; rfl
      rw [Multiset.card_add] at h_card
      have h1 : F.card ≥ 1 := Nat.one_le_iff_ne_zero.mpr hF
      have h2 : G.card ≥ 1 := Nat.one_le_iff_ne_zero.mpr hG
      omega

/-! ### Counit-Leibniz rule on forest products -/

/-- The ε-twisted Leibniz rule on basis elements: under
    `of' F * of' G = of' (F + G)`, `bMinusLin` splits according to which side
    is empty. Uses `ConnesKreimer.of'` (not `GrossmanLarson.of'`) and the
    disjoint-union product (not `productForest`). -/
private theorem bMinusLin_of'_mul_of' (a : α) (F G : Forest (Nonplanar α)) :
    bMinusLin (R := ℤ) a
        ((ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α)) *
          ConnesKreimer.of' G) =
      counit (ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α)) •
        bMinusLin (R := ℤ) a (ConnesKreimer.of' G : ConnesKreimer ℤ (Nonplanar α)) +
      counit (ConnesKreimer.of' G : ConnesKreimer ℤ (Nonplanar α)) •
        bMinusLin (R := ℤ) a (ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α)) := by
  rw [← of'_add]
  -- `bMinusLin_of'` uses `GrossmanLarson.of'`. Bridge via def-equal `show`.
  show bMinusLin a (GrossmanLarson.of' (F + G)) =
    counit (GrossmanLarson.of' F : ConnesKreimer ℤ (Nonplanar α)) •
      bMinusLin a (GrossmanLarson.of' G) +
    counit (GrossmanLarson.of' G : ConnesKreimer ℤ (Nonplanar α)) •
      bMinusLin a (GrossmanLarson.of' F)
  rw [bMinusLin_of', bMinusLin_of', bMinusLin_of']
  -- Now: bMinusBasis a (F+G) = counit(GL.of' F) • bMinusBasis a G + counit(GL.of' G) • bMinusBasis a F
  -- counit on GL.of' = counit on CK.of' (def-equal, both `counit` from CK namespace).
  show bMinusBasis a (F + G) =
    counit (ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α)) • bMinusBasis a G +
    counit (ConnesKreimer.of' G : ConnesKreimer ℤ (Nonplanar α)) • bMinusBasis a F
  rw [counit_of', counit_of', bMinusBasis_add]
  by_cases hF : F.card = 0 <;> by_cases hG : G.card = 0 <;> simp [hF, hG]

/-! ### The transport identity

`bMinusLin a (ckIso X) = ckIso (bMinusLin_SL a X)` for all `X : SL`. The
proof inducts on `X` via `SymmetricAlgebra.induction`. Two private helpers
are added in service of the `mul` case: a CK-side counit-Leibniz rule
(`bMinusLin_mul_eps`, bilinear extension of `bMinusLin_of'_mul_of'`) and a
bridge identifying `counit ∘ ckIso` with `algebraMapInv` (`counit_ckIso`).

Relocation candidates: `bMinusLin_mul_eps` belongs in `BMinus.lean` (CK
substrate); deferred to avoid concurrent edits. -/

/-- CK-side counit-Leibniz for `bMinusLin`: bilinear extension of
    `bMinusLin_of'_mul_of'` from `of' F`-basis elements to arbitrary CK
    elements. Disjoint-union product (NOT GL); proof: realize both sides
    as `R`-bilinear maps that agree on basis pairs. Relocation candidate
    to `BMinus.lean`. -/
private theorem bMinusLin_mul_eps [DecidableEq (Nonplanar α)] (a : α)
    (X Y : ConnesKreimer ℤ (Nonplanar α)) :
    bMinusLin (R := ℤ) a (X * Y) =
      counit X • bMinusLin (R := ℤ) a Y +
      counit Y • bMinusLin (R := ℤ) a X := by
  -- Build the difference (LHS - RHS) as a bilinear map and show it vanishes on
  -- basis pairs (of' F, of' G), hence on all (X, Y) by `mk₂`-extension.
  -- Set L (X, Y) := bMinusLin a (X * Y) - counit X • bMinusLin a Y -
  --                                       counit Y • bMinusLin a X.
  -- L extends as a ℤ-bilinear map and vanishes on basis pairs by
  -- `bMinusLin_of'_mul_of'`. Conclude `L X Y = 0`.
  -- For concreteness we prove the difference is zero via Finsupp double
  -- induction; each step uses only ℤ-linearity laws.
  -- Reduce to a LinearMap-on-(X⊗Y) equality, then apply `mk₂` ext.
  let CK : Type _ := ConnesKreimer ℤ (Nonplanar α)
  -- Build the two sides as ℤ-bilinear maps `CK →ₗ[ℤ] CK →ₗ[ℤ] CK`.
  -- LHS(X,Y) = bMinusLin a (X*Y); RHS(X,Y) = counit X • bMinusLin a Y +
  --                                          counit Y • bMinusLin a X.
  suffices h : ∀ F : Forest (Nonplanar α),
      ∀ Z : ConnesKreimer ℤ (Nonplanar α),
        bMinusLin (R := ℤ) a (ConnesKreimer.of' F * Z) =
          counit (ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α)) •
            bMinusLin (R := ℤ) a Z +
          counit Z • bMinusLin (R := ℤ) a (ConnesKreimer.of' F) by
    -- Bilinear extension: extend over X via Finsupp.induction_linear on X.
    induction X using Finsupp.induction_linear with
    | zero =>
      -- LHS: bMinusLin a (0 * Y) = bMinusLin a 0 = 0.
      -- RHS: counit 0 • _ + counit Y • bMinusLin a 0 = 0 • _ + counit Y • 0 = 0.
      show bMinusLin (R := ℤ) a
              ((0 : ConnesKreimer ℤ (Nonplanar α)) * Y) = _
      rw [zero_mul, LinearMap.map_zero]
      show (0 : ConnesKreimer ℤ (Nonplanar α)) =
           counit (0 : ConnesKreimer ℤ (Nonplanar α)) • bMinusLin a Y +
           counit Y • bMinusLin a (0 : ConnesKreimer ℤ (Nonplanar α))
      rw [map_zero, zero_smul, zero_add, LinearMap.map_zero, smul_zero]
    | add X₁ X₂ ih₁ ih₂ =>
      -- After Finsupp.induction_linear, X₁ X₂ have type Forest →₀ ℤ; coerce
      -- to CK by an opaque alias bound to the same term.
      let X₁' : ConnesKreimer ℤ (Nonplanar α) := X₁
      let X₂' : ConnesKreimer ℤ (Nonplanar α) := X₂
      show bMinusLin (R := ℤ) a ((X₁' + X₂') * Y) =
           counit (X₁' + X₂') • bMinusLin a Y +
           counit Y • bMinusLin a (X₁' + X₂')
      rw [add_mul, LinearMap.map_add, _root_.map_add, add_smul,
          LinearMap.map_add, smul_add]
      show bMinusLin (R := ℤ) a (X₁' * Y) + bMinusLin (R := ℤ) a (X₂' * Y) =
        counit X₁' • bMinusLin a Y + counit X₂' • bMinusLin a Y +
        (counit Y • bMinusLin a X₁' + counit Y • bMinusLin a X₂')
      rw [ih₁, ih₂]
      abel
    | single F r =>
      -- Reduce single F r = r • of' F, then apply h on of' F.
      have hX : (Finsupp.single F r : ConnesKreimer ℤ (Nonplanar α)) =
                r • ConnesKreimer.of' F := by
        show Finsupp.single F r = r • Finsupp.single F (1 : ℤ)
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hX]
      show bMinusLin (R := ℤ) a ((r • ConnesKreimer.of' F) * Y) =
           counit ((r • ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α))) •
             bMinusLin a Y +
           counit Y • bMinusLin a (r • ConnesKreimer.of' F)
      rw [show ((r • ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α)) * Y) =
              r • (ConnesKreimer.of' F * Y) from smul_mul_assoc r _ Y,
          LinearMap.map_smul, h F Y, _root_.map_smul,
          LinearMap.map_smul, smul_smul, mul_comm (counit Y) r, ← smul_smul,
          smul_add]
      congr 1
      rw [smul_smul, smul_eq_mul]
  -- Now prove h: for fixed of' F, the identity holds for all Z.
  intro F Z
  induction Z using Finsupp.induction_linear with
  | zero =>
    show bMinusLin (R := ℤ) a
          (ConnesKreimer.of' F * (0 : ConnesKreimer ℤ (Nonplanar α))) = _
    rw [mul_zero, LinearMap.map_zero]
    show (0 : ConnesKreimer ℤ (Nonplanar α)) =
         counit (ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α)) •
           bMinusLin a (0 : ConnesKreimer ℤ (Nonplanar α)) +
         counit (0 : ConnesKreimer ℤ (Nonplanar α)) •
           bMinusLin a (ConnesKreimer.of' F)
    rw [LinearMap.map_zero, smul_zero, map_zero, zero_smul, zero_add]
  | add Z₁ Z₂ ih₁ ih₂ =>
    let Z₁' : ConnesKreimer ℤ (Nonplanar α) := Z₁
    let Z₂' : ConnesKreimer ℤ (Nonplanar α) := Z₂
    show bMinusLin (R := ℤ) a (ConnesKreimer.of' F * (Z₁' + Z₂')) =
      counit (ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α)) •
        bMinusLin a (Z₁' + Z₂') +
      counit (Z₁' + Z₂') • bMinusLin a (ConnesKreimer.of' F)
    rw [mul_add, LinearMap.map_add]
    show bMinusLin (R := ℤ) a (ConnesKreimer.of' F * Z₁') +
         bMinusLin (R := ℤ) a (ConnesKreimer.of' F * Z₂') =
         counit (ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α)) •
           bMinusLin a (Z₁' + Z₂') +
         counit (Z₁' + Z₂') • bMinusLin a (ConnesKreimer.of' F)
    rw [ih₁, ih₂, LinearMap.map_add, smul_add, _root_.map_add, add_smul]
    abel
  | single G s =>
    have hY : (Finsupp.single G s : ConnesKreimer ℤ (Nonplanar α)) =
              s • ConnesKreimer.of' G := by
      show Finsupp.single G s = s • Finsupp.single G (1 : ℤ)
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hY]
    show bMinusLin (R := ℤ) a
            (ConnesKreimer.of' F * s • ConnesKreimer.of' G) =
         counit (ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α)) •
           bMinusLin a (s • ConnesKreimer.of' G) +
         counit (s • ConnesKreimer.of' G :
           ConnesKreimer ℤ (Nonplanar α)) •
           bMinusLin a (ConnesKreimer.of' F)
    -- LHS: mul_smul_comm + LinearMap.map_smul + basis identity + smul_add.
    rw [mul_smul_comm s (ConnesKreimer.of' F) (ConnesKreimer.of' G),
        LinearMap.map_smul, bMinusLin_of'_mul_of', smul_add]
    -- RHS: LinearMap.map_smul on first, _root_.map_smul on second.
    rw [LinearMap.map_smul, _root_.map_smul]
    -- Goal: s • (counit (of' F) • bMinusLin a (of' G) + counit (of' G) • bMinusLin a (of' F))
    --     decomposed via smul_add becomes
    --   s • counit (of' F) • bMinusLin a (of' G) +
    --   s • counit (of' G) • bMinusLin a (of' F)
    -- = counit (of' F) • s • bMinusLin a (of' G) +
    --   (s • counit (of' G)) • bMinusLin a (of' F)
    congr 1
    · rw [smul_comm s (counit (ConnesKreimer.of' F : ConnesKreimer ℤ (Nonplanar α)))]
    · rw [smul_smul, smul_eq_mul]

/-- Bridge: the CK counit pulled back along `ckIsoSymmetricAlgebra` equals
    the SL counit `SymmetricAlgebra.algebraMapInv`. Both sides are AlgHoms
    `SL →ₐ[ℤ] ℤ`; agree on `ι (single t 1)`. -/
private theorem counit_ckIso [DecidableEq (Nonplanar α)] (X : SL) :
    counit (ckIsoSymmetricAlgebra X) =
    SymmetricAlgebra.algebraMapInv (M := InsertionAlgebra α) X := by
  -- Show the AlgHoms are equal pointwise.
  suffices h : (counit (R := ℤ) (T := Nonplanar α)).comp
      ckIsoSymmetricAlgebra.toAlgHom =
      SymmetricAlgebra.algebraMapInv (M := InsertionAlgebra α) (R := ℤ) by
    exact congrArg (fun (φ : SL →ₐ[ℤ] ℤ) => φ X) h
  -- Both AlgHoms on SL; the structure of SL = SymAlg ℤ LL gives us a
  -- universal property via `SymmetricAlgebra.lift`. Use `algHom_ext`.
  apply SymmetricAlgebra.algHom_ext
  ext x
  -- Goal: (counit ∘ₗ ckIso ∘ₗ ι) x = (algebraMapInv ∘ₗ ι) x.
  -- Both are linear maps `LL →ₗ[ℤ] ℤ`; reduce via Finsupp.induction_linear on x.
  refine Finsupp.induction_linear x ?_ ?_ ?_
  · -- x = 0: both sides are 0 by linearity.
    show counit (ckIsoSymmetricAlgebra (SymmetricAlgebra.ι ℤ LL 0)) =
         SymmetricAlgebra.algebraMapInv
           (M := InsertionAlgebra α) (SymmetricAlgebra.ι ℤ LL 0)
    have h₀ : (SymmetricAlgebra.ι ℤ LL : LL →ₗ[ℤ] SL) 0 = (0 : SL) :=
      LinearMap.map_zero _
    rw [h₀, _root_.map_zero, _root_.map_zero, _root_.map_zero]
  · intro x₁ x₂ ih₁ ih₂
    -- ih₁, ih₂ are stated via `LinearMap.ext`'s composition. Unfold first.
    have ih₁' : counit (ckIsoSymmetricAlgebra (SymmetricAlgebra.ι ℤ LL x₁)) =
                SymmetricAlgebra.algebraMapInv
                  (M := InsertionAlgebra α) (SymmetricAlgebra.ι ℤ LL x₁) := ih₁
    have ih₂' : counit (ckIsoSymmetricAlgebra (SymmetricAlgebra.ι ℤ LL x₂)) =
                SymmetricAlgebra.algebraMapInv
                  (M := InsertionAlgebra α) (SymmetricAlgebra.ι ℤ LL x₂) := ih₂
    show counit (ckIsoSymmetricAlgebra (SymmetricAlgebra.ι ℤ LL (x₁ + x₂))) =
         SymmetricAlgebra.algebraMapInv
           (M := InsertionAlgebra α) (SymmetricAlgebra.ι ℤ LL (x₁ + x₂))
    have h_add : (SymmetricAlgebra.ι ℤ LL : LL →ₗ[ℤ] SL) (x₁ + x₂) =
                  SymmetricAlgebra.ι ℤ LL x₁ + SymmetricAlgebra.ι ℤ LL x₂ :=
      LinearMap.map_add _ _ _
    rw [h_add, _root_.map_add, _root_.map_add, _root_.map_add, ih₁', ih₂']
  · intro t r
    have h_single : (Finsupp.single t r : InsertionAlgebra α) =
        r • (Finsupp.single t 1 : InsertionAlgebra α) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    show counit (ckIsoSymmetricAlgebra
            (SymmetricAlgebra.ι ℤ LL (Finsupp.single t r))) =
         SymmetricAlgebra.algebraMapInv
           (M := InsertionAlgebra α)
           (SymmetricAlgebra.ι ℤ LL (Finsupp.single t r))
    rw [h_single]
    -- Push smul: ι (r • single t 1) = r • ι (single t 1).
    rw [show (SymmetricAlgebra.ι ℤ LL (r • Finsupp.single t (1 : ℤ)) : SL) =
            r • SymmetricAlgebra.ι ℤ LL (Finsupp.single t 1) from
          LinearMap.map_smul (SymmetricAlgebra.ι ℤ LL) r _]
    rw [_root_.map_smul, _root_.map_smul,
        ckIsoSymmetricAlgebra_ι_single, counit_of', Multiset.card_singleton,
        if_neg (by decide : ¬(1 : ℕ) = 0), smul_zero, _root_.map_smul,
        SymmetricAlgebra.algebraMapInv_ι, smul_zero]

/-- Product of `ιTree c` over a multiset `M` in SL, transported through
    `ckIso`, equals `of' M` in CK. Used in the `ι x` case of
    `bMinusLin_ckIso` to identify `ckIso (psiA_basis a t)` with
    `bMinusBasis a {t}` when `rootValue t = a`. -/
private theorem ckIso_prod_ιTree [DecidableEq (Nonplanar α)]
    (M : Multiset (Nonplanar α)) :
    ckIsoSymmetricAlgebra ((M.map (fun c => ιTree c)).prod) =
    (ConnesKreimer.of' M : ConnesKreimer ℤ (Nonplanar α)) := by
  induction M using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, map_one]
    exact (ConnesKreimer.of'_zero (R := ℤ) (T := Nonplanar α)).symm
  | cons c M ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, map_mul]
    rw [ih]
    -- Now: ckIso (ιTree c) * of' M = of' (c ::ₘ M)
    show ckIsoSymmetricAlgebra
            (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c)) *
         (ConnesKreimer.of' M : ConnesKreimer ℤ (Nonplanar α)) =
         ConnesKreimer.of' (c ::ₘ M)
    show ckIsoSymmetricAlgebra
            (SymmetricAlgebra.ι ℤ LL (Finsupp.single c (1 : ℤ))) *
         (ConnesKreimer.of' M : ConnesKreimer ℤ (Nonplanar α)) =
         ConnesKreimer.of' (c ::ₘ M)
    rw [ckIsoSymmetricAlgebra_ι_single]
    show (ConnesKreimer.of' ({c} : Multiset (Nonplanar α))
            : ConnesKreimer ℤ (Nonplanar α)) *
         ConnesKreimer.of' M = ConnesKreimer.of' (c ::ₘ M)
    rw [← of'_add]
    show ConnesKreimer.of' (({c} : Multiset (Nonplanar α)) + M) =
         ConnesKreimer.of' (c ::ₘ M)
    rw [Multiset.singleton_add]

/-- Transport of `B⁻_a` along `ckIsoSymmetricAlgebra`:
    `bMinusLin a (ckIso X) = ckIso (bMinusLin_SL a X)`. Induction on `X`
    via `SymmetricAlgebra.induction`: the `algebraMap`/`add` cases are
    linearity, the `ι x` case routes through `ckIsoSymmetricAlgebra_ι_single`
    + `ckIso_prod_ιTree`, and the `mul` case combines `bMinusLin_SL_mul_eps`
    (SL side) with `bMinusLin_mul_eps` + `counit_ckIso` (CK side). -/
theorem bMinusLin_ckIso [DecidableEq (Nonplanar α)] (a : α) (X : SL) :
    bMinusLin (R := ℤ) a (ckIsoSymmetricAlgebra X) =
    ckIsoSymmetricAlgebra (bMinusLin_SL a X) := by
  induction X using SymmetricAlgebra.induction with
  | algebraMap r =>
    -- X = algebraMap r; ckIso commutes with algebraMap, bMinusLin_SL kills algebraMap.
    -- LHS: bMinusLin (ckIso (algebraMap r)) = bMinusLin (algebraMap r) = r • bMinusLin 1 = 0.
    -- RHS: ckIso (bMinusLin_SL (algebraMap r)) = ckIso 0 = 0.
    have h_LHS : bMinusLin (R := ℤ) a
        (ckIsoSymmetricAlgebra (algebraMap ℤ SL r)) = 0 := by
      rw [ckIsoSymmetricAlgebra.commutes, Algebra.algebraMap_eq_smul_one,
          LinearMap.map_smul]
      show r • bMinusLin (R := ℤ) a (1 : ConnesKreimer ℤ (Nonplanar α)) = 0
      -- bMinusLin a 1 = bMinusLin a (GL.of' 0) = bMinusBasis a 0 = 0.
      -- Bridge ConnesKreimer.of'/GrossmanLarson.of' via `show` (def-eq).
      rw [show (1 : ConnesKreimer ℤ (Nonplanar α)) =
              ConnesKreimer.of' (0 : Forest (Nonplanar α)) from
            (ConnesKreimer.of'_zero (R := ℤ) (T := Nonplanar α)).symm]
      show r • bMinusLin (R := ℤ) a (GrossmanLarson.of' (0 : Forest (Nonplanar α))) = 0
      rw [bMinusLin_of', bMinusBasis_zero, smul_zero]
    have h_RHS : ckIsoSymmetricAlgebra (bMinusLin_SL a (algebraMap ℤ SL r)) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      show ckIsoSymmetricAlgebra (bMinusLin_SL a (r • (1 : SL))) = 0
      rw [LinearMap.map_smul, bMinusLin_SL_one, smul_zero, _root_.map_zero]
    rw [h_LHS, h_RHS]
  | ι x =>
    -- ι x case: reduce by Finsupp.induction_linear on x.
    refine Finsupp.induction_linear x ?_ ?_ ?_
    · -- x = 0; both sides 0.
      show bMinusLin (R := ℤ) a (ckIsoSymmetricAlgebra
              (SymmetricAlgebra.ι ℤ LL 0)) =
           ckIsoSymmetricAlgebra (bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL 0))
      have h₀ : (SymmetricAlgebra.ι ℤ LL : LL →ₗ[ℤ] SL) 0 = (0 : SL) :=
        LinearMap.map_zero _
      rw [h₀, _root_.map_zero, _root_.map_zero, LinearMap.map_zero,
          _root_.map_zero]
    · -- x = x₁ + x₂; linearity.
      intro x₁ x₂ ih₁ ih₂
      show bMinusLin (R := ℤ) a (ckIsoSymmetricAlgebra
              (SymmetricAlgebra.ι ℤ LL (x₁ + x₂))) =
           ckIsoSymmetricAlgebra (bMinusLin_SL a
              (SymmetricAlgebra.ι ℤ LL (x₁ + x₂)))
      have h_add : (SymmetricAlgebra.ι ℤ LL : LL →ₗ[ℤ] SL) (x₁ + x₂) =
                    SymmetricAlgebra.ι ℤ LL x₁ + SymmetricAlgebra.ι ℤ LL x₂ :=
        LinearMap.map_add _ _ _
      rw [h_add, _root_.map_add, LinearMap.map_add, LinearMap.map_add,
          _root_.map_add, ih₁, ih₂]
    · -- x = single t r.
      intro t r
      have h_single : (Finsupp.single t r : InsertionAlgebra α) =
          r • (Finsupp.single t 1 : InsertionAlgebra α) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      show bMinusLin (R := ℤ) a (ckIsoSymmetricAlgebra
              (SymmetricAlgebra.ι ℤ LL (Finsupp.single t r))) =
           ckIsoSymmetricAlgebra (bMinusLin_SL a
              (SymmetricAlgebra.ι ℤ LL (Finsupp.single t r)))
      rw [h_single,
          show (SymmetricAlgebra.ι ℤ LL (r • Finsupp.single t (1 : ℤ)) : SL) =
              r • SymmetricAlgebra.ι ℤ LL (Finsupp.single t 1) from
            LinearMap.map_smul (SymmetricAlgebra.ι ℤ LL) r _,
          _root_.map_smul, LinearMap.map_smul, LinearMap.map_smul,
          _root_.map_smul,
          ckIsoSymmetricAlgebra_ι_single, bMinusLin_SL_ι]
      -- Goal: r • bMinusLin a (of'{t}) = r • ckIso ((psiA_L a) (single t 1)).
      -- Finsupp.single t 1 = InsertionAlgebra.ofTree t (definitionally).
      show r • bMinusLin (R := ℤ) a
              (ConnesKreimer.of' ({t} : Multiset (Nonplanar α))) =
           r • ckIsoSymmetricAlgebra
                (psiA_L a (InsertionAlgebra.ofTree t))
      rw [psiA_L_ofTree]
      -- Goal: r • bMinusLin a (of'{t}) = r • ckIso (psiA_basis a t)
      congr 1
      -- bMinusLin a (of'{t}) = bMinusBasis a {t}; case on rootValue t = a.
      show bMinusLin (R := ℤ) a (GrossmanLarson.of' ({t} : Forest (Nonplanar α))) =
           ckIsoSymmetricAlgebra (psiA_basis a t)
      rw [bMinusLin_of']
      -- Split on rootValue t = a.
      letI : Decidable (Nonplanar.rootValue t = a) := Classical.dec _
      unfold psiA_basis
      by_cases hlab : Nonplanar.rootValue t = a
      · -- rootValue t = a: t = node a (rootChildren t); both sides = of'(rootChildren t).
        rw [if_pos hlab]
        rw [show t = Nonplanar.node a (Nonplanar.rootChildren t) by
              rw [← hlab, Nonplanar.node_eta]]
        rw [bMinusBasis_singleton_node, Nonplanar.rootChildren_node]
        -- RHS: ckIso (∏ c, ιTree c) over rootChildren (node a (rootChildren t)).
        -- After substitution, rootChildren (node a F) = F, so we get
        -- ckIso (∏ c ∈ F, ιTree c) = of' F.
        exact (ckIso_prod_ιTree _).symm
      · -- rootValue t ≠ a; both sides 0.
        rw [if_neg hlab]
        rw [show bMinusBasis (R := ℤ) a ({t} : Forest (Nonplanar α)) = 0 from by
              apply bMinusBasis_eq_zero_of_not_singleton_a
              rintro ⟨G', hG⟩
              apply hlab
              have hT : t = Nonplanar.node a G' := Multiset.singleton_inj.mp hG
              rw [hT, Nonplanar.rootValue_node]]
        rw [_root_.map_zero]
  | mul X Y ihX ihY =>
    -- CK side: bMinusLin (ckIso (X*Y)) = bMinusLin (ckIso X * ckIso Y)
    --        = counit (ckIso X) • bMinusLin (ckIso Y)
    --        + counit (ckIso Y) • bMinusLin (ckIso X)
    rw [_root_.map_mul, bMinusLin_mul_eps, counit_ckIso, counit_ckIso,
        ihX, ihY]
    -- SL side: bMinusLin_SL (X*Y) = ε X • bMinusLin_SL Y + ε Y • bMinusLin_SL X.
    rw [bMinusLin_SL_mul_eps, _root_.map_add, _root_.map_smul, _root_.map_smul]
  | add X Y ihX ihY =>
    simp only [_root_.map_add]
    rw [ihX, ihY]

end CKTransport

/-! ### Trees as circle products of root and children

The root-grafting identity displayed in §3.1 of [oudom-guin-2008]: in the
free pre-Lie algebra of rooted trees,

```
• ∘ T₁ ... T_n  =  [tree with root • and children T₁, ..., T_n]
```

Here `InsertionAlgebra α` is the free pre-Lie algebra on `α`, and the
identity takes the form
`ι (ofTree (node a A')) = ι (ofTree (leaf a)) ○ ∏ c ∈ A', ι (ofTree c)`
(`iotaTree_node_via_circ`). -/

/-- `leaf a = node a 0`: the singleton-vertex tree is the empty-children
    node. -/
theorem leaf_eq_node_zero (a : α) :
    (Nonplanar.leaf a : Nonplanar α) = Nonplanar.node a 0 := rfl

/-! ### Helpers for the cancellation argument -/

/-- Leibniz formula for `○ ι X` over a multiset product (Notation 2.2 of
    [oudom-guin-2008]):

    `(M.map f).prod ○ ι X = Σ_{s ∈ M} ((M.erase s).map f).prod * (f s ○ ι X)`

    Each summand pulls out one factor `f s`, applies `○ ι X` to it, and keeps
    the rest of the product. -/
private theorem prod_oudomGuinCirc_ι {β : Type*} [DecidableEq β]
    (f : β → SL) (M : Multiset β) (X : LL) :
    oudomGuinCirc (R := ℤ) (M.map f).prod (SymmetricAlgebra.ι ℤ LL X) =
      (M.map (fun s => ((M.erase s).map f).prod *
        oudomGuinCirc (R := ℤ) (f s) (SymmetricAlgebra.ι ℤ LL X))).sum := by
  induction M using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero]
    rw [one_circ, SymmetricAlgebra.algebraMapInv_ι]
    exact zero_smul _ _
  | cons t M ih =>
    -- Leibniz on the head factor, IH on the tail; match termwise on s = t.
    rw [Multiset.map_cons, Multiset.prod_cons, oudomGuinCirc_mul_ι, ih]
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
    rw [mul_comm ((M.map f).prod) (oudomGuinCirc (f t) _)]
    congr 1
    rw [← Multiset.sum_map_mul_left]
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro s hs
    by_cases hst : s = t
    · subst hst
      have hM : M = s ::ₘ M.erase s := (Multiset.cons_erase hs).symm
      rw [Multiset.erase_cons_head]
      conv_rhs => rw [hM, Multiset.map_cons, Multiset.prod_cons]
      ring
    · have h_ne : t ≠ s := Ne.symm hst
      rw [Multiset.erase_cons_tail (s := M) h_ne, Multiset.map_cons,
          Multiset.prod_cons]
      ring

/-- Multiset identity: `B + (x ::ₘ C) = (x ::ₘ B) + C`. -/
private theorem cons_add_swap {β : Type*} (x : β) (B C : Multiset β) :
    B + (x ::ₘ C) = (x ::ₘ B) + C := by
  rw [Multiset.add_cons, ← Multiset.cons_add]

/-- Prefix-generalized auxiliary form of `insertSum_node_decompose`. The
    induction substrate: list-induction on `cs` with an arbitrary prefix
    `pre` carried in the inner `node`'s children-multiset. -/
private theorem insertSumList_bind_lift_aux [DecidableEq (Nonplanar α)]
    (a : α) (pre : Multiset (Nonplanar α))
    (cs : List (RoseTree α)) (c_pl : RoseTree α) :
    (RoseTree.insertSumList cs c_pl).map (fun cs' =>
      Nonplanar.node a (pre + ↑(cs'.map Nonplanar.mk))) =
    (↑(cs.map Nonplanar.mk) : Multiset (Nonplanar α)).bind (fun d =>
      (Nonplanar.insertSum d (Nonplanar.mk c_pl)).map (fun d' =>
        Nonplanar.node a (d' ::ₘ pre +
          (↑(cs.map Nonplanar.mk) : Multiset (Nonplanar α)).erase d))) := by
  induction cs generalizing pre with
  | nil =>
    simp only [RoseTree.insertSumList_nil, Multiset.map_zero,
               List.map_nil, Multiset.coe_nil, Multiset.zero_bind]
  | cons e cs' ih =>
    rw [RoseTree.insertSumList_cons, Multiset.map_add,
        Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def]
    -- Convert `↑((e :: cs').map mk)` to `mk e ::ₘ ↑(cs'.map mk)` (rfl) under
    -- all binders.
    simp only [show (↑((e :: cs').map Nonplanar.mk) : Multiset (Nonplanar α)) =
                    Nonplanar.mk e ::ₘ ↑(cs'.map Nonplanar.mk) from rfl]
    rw [Multiset.cons_bind, Multiset.erase_cons_head]
    refine congr_arg₂ (· + ·) ?_ ?_
    · -- First piece: head graft into `e`.
      rw [Nonplanar.mk_insertSum, Multiset.map_map]
      simp only [Function.comp_def]
      apply Multiset.map_congr rfl
      intro c' _
      -- Force the goal into cons form so `cons_add_swap` unifies directly.
      show Nonplanar.node a (pre + (Nonplanar.mk c' ::ₘ ↑(cs'.map Nonplanar.mk))) =
           Nonplanar.node a (Nonplanar.mk c' ::ₘ pre + ↑(cs'.map Nonplanar.mk))
      congr 1
      exact cons_add_swap (Nonplanar.mk c') pre _
    · -- Second piece: apply IH at `pre' = mk e ::ₘ pre`, then bridge to RHS.
      have hLHS_bridge :
          (RoseTree.insertSumList cs' c_pl).map (fun L' =>
            Nonplanar.node a (pre + ↑((e :: L').map Nonplanar.mk))) =
          (RoseTree.insertSumList cs' c_pl).map (fun L' =>
            Nonplanar.node a ((Nonplanar.mk e ::ₘ pre) + ↑(L'.map Nonplanar.mk))) := by
        apply Multiset.map_congr rfl
        intro L' _
        show Nonplanar.node a (pre + (Nonplanar.mk e ::ₘ ↑(L'.map Nonplanar.mk))) =
             Nonplanar.node a ((Nonplanar.mk e ::ₘ pre) + ↑(L'.map Nonplanar.mk))
        congr 1
        exact cons_add_swap (Nonplanar.mk e) pre _
      rw [hLHS_bridge, ih (Nonplanar.mk e ::ₘ pre)]
      -- Bridge IH-RHS form to RHS form (per-d, per-d' on the bind).
      apply Multiset.bind_congr
      intro d hd
      apply Multiset.map_congr rfl
      intro d' _
      congr 1
      conv_lhs => rw [Multiset.cons_add]
      conv_rhs => rw [Multiset.cons_add]
      congr 1
      -- Goal: (mk e ::ₘ pre) + ↑(cs'.map mk).erase d =
      --       pre + (mk e ::ₘ ↑(cs'.map mk)).erase d
      by_cases h : d = Nonplanar.mk e
      · subst h
        rw [Multiset.erase_cons_head]
        conv_rhs => rw [← Multiset.cons_erase hd]
        exact (cons_add_swap (Nonplanar.mk e) pre _).symm
      · have hne : Nonplanar.mk e ≠ d := fun heq => h heq.symm
        rw [Multiset.erase_cons_tail (s := ↑(cs'.map Nonplanar.mk)) hne]
        exact (cons_add_swap (Nonplanar.mk e) pre _).symm

/-- Grafting `c` at each vertex of `node a A''` splits into the root-graft
    summand `node a (c ::ₘ A'')` plus a bind over `A''` of subtree-grafts at
    each child `d ∈ A''`. -/
private theorem insertSum_node_decompose [DecidableEq (Nonplanar α)]
    (a : α) (A'' : Multiset (Nonplanar α)) (c : Nonplanar α) :
    Nonplanar.insertSum (Nonplanar.node a A'') c =
      Nonplanar.node a (c ::ₘ A'') ::ₘ
      A''.bind (fun d => (Nonplanar.insertSum d c).map
        (fun d' => Nonplanar.node a (d' ::ₘ A''.erase d))) := by
  -- Step 1: Substitute c = mk c_pl and A'' = ↑(cs.map mk) for planar reps.
  obtain ⟨c_pl, rfl⟩ : ∃ c_pl : RoseTree α, c = Nonplanar.mk c_pl :=
    ⟨c.out, c.out_eq.symm⟩
  obtain ⟨cs, rfl⟩ : ∃ cs : List (RoseTree α),
      A'' = (↑(cs.map Nonplanar.mk) : Multiset (Nonplanar α)) := by
    refine ⟨A''.toList.map Quotient.out, ?_⟩
    have h_cs_lift : (A''.toList.map Quotient.out).map Nonplanar.mk = A''.toList := by
      rw [List.map_map]
      induction A''.toList with
      | nil => rfl
      | cons hd tl ih =>
        show (Nonplanar.mk ∘ Quotient.out) hd ::
             tl.map (Nonplanar.mk ∘ Quotient.out) = hd :: tl
        rw [show (Nonplanar.mk ∘ Quotient.out) hd = hd from hd.out_eq, ih]
    rw [h_cs_lift]
    exact A''.coe_toList.symm
  -- Step 2: Reduce LHS via `node_mk_tree_list` + `mk_insertSum` +
  -- `RoseTree.insertSum_node` + `Multiset.map_cons`.
  rw [Nonplanar.node_mk_tree_list a cs, Nonplanar.mk_insertSum,
      RoseTree.insertSum_node, Multiset.map_cons]
  -- Step 3: Match the two cons-heads + tails separately.
  congr 1
  · -- Heads: `mk (RoseTree.node a (c_pl :: cs)) = node a (mk c_pl ::ₘ ↑(cs.map mk))`
    -- by `node_mk_tree_list`-symm + `cons_coe` (rfl).
    rw [← Nonplanar.node_mk_tree_list a (c_pl :: cs)]
    rfl
  · -- Tails: `((insertSumList cs c_pl).map (RoseTree.node a)).map mk = bind form`.
    rw [Multiset.map_map]
    -- LHS bridge: `(mk ∘ RoseTree.node a) cs' = node a (0 + ↑(cs'.map mk))`.
    have hLHS_eq : (RoseTree.insertSumList cs c_pl).map
          (Nonplanar.mk ∘ RoseTree.node a) =
        (RoseTree.insertSumList cs c_pl).map (fun cs' =>
          Nonplanar.node a (0 + ↑(cs'.map Nonplanar.mk))) := by
      apply Multiset.map_congr rfl
      intro cs' _
      show Nonplanar.mk (RoseTree.node a cs') =
           Nonplanar.node a (0 + ↑(cs'.map Nonplanar.mk))
      rw [Multiset.zero_add, Nonplanar.node_mk_tree_list]
    -- RHS bridge: drop `+ 0` inside the bind.
    have hRHS_eq :
        ((↑(cs.map Nonplanar.mk) : Multiset (Nonplanar α))).bind (fun d =>
          (Nonplanar.insertSum d (Nonplanar.mk c_pl)).map (fun d' =>
            Nonplanar.node a (d' ::ₘ (0 : Multiset (Nonplanar α)) +
              ((↑(cs.map Nonplanar.mk) : Multiset (Nonplanar α))).erase d))) =
        ((↑(cs.map Nonplanar.mk) : Multiset (Nonplanar α))).bind (fun d =>
          (Nonplanar.insertSum d (Nonplanar.mk c_pl)).map (fun d' =>
            Nonplanar.node a (d' ::ₘ
              ((↑(cs.map Nonplanar.mk) : Multiset (Nonplanar α))).erase d))) := by
      apply Multiset.bind_congr
      intro d _
      apply Multiset.map_congr rfl
      intro d' _
      simp only [Multiset.cons_add, Multiset.zero_add]
    rw [hLHS_eq, insertSumList_bind_lift_aux (α := α) a 0 cs c_pl, hRHS_eq]

/-- `ι (ofMultiset M) = Σ_{t ∈ M} ι (ofTree t)`. -/
private theorem iota_ofMultiset (M : Multiset (Nonplanar α)) :
    SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofMultiset M) =
      (M.map (fun t => SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree t))).sum := by
  induction M using Multiset.induction with
  | empty =>
    simp only [InsertionAlgebra.ofMultiset_zero, map_zero, Multiset.map_zero,
               Multiset.sum_zero]
  | cons t M ih =>
    rw [InsertionAlgebra.ofMultiset_cons, map_add, ih,
        Multiset.map_cons, Multiset.sum_cons]

/-! ### The tree-decomposition identity -/

/-- Every nonplanar tree is the circle product of its singleton-vertex root
    with its children-forest:

    `ι (ofTree (node a A')) = ι (ofTree (leaf a)) ○ ∏ c ∈ A', ι (ofTree c)`

    This is the root-grafting identity displayed in §3.1 of
    [oudom-guin-2008]. The induction is on the children-multiset cardinality;
    weight is conserved by subtree grafting and is not a valid measure. -/
theorem iotaTree_node_via_circ (a : α) (A' : Multiset (Nonplanar α)) :
    SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree (Nonplanar.node a A')) =
    oudomGuinCirc
        (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree (Nonplanar.leaf a)))
        ((A'.map (fun c =>
            SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c))).prod) := by
  classical
  -- Set up abbreviations for readability.
  set f : Nonplanar α → SL :=
    fun c => SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c) with hf
  set ιa : SL := SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree (Nonplanar.leaf a))
    with hιa
  -- Reduce to a Nat-indexed statement, then do strong induction on Nat.
  suffices H : ∀ n A' (h : Multiset.card A' = n),
      SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree (Nonplanar.node a A')) =
      oudomGuinCirc (R := ℤ) ιa ((A'.map f).prod) by
    exact H A'.card A' rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro A' hA'
    -- Base case: A' = 0 (card 0). node a 0 = leaf a. prod 0 = 1.
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- n = 0 case
      subst hn
      have hA'0 : A' = 0 := Multiset.card_eq_zero.mp hA'
      subst hA'0
      simp only [Multiset.map_zero, Multiset.prod_zero, ← leaf_eq_node_zero, hιa]
      rw [circ_one_right]
    · -- n ≥ 1. A' is nonempty; pick a head element.
      have hA'_ne : A' ≠ 0 := by
        intro h
        rw [h, Multiset.card_zero] at hA'
        omega
      -- Decompose A' = c ::ₘ A'' for some c, A''.
      obtain ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero hA'_ne
      obtain ⟨A'', rfl⟩ := Multiset.exists_cons_of_mem hc
      have hA''_card : Multiset.card A'' = n - 1 := by
        rw [Multiset.card_cons] at hA'
        omega
      have h_sub_lt : n - 1 < n := Nat.sub_lt hn Nat.one_pos
      -- Apply IH to A'' at cardinality n - 1.
      have ih_A'' : SymmetricAlgebra.ι ℤ LL
            (InsertionAlgebra.ofTree (Nonplanar.node a A'')) =
          oudomGuinCirc (R := ℤ) ιa ((A''.map f).prod) :=
        IH (n - 1) h_sub_lt A'' hA''_card
      -- Set up abbreviations for the RHS pieces.
      set Q : SL := (A''.map f).prod
      set Qιc : SL :=
        oudomGuinCirc (R := ℤ) Q (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c))
      set SG : Multiset (Nonplanar α) :=
        A''.bind (fun d => (Nonplanar.insertSum d c).map
          (fun d' => Nonplanar.node a (d' ::ₘ A''.erase d)))
      -- Suffices the cancellation: ιa ○ Qιc = ι(ofMultiset SG).
      suffices h_cancel :
          oudomGuinCirc (R := ℤ) ιa Qιc =
          SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofMultiset SG) by
        -- Unfold the LHS prod cons and commute.
        rw [Multiset.map_cons, Multiset.prod_cons]
        -- Goal: ι(node a (c ::ₘ A'')) = ιa ○ (f c * Q)
        rw [mul_comm (f c) Q]
        -- Goal: ι(node a (c ::ₘ A'')) = ιa ○ (Q * f c)
        show SymmetricAlgebra.ι ℤ LL _ =
          oudomGuinCirc (R := ℤ) ιa
            (Q * SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c))
        rw [circ_T_mul]
        -- Goal: ι(node a (c::A'')) = (ιa ○ Q) ○ ι c - ιa ○ (Q ○ ι c)
        rw [← ih_A'']
        -- Goal: ι(node a (c::A'')) = ι(node a A'') ○ ι c - ιa ○ Qιc
        rw [circ_ι_ι, InsertionAlgebra.ofTree_mul_ofTree,
            insertSum_node_decompose a A'' c,
            InsertionAlgebra.ofMultiset_cons, map_add, h_cancel]
        -- Goal: ι(node a (c::A'')) = (ι(node a (c::A'')) + ι(ofMultiset SG)) - ι(ofMultiset SG)
        ring
      -- Now prove the cancellation: ιa ○ (Q ○ ι c) = ι(ofMultiset SG).
      -- Apply IH to each (d' ::ₘ A''.erase d) (cardinality n - 1 < n).
      have h_inner : ∀ d ∈ A'', ∀ d' ∈ Nonplanar.insertSum d c,
          SymmetricAlgebra.ι ℤ LL
            (InsertionAlgebra.ofTree
              (Nonplanar.node a (d' ::ₘ A''.erase d))) =
          oudomGuinCirc (R := ℤ) ιa (((d' ::ₘ A''.erase d).map f).prod) := by
        intro d hd d' _
        have hA''_pos : 0 < Multiset.card A'' :=
          Multiset.card_pos_iff_exists_mem.mpr ⟨d, hd⟩
        have h_card : Multiset.card (d' ::ₘ A''.erase d) = n - 1 := by
          rw [Multiset.card_cons, Multiset.card_erase_of_mem hd, hA''_card,
              Nat.pred_eq_sub_one]
          omega
        exact IH (n - 1) h_sub_lt (d' ::ₘ A''.erase d) h_card
      -- RHS: ι(ofMultiset SG) = (SG.map (ι ∘ ofTree)).sum.
      -- SG = A''.bind (...) so ι(ofMultiset SG) becomes a bind of mapped sums.
      rw [iota_ofMultiset]
      simp only [SG, Multiset.map_bind, Multiset.map_map, Function.comp_def]
      -- After fusing maps, the inner function inside the bind is:
      -- fun d' => ι(ofTree (node a (d' ::ₘ A''.erase d))).
      -- Substitute via h_inner.
      rw [show A''.bind (fun d =>
                (Nonplanar.insertSum d c).map (fun d' =>
                  SymmetricAlgebra.ι ℤ LL
                    (InsertionAlgebra.ofTree
                      (Nonplanar.node a (d' ::ₘ A''.erase d))))) =
              A''.bind (fun d =>
                (Nonplanar.insertSum d c).map (fun d' =>
                  oudomGuinCirc (R := ℤ) ιa
                    (((d' ::ₘ A''.erase d).map f).prod))) from ?_]
      · -- Compute the LHS via the Leibniz formula + ι linearity.
        show oudomGuinCirc (R := ℤ) ιa Qιc = _
        show oudomGuinCirc (R := ℤ) ιa
          (oudomGuinCirc (R := ℤ) Q
            (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c))) = _
        rw [show Q = (A''.map f).prod from rfl,
            prod_oudomGuinCirc_ι f A'' (InsertionAlgebra.ofTree c)]
        rw [map_multiset_sum, Multiset.map_map]
        rw [Multiset.sum_bind]
        -- Both sides are sums over A''; match termwise.
        apply congrArg Multiset.sum
        apply Multiset.map_congr rfl
        intro d hd
        simp only [Function.comp_apply]
        simp only [Multiset.map_cons, Multiset.prod_cons]
        -- f d ○ ι c = ι (ofMultiset (insertSum d c)).
        have h_fd_circ : oudomGuinCirc (R := ℤ) (f d)
            (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c)) =
            SymmetricAlgebra.ι ℤ LL
              (InsertionAlgebra.ofMultiset (Nonplanar.insertSum d c)) := by
          rw [hf]
          show oudomGuinCirc (R := ℤ)
            (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree d))
            (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c)) = _
          rw [circ_ι_ι, InsertionAlgebra.ofTree_mul_ofTree]
        rw [h_fd_circ]
        rw [iota_ofMultiset, ← Multiset.sum_map_mul_left, map_multiset_sum,
            Multiset.map_map]
        -- Both sides are sums over (insertSum d c); match termwise.
        apply congrArg Multiset.sum
        apply Multiset.map_congr rfl
        intro d' _
        simp only [Function.comp_apply]
        rw [mul_comm ((A''.erase d).map f).prod _]
      · -- Bind congruence for the substitution via h_inner.
        apply Multiset.bind_congr
        intro d hd
        apply Multiset.map_congr rfl
        intro d' hd'
        exact h_inner d hd d' hd'

/-! ### The circle-product identity for `psiA_L`

`psiA_L_circByT_total_eq`:
`psiA_L a (circByT_total Y B) = oudomGuinStar (psiA_L a Y) B`, consumed by
the `ι` case of `bMinusLin_SL_oudomGuinStar`. -/

/-- `psiA_L a (ofMultiset M) = (M.map (psiA_basis a)).sum`. -/
private theorem psiA_L_ofMultiset (a : α) (M : Multiset (Nonplanar α)) :
    psiA_L a (InsertionAlgebra.ofMultiset M) =
      (M.map (psiA_basis a)).sum := by
  induction M using Multiset.induction with
  | empty =>
    simp only [InsertionAlgebra.ofMultiset_zero, map_zero,
               Multiset.map_zero, Multiset.sum_zero]
  | cons t M ih =>
    rw [InsertionAlgebra.ofMultiset_cons, map_add, ih,
        Multiset.map_cons, Multiset.sum_cons, psiA_L_ofTree]

/-- Closed form for `psiA_basis a (node a A)` (self-color case):
    `(A.map ιTree).prod`. -/
private theorem psiA_basis_node_self (a : α) (A : Multiset (Nonplanar α)) :
    psiA_basis a (Nonplanar.node a A) =
      (A.map (fun c => ιTree c)).prod := by
  unfold psiA_basis
  rw [Nonplanar.rootValue_node, Nonplanar.rootChildren_node]
  exact if_pos rfl

/-- Closed form for `psiA_basis a (node a' A)` (off-color case): `0`. -/
private theorem psiA_basis_node_ne (a a' : α) (h : a' ≠ a)
    (A : Multiset (Nonplanar α)) :
    psiA_basis a (Nonplanar.node a' A) = 0 := by
  unfold psiA_basis
  rw [Nonplanar.rootValue_node]
  exact if_neg h

/-- Cocycle rule for `psiA_L` on the insertion algebra:
    `psiA_L a (Y * Z) = (psiA_L a Y) ○ ι Z + psiA_L a Y * ι Z`. -/
private theorem psiA_L_mul_eq [DecidableEq (Nonplanar α)]
    (a : α) (Y Z : LL) :
    psiA_L a (Y * Z) =
      oudomGuinCirc (R := ℤ) (psiA_L a Y) (SymmetricAlgebra.ι ℤ LL Z) +
      psiA_L a Y * SymmetricAlgebra.ι ℤ LL Z := by
  classical
  suffices h_basis : ∀ (t s : Nonplanar α),
      psiA_L a (InsertionAlgebra.ofTree t * InsertionAlgebra.ofTree s) =
        oudomGuinCirc (R := ℤ) (psiA_L a (InsertionAlgebra.ofTree t))
          (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree s)) +
        psiA_L a (InsertionAlgebra.ofTree t) *
          SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree s) by
    -- Outer Y-extension via Finsupp.induction_linear.
    -- Use the `let ... := ...` pattern (per BMinus.lean) to bind bound-type
    -- variables at LL type, then `show` to reformulate the goal in LL terms.
    induction Y using Finsupp.induction_linear with
    | zero =>
      let Y' : LL := (0 : LL)
      show psiA_L a (Y' * Z) =
           oudomGuinCirc (R := ℤ) (psiA_L a Y')
             (SymmetricAlgebra.ι ℤ LL Z) +
           psiA_L a Y' * SymmetricAlgebra.ι ℤ LL Z
      show psiA_L a ((0 : LL) * Z) = _
      rw [InsertionAlgebra.zero_mul, map_zero, map_zero,
          LinearMap.zero_apply, zero_mul, add_zero]
    | add Y₁ Y₂ ih₁ ih₂ =>
      let Y₁' : LL := Y₁
      let Y₂' : LL := Y₂
      show psiA_L a ((Y₁' + Y₂') * Z) =
           oudomGuinCirc (R := ℤ) (psiA_L a (Y₁' + Y₂'))
             (SymmetricAlgebra.ι ℤ LL Z) +
           psiA_L a (Y₁' + Y₂') * SymmetricAlgebra.ι ℤ LL Z
      rw [InsertionAlgebra.add_mul, map_add, ih₁, ih₂,
          map_add, (oudomGuinCirc (R := ℤ)).map_add,
          LinearMap.add_apply, add_mul]
      abel
    | single t r =>
      let Y' : LL := Finsupp.single t r
      show psiA_L a (Y' * Z) =
           oudomGuinCirc (R := ℤ) (psiA_L a Y')
             (SymmetricAlgebra.ι ℤ LL Z) +
           psiA_L a Y' * SymmetricAlgebra.ι ℤ LL Z
      rw [show Y' = r • InsertionAlgebra.ofTree t from
            (Finsupp.smul_single_one t r).symm,
          smul_mul_assoc, map_smul, map_smul,
          show oudomGuinCirc (R := ℤ)
              (r • psiA_L a (InsertionAlgebra.ofTree t))
              (SymmetricAlgebra.ι ℤ LL Z) =
            r • oudomGuinCirc (R := ℤ) (psiA_L a (InsertionAlgebra.ofTree t))
              (SymmetricAlgebra.ι ℤ LL Z) from
            LinearMap.congr_fun ((oudomGuinCirc (R := ℤ)).map_smul r _) _,
          smul_mul_assoc, ← smul_add]
      congr 1
      -- Inner Z-extension via Finsupp.induction_linear.
      induction Z using Finsupp.induction_linear with
      | zero =>
        let Z' : LL := (0 : LL)
        show psiA_L a (InsertionAlgebra.ofTree t * Z') =
             oudomGuinCirc (R := ℤ) (psiA_L a (InsertionAlgebra.ofTree t))
               (SymmetricAlgebra.ι ℤ LL Z') +
             psiA_L a (InsertionAlgebra.ofTree t) *
               SymmetricAlgebra.ι ℤ LL Z'
        show psiA_L a (InsertionAlgebra.ofTree t * (0 : LL)) = _
        rw [mul_zero, map_zero, map_zero, map_zero,
            mul_zero, add_zero]
      | add Z₁ Z₂ ih₁' ih₂' =>
        let Z₁' : LL := Z₁
        let Z₂' : LL := Z₂
        show psiA_L a (InsertionAlgebra.ofTree t * (Z₁' + Z₂')) =
             oudomGuinCirc (R := ℤ) (psiA_L a (InsertionAlgebra.ofTree t))
               (SymmetricAlgebra.ι ℤ LL (Z₁' + Z₂')) +
             psiA_L a (InsertionAlgebra.ofTree t) *
               SymmetricAlgebra.ι ℤ LL (Z₁' + Z₂')
        rw [mul_add, map_add, ih₁', ih₂', map_add,
            (oudomGuinCirc (R := ℤ) (psiA_L a (InsertionAlgebra.ofTree t))).map_add,
            mul_add]
        abel
      | single s u =>
        let Z' : LL := Finsupp.single s u
        show psiA_L a (InsertionAlgebra.ofTree t * Z') =
             oudomGuinCirc (R := ℤ) (psiA_L a (InsertionAlgebra.ofTree t))
               (SymmetricAlgebra.ι ℤ LL Z') +
             psiA_L a (InsertionAlgebra.ofTree t) *
               SymmetricAlgebra.ι ℤ LL Z'
        rw [show Z' = u • InsertionAlgebra.ofTree s from
              (Finsupp.smul_single_one s u).symm,
            mul_smul_comm, map_smul, map_smul, map_smul, mul_smul_comm,
            ← smul_add]
        congr 1
        exact h_basis t s
  -- Basis case.
  intro t s
  obtain ⟨a', A', rfl⟩ : ∃ a' A', t = Nonplanar.node a' A' :=
    ⟨t.rootValue, t.rootChildren, (Nonplanar.node_eta t).symm⟩
  set ιs : SL := SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree s) with hιs
  rw [InsertionAlgebra.ofTree_mul_ofTree, insertSum_node_decompose,
      InsertionAlgebra.ofMultiset_cons, map_add, psiA_L_ofTree,
      psiA_L_ofMultiset, psiA_L_ofTree]
  by_cases ha : a' = a
  · -- Case a' = a. Rewrite all a' to a via ha.
    rw [ha]
    -- Use closed-form for psiA_basis a (node a B) = (B.map ιTree).prod.
    rw [psiA_basis_node_self, psiA_basis_node_self]
    -- LHS first term: ((s ::ₘ A').map ιTree).prod = ιTree s * Q
    rw [Multiset.map_cons, Multiset.prod_cons]
    -- Q := (A'.map ιTree).prod
    set Q : SL := (A'.map (fun c => ιTree c)).prod with hQ
    have h_ιTree_s : (ιTree s : SL) = ιs := rfl
    rw [h_ιTree_s, mul_comm ιs Q]
    rw [add_comm (oudomGuinCirc (R := ℤ) Q ιs) (Q * ιs)]
    congr 1
    -- Need: bind-sum = Q ○ ιs.
    rw [hQ, prod_oudomGuinCirc_ι (fun c => ιTree c) A'
          (InsertionAlgebra.ofTree s)]
    rw [Multiset.map_bind]
    rw [show A'.bind (fun d =>
                ((Nonplanar.insertSum d s).map (fun d' =>
                  Nonplanar.node a (d' ::ₘ A'.erase d))).map (psiA_basis a)) =
            A'.bind (fun d =>
              (Nonplanar.insertSum d s).map (fun d' =>
                ιTree d' * ((A'.erase d).map (fun c => ιTree c)).prod))
        from by
      apply Multiset.bind_congr
      intro d _
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro d' _
      rw [Function.comp_apply, psiA_basis_node_self]
      rw [Multiset.map_cons, Multiset.prod_cons]]
    rw [Multiset.sum_bind]
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro d _
    have h_circ_d : oudomGuinCirc (R := ℤ) (ιTree d) ιs =
        ((Nonplanar.insertSum d s).map (fun t' => ιTree t')).sum := by
      show oudomGuinCirc (R := ℤ)
            (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree d))
            (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree s)) = _
      rw [circ_ι_ι, InsertionAlgebra.ofTree_mul_ofTree, iota_ofMultiset]
      rfl
    rw [h_circ_d, ← Multiset.sum_map_mul_left]
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro d' _
    ring
  · -- Case a' ≠ a.
    have h_zero : ∀ (B : Multiset (Nonplanar α)),
        psiA_basis a (Nonplanar.node a' B) = 0 := psiA_basis_node_ne a a' ha
    -- Show LHS = 0 and RHS = 0 separately.
    have h_LHS_zero : psiA_basis a (Nonplanar.node a' (s ::ₘ A')) +
        ((A'.bind (fun d =>
          (Nonplanar.insertSum d s).map (fun d' =>
            Nonplanar.node a' (d' ::ₘ A'.erase d)))).map (psiA_basis a)).sum =
        (0 : SL) := by
      rw [h_zero, zero_add, Multiset.map_bind]
      rw [show A'.bind (fun d =>
                ((Nonplanar.insertSum d s).map (fun d' =>
                  Nonplanar.node a' (d' ::ₘ A'.erase d))).map (psiA_basis a)) =
              A'.bind (fun d =>
                (Nonplanar.insertSum d s).map (fun _ : Nonplanar α => (0 : SL)))
          from by
        apply Multiset.bind_congr
        intro d _
        rw [Multiset.map_map]
        apply Multiset.map_congr rfl
        intro d' _
        exact h_zero _]
      rw [Multiset.sum_bind]
      rw [show A'.map (fun d => ((Nonplanar.insertSum d s).map
                (fun _ : Nonplanar α => (0 : SL))).sum) =
              A'.map (fun _ : Nonplanar α => (0 : SL)) from by
        apply Multiset.map_congr rfl
        intro d _
        rw [Multiset.map_const', Multiset.sum_replicate, smul_zero]]
      rw [Multiset.map_const', Multiset.sum_replicate, smul_zero]
    have h_RHS_zero :
        oudomGuinCirc (R := ℤ) (psiA_basis a (Nonplanar.node a' A')) ιs +
          psiA_basis a (Nonplanar.node a' A') * ιs = (0 : SL) := by
      rw [h_zero, LinearMap.map_zero, LinearMap.zero_apply,
          zero_mul, add_zero]
    rw [h_LHS_zero, h_RHS_zero]

open PreLie.OudomGuinCircConstruct in
/-- Peel the last factor of a tprod through `algHomL`:
    `algHomL (tprod (n+1) f) = algHomL (tprod n (init f)) * ι (f (last n))`. -/
private theorem algHomL_tprod_succ (n : ℕ) (f : Fin (n + 1) → LL) :
    algHomL (R := ℤ) (L := LL) (TensorAlgebra.tprod ℤ LL (n + 1) f) =
      algHomL (R := ℤ) (L := LL) (TensorAlgebra.tprod ℤ LL n (Fin.init f)) *
        SymmetricAlgebra.ι ℤ LL (f (Fin.last n)) := by
  have h_tprod_succ :
      TensorAlgebra.tprod ℤ LL (n + 1) f =
      TensorAlgebra.tprod ℤ LL n (Fin.init f) *
        TensorAlgebra.ι ℤ (f (Fin.last n)) := by
    conv_lhs => rw [show f = Fin.snoc (Fin.init f) (f (Fin.last n)) from
      (Fin.snoc_init_self f).symm]
    rw [Fin.snoc_eq_append, ι_eq_tprod_one, ← tprod_mul_tprod]
    congr 1
  rw [h_tprod_succ, algHomL_apply, map_mul]
  rfl

/-- TA-descent for `psiA_L a ∘ circByT_total T`: its value on `X : SL` is
    `g X` once the per-tprod values match `g ∘ₗ algHomL`. -/
private theorem psiA_L_circByT_eq_of_per_tprod (a : α) (T : LL)
    (g : SL →ₗ[ℤ] SL)
    (h : ∀ (n : ℕ) (f : Fin n → LL),
      psiA_L a (PreLie.OudomGuinCircConstruct.circTMultilinear ℤ T n f) =
      g (PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL)
          (TensorAlgebra.tprod ℤ LL n f)))
    (X : SL) :
    psiA_L a
        (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) T X) = g X := by
  obtain ⟨z, rfl⟩ := PreLie.OudomGuinCircConstruct.algHomL_surjective X
  have h_eq :
      (psiA_L a).comp
        ((PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) T).comp
          (PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL))) =
      g.comp (PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL)) := by
    apply PreLie.OudomGuinCircConstruct.TA_linearMap_ext_tprod
    intro n f
    simp only [LinearMap.comp_apply]
    have h_tot := LinearMap.congr_fun
      (PreLie.OudomGuinCircConstruct.circByT_total_comp_algHomL (R := ℤ) T)
      (TensorAlgebra.tprod ℤ LL n f)
    simp only [LinearMap.comp_apply] at h_tot
    rw [h_tot, PreLie.OudomGuinCircConstruct.circTTensor_tprod]
    exact h n f
  exact LinearMap.congr_fun h_eq z

/-- `psiA_L a` inverts grafting onto an `a`-colored leaf:
    `psiA_L a (circByT_total (leaf a) X) = X`. -/
private theorem psiA_L_circByT_leaf_eq_id [DecidableEq (Nonplanar α)]
    (a : α) (X : SL) :
    psiA_L a (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
      (InsertionAlgebra.ofTree (Nonplanar.leaf a)) X) = X := by
  classical
  have h : ∀ (n : ℕ) (f : Fin n → LL),
      psiA_L a (PreLie.OudomGuinCircConstruct.circTMultilinear ℤ
        (InsertionAlgebra.ofTree (Nonplanar.leaf a)) n f) =
      PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL)
        (TensorAlgebra.tprod ℤ LL n f) := by
    intro n
    induction n with
    | zero =>
      intro f
      rw [PreLie.OudomGuinCircConstruct.circTMultilinear_zero, psiA_L_ofTree,
          leaf_eq_node_zero, psiA_basis_node_self, Multiset.map_zero,
          Multiset.prod_zero, tprod_zero, algHomL_apply, map_one]
    | succ n IH =>
      intro f
      rw [PreLie.OudomGuinCircConstruct.circTMultilinear_succ, map_sub,
          map_sum, psiA_L_mul_eq, IH (Fin.init f),
          oudomGuinCirc_algHomL_tprod_ι (f (Fin.last n)) n (Fin.init f)]
      simp only [IH]
      rw [add_sub_cancel_left, algHomL_tprod_succ]
  exact psiA_L_circByT_eq_of_per_tprod a _ LinearMap.id (fun n f => h n f) X

/-- `psiA_L a` kills grafting onto an off-color leaf: for `a' ≠ a`,
    `psiA_L a (circByT_total (leaf a') X) = 0`. -/
private theorem psiA_L_circByT_leaf_eq_zero [DecidableEq (Nonplanar α)]
    (a a' : α) (h : a' ≠ a) (X : SL) :
    psiA_L a (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
      (InsertionAlgebra.ofTree (Nonplanar.leaf a')) X) = 0 := by
  classical
  have h_per : ∀ (n : ℕ) (f : Fin n → LL),
      psiA_L a (PreLie.OudomGuinCircConstruct.circTMultilinear ℤ
        (InsertionAlgebra.ofTree (Nonplanar.leaf a')) n f) = 0 := by
    intro n
    induction n with
    | zero =>
      intro f
      rw [PreLie.OudomGuinCircConstruct.circTMultilinear_zero, psiA_L_ofTree,
          leaf_eq_node_zero, psiA_basis_node_ne a a' h]
    | succ n IH =>
      intro f
      rw [PreLie.OudomGuinCircConstruct.circTMultilinear_succ, map_sub,
          map_sum, psiA_L_mul_eq, IH (Fin.init f)]
      -- IH gives 0 for leading-term Y. So 0 ○ ι _ + 0 * ι _ = 0.
      rw [LinearMap.map_zero, LinearMap.zero_apply, zero_add, zero_mul]
      simp only [IH, Finset.sum_const_zero, sub_zero]
  exact psiA_L_circByT_eq_of_per_tprod a _ 0 (fun n f => h_per n f) X

/-- `psiA_L a (circByT_total Y B) = oudomGuinStar (psiA_L a Y) B`. Factors a
    basis tree as root ○ children (`iotaTree_node_via_circ`) and reassociates
    via Prop 2.8.v of [oudom-guin-2008] (`circ_assoc_via_comul`). -/
private theorem psiA_L_circByT_total_eq [DecidableEq (Nonplanar α)]
    (a : α) (Y : LL) (B : SL) :
    psiA_L a
        ((PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) (L := LL) Y) B) =
      oudomGuinStar (psiA_L a Y) B := by
  classical
  induction Y using Finsupp.induction_linear with
  | zero =>
    let Y' : LL := (0 : LL)
    show psiA_L a ((PreLie.OudomGuinCircConstruct.circByT_total
      (R := ℤ) (L := LL) Y') B) =
         oudomGuinStar (psiA_L a Y') B
    have h_circByT_zero :
        PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) (L := LL) (0 : LL)
          = 0 :=
      PreLie.OudomGuinCircConstruct.circByT_totalLM.map_zero
    show psiA_L a ((PreLie.OudomGuinCircConstruct.circByT_total
      (R := ℤ) (L := LL) (0 : LL)) B) = _
    rw [h_circByT_zero, LinearMap.zero_apply, map_zero,
        oudomGuinStar_zero_left]
  | add Y₁ Y₂ ih₁ ih₂ =>
    let Y₁' : LL := Y₁
    let Y₂' : LL := Y₂
    show psiA_L a ((PreLie.OudomGuinCircConstruct.circByT_total
      (R := ℤ) (L := LL) (Y₁' + Y₂')) B) =
         oudomGuinStar (psiA_L a (Y₁' + Y₂')) B
    rw [PreLie.OudomGuinCircConstruct.circByT_total_T_add,
        LinearMap.add_apply, map_add, map_add, oudomGuinStar_add_left, ih₁, ih₂]
  | single t r =>
    let Y' : LL := Finsupp.single t r
    show psiA_L a ((PreLie.OudomGuinCircConstruct.circByT_total
      (R := ℤ) (L := LL) Y') B) =
         oudomGuinStar (psiA_L a Y') B
    have hY : Y' = r • InsertionAlgebra.ofTree t :=
      (Finsupp.smul_single_one t r).symm
    rw [hY]
    have h_psi_smul :
        psiA_L a (r • InsertionAlgebra.ofTree t) =
          r • psiA_L a (InsertionAlgebra.ofTree t) :=
      map_smul _ _ _
    have h_LHS_eq :
        psiA_L a ((PreLie.OudomGuinCircConstruct.circByT_total
            (R := ℤ) (L := LL) (r • InsertionAlgebra.ofTree t)) B) =
          r • psiA_L a ((PreLie.OudomGuinCircConstruct.circByT_total
            (R := ℤ) (L := LL) (InsertionAlgebra.ofTree t)) B) := by
      rw [PreLie.OudomGuinCircConstruct.circByT_total_T_smul,
          LinearMap.smul_apply, map_smul]
    have h_RHS_eq :
        oudomGuinStar (psiA_L a (r • InsertionAlgebra.ofTree t)) B =
          r • oudomGuinStar (psiA_L a (InsertionAlgebra.ofTree t)) B := by
      rw [h_psi_smul]
      exact oudomGuinStar_smul_left r _ _
    rw [h_LHS_eq, h_RHS_eq]
    congr 1
    -- Now: psiA_L a (circByT_total (ofTree t) B) = (psiA_L a (ofTree t)) ★ B.
    obtain ⟨a', A', rfl⟩ : ∃ a' A', t = Nonplanar.node a' A' :=
      ⟨t.rootValue, t.rootChildren, (Nonplanar.node_eta t).symm⟩
    set Q : SL := (A'.map (fun c => SymmetricAlgebra.ι ℤ LL
      (InsertionAlgebra.ofTree c))).prod with hQ
    have h_circ_node :
        SymmetricAlgebra.ι ℤ LL
          (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
            (InsertionAlgebra.ofTree (Nonplanar.node a' A')) B) =
        SymmetricAlgebra.ι ℤ LL
          (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
            (InsertionAlgebra.ofTree (Nonplanar.leaf a')) (oudomGuinStar Q B)) := by
      rw [← oudomGuinCirc_ι_apply, ← oudomGuinCirc_ι_apply,
          iotaTree_node_via_circ a' A', circ_assoc_via_comul]
      rfl
    have h_psi_eq :
        psiA_L a (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
          (InsertionAlgebra.ofTree (Nonplanar.node a' A')) B) =
        psiA_L a (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
          (InsertionAlgebra.ofTree (Nonplanar.leaf a')) (oudomGuinStar Q B)) := by
      simpa only [bMinusLin_SL_ι] using congrArg (bMinusLin_SL a) h_circ_node
    rw [h_psi_eq, psiA_L_ofTree]
    by_cases ha : a' = a
    · subst ha
      rw [psiA_L_circByT_leaf_eq_id, psiA_basis_node_self]
      rfl
    · rw [psiA_L_circByT_leaf_eq_zero a a' ha,
          psiA_basis_node_ne a a' ha, oudomGuinStar_zero_left]

/-! ### Helpers for the cocycle `mul` case -/

/-- Reformulation of `B⁻_a(A ★ B)` via `B⁻_a` and `○`:

    `B⁻_a(A ★ B) = ε(A) • B⁻_a B + B⁻_a(A ○ B)`.

    Follows from counit-Leibniz on `B⁻_a` (`bMinusLin_SL_mul_eps`) applied to
    the Sweedler expansion `A ★ B = mul' ((TP.map (○A) id)(cm B))`, then the
    counit-comul triangle on both summands. -/
private theorem bMinusLin_SL_star_eq (a : α) (A B : SL) :
    bMinusLin_SL a (oudomGuinStar A B) =
      SymmetricAlgebra.algebraMapInv (M := LL) A • bMinusLin_SL a B +
      bMinusLin_SL a (oudomGuinCirc (R := ℤ) A B) := by
  -- Apply counit-Leibniz pointwise on the Sweedler expansion of A ★ B,
  -- then collapse via the two counit-comul triangles.
  letI inst_B : Bialgebra ℤ (SymmetricAlgebra ℤ LL) := SymmetricAlgebra.instBialgebra ℤ LL
  letI inst_Co : Coalgebra ℤ (SymmetricAlgebra ℤ LL) := inst_B.toCoalgebra
  letI inst_C : CoalgebraStruct ℤ (SymmetricAlgebra ℤ LL) := inst_Co.toCoalgebraStruct
  set cmB : SL ⊗[ℤ] SL :=
    (Bialgebra.comulAlgHom ℤ (SymmetricAlgebra ℤ LL)).toLinearMap B with hcmB
  -- Step 1: LinearMap identity F = F₁ + F₂ on `SL ⊗ SL → SL` where
  --   F   = B⁻_a ∘ mul' ∘ (TP.map (○A) id)              [evaluated at cm B = A ★ B]
  --   F₁  = ε(A) • B⁻_a ∘ mul' ∘ (TP.map (η∘ε) id)      [collapses to ε(A) • B⁻_a B]
  --   F₂  = B⁻_a ∘ (○A) ∘ mul' ∘ (TP.map id (η∘ε))      [collapses to B⁻_a(A○B)]
  set η : ℤ →ₗ[ℤ] SL := Algebra.linearMap ℤ SL with hη_def
  set εL : SL →ₗ[ℤ] ℤ :=
    (SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)).toLinearMap with hεL_def
  -- The "left" projection: F₁(b₁ ⊗ b₂) = ε(A)·ε(b₁)·B⁻_a b₂.
  set F₁ : SL ⊗[ℤ] SL →ₗ[ℤ] SL :=
    SymmetricAlgebra.algebraMapInv (M := LL) A •
      ((bMinusLin_SL a).comp ((LinearMap.mul' ℤ SL).comp
        (TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL))))
    with hF₁_def
  -- The "right" projection: F₂(b₁ ⊗ b₂) = ε(b₂)·B⁻_a(A○b₁).
  set F₂ : SL ⊗[ℤ] SL →ₗ[ℤ] SL :=
    (bMinusLin_SL a).comp
      ((oudomGuinCirc (R := ℤ) A).comp ((LinearMap.mul' ℤ SL).comp
        (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL))))
    with hF₂_def
  have h_lm :
      (bMinusLin_SL a).comp ((LinearMap.mul' ℤ SL).comp
          (TensorProduct.map (oudomGuinCirc (R := ℤ) A)
            (LinearMap.id : SL →ₗ[ℤ] SL))) = F₁ + F₂ := by
    apply TensorProduct.ext'
    intro b₁ b₂
    -- LHS at b₁⊗b₂: B⁻_a((A○b₁)·b₂) = ε(A○b₁)·B⁻_a b₂ + ε(b₂)·B⁻_a(A○b₁)
    --                              = ε(A)·ε(b₁)·B⁻_a b₂ + ε(b₂)·B⁻_a(A○b₁)
    -- F₁ at b₁⊗b₂: ε(A) • B⁻_a((η(ε b₁))·b₂) = ε(A)·ε(b₁)·B⁻_a b₂
    -- F₂ at b₁⊗b₂: B⁻_a(A ○ (b₁ · η(ε b₂))) = B⁻_a(A ○ (ε(b₂)·b₁)) = ε(b₂)·B⁻_a(A○b₁)
    show bMinusLin_SL a ((oudomGuinCirc (R := ℤ) A b₁) * b₂) =
        SymmetricAlgebra.algebraMapInv (M := LL) A •
          bMinusLin_SL a (algebraMap ℤ SL
            (SymmetricAlgebra.algebraMapInv (M := LL) b₁) * b₂) +
        bMinusLin_SL a (oudomGuinCirc (R := ℤ) A
          (b₁ * algebraMap ℤ SL (SymmetricAlgebra.algebraMapInv (M := LL) b₂)))
    -- LHS reduction by counit-Leibniz on B⁻_a + counit_circ.
    rw [bMinusLin_SL_mul_eps, counit_circ]
    -- F₁ reduction: ε(A) • B⁻_a((algMap r)·b₂) = ε(A) • (r • B⁻_a b₂).
    have hF₁_pt : bMinusLin_SL a (algebraMap ℤ SL
            (SymmetricAlgebra.algebraMapInv (M := LL) b₁) * b₂) =
          SymmetricAlgebra.algebraMapInv (M := LL) b₁ • bMinusLin_SL a b₂ := by
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul]
    rw [hF₁_pt]
    -- F₂ reduction: B⁻_a(A ○ (b₁·algMap r)) = B⁻_a(A ○ (r • b₁)) = r • B⁻_a(A ○ b₁).
    have hF₂_inner : b₁ * algebraMap ℤ SL
            (SymmetricAlgebra.algebraMapInv (M := LL) b₂) =
          SymmetricAlgebra.algebraMapInv (M := LL) b₂ • b₁ := by
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]; rfl
    rw [hF₂_inner, map_smul, map_smul]
    -- Goal: ε(A)·ε(b₁) • B⁻_a b₂ + ε(b₂) • B⁻_a(A○b₁) = ε(A) • ε(b₁) • B⁻_a b₂ + ε(b₂) • B⁻_a(A○b₁).
    rw [mul_smul]
  -- Apply at cmB.
  have h_at_B := LinearMap.congr_fun h_lm cmB
  simp only [LinearMap.comp_apply] at h_at_B
  -- Goal LHS = B⁻_a(A ★ B) ≡ B⁻_a(mul'(TP.map (○A) id (cmB))) (by oudomGuinStar_def
  -- + cmB defeq with Coalgebra.comul B).
  change bMinusLin_SL a ((LinearMap.mul' ℤ SL)
        ((TensorProduct.map (oudomGuinCirc (R := ℤ) A) LinearMap.id) cmB)) = _
  refine h_at_B.trans ?_
  show (F₁ + F₂) cmB = _
  rw [hF₁_def, hF₂_def]
  -- Now we have: F₁(cmB) + F₂(cmB) on LHS.
  -- Step A: F₁(cmB) = ε(A) • B⁻_a B (via rTensor counit triangle).
  have h_F₁_eval :
      SymmetricAlgebra.algebraMapInv (M := LL) A •
        ((bMinusLin_SL a).comp ((LinearMap.mul' ℤ SL).comp
          (TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL)))) cmB =
      SymmetricAlgebra.algebraMapInv (M := LL) A • bMinusLin_SL a B := by
    congr 1
    -- Reduce: B⁻_a(mul'(TP.map (η∘ε) id (cmB))) = B⁻_a B.
    have h_rTensor_at_cmB :
        (TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL)) cmB =
          (1 : SL) ⊗ₜ[ℤ] B := by
      rw [hcmB]
      show (TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL))
              (Coalgebra.comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B) = _
      rw [show TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL) =
              (TensorProduct.map η (LinearMap.id : SL →ₗ[ℤ] SL)).comp
                (TensorProduct.map εL (LinearMap.id : SL →ₗ[ℤ] SL)) from by
            rw [← TensorProduct.map_comp, LinearMap.id_comp]]
      rw [LinearMap.comp_apply]
      -- εL = Coalgebra.counit, and TP.map counit id = counit.rTensor.
      have h_εL_eq : (TensorProduct.map εL (LinearMap.id : SL →ₗ[ℤ] SL))
                       (Coalgebra.comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B) =
                     (1 : ℤ) ⊗ₜ[ℤ] B := by
        rw [hεL_def]
        exact Coalgebra.rTensor_counit_comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B
      rw [h_εL_eq, TensorProduct.map_tmul, hη_def]
      show (algebraMap ℤ SL 1 : SL) ⊗ₜ[ℤ] (LinearMap.id : SL →ₗ[ℤ] SL) B =
            (1 : SL) ⊗ₜ[ℤ] B
      rw [map_one]
      rfl
    simp only [LinearMap.comp_apply, h_rTensor_at_cmB, LinearMap.mul'_apply, one_mul]
  -- Step B: F₂(cmB) = B⁻_a(A ○ B) (via lTensor counit triangle).
  have h_F₂_eval :
      ((bMinusLin_SL a).comp
        ((oudomGuinCirc (R := ℤ) A).comp ((LinearMap.mul' ℤ SL).comp
          (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL))))) cmB =
        bMinusLin_SL a (oudomGuinCirc (R := ℤ) A B) := by
    have h_lTensor_at_cmB :
        (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL)) cmB =
          B ⊗ₜ[ℤ] (1 : SL) := by
      rw [hcmB]
      show (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL))
              (Coalgebra.comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B) = _
      rw [show TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL) =
              (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) η).comp
                (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) εL) from by
            rw [← TensorProduct.map_comp, LinearMap.id_comp]]
      rw [LinearMap.comp_apply]
      have h_εL_eq : (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) εL)
                       (Coalgebra.comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B) =
                     B ⊗ₜ[ℤ] (1 : ℤ) := by
        rw [hεL_def]
        exact Coalgebra.lTensor_counit_comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B
      rw [h_εL_eq, TensorProduct.map_tmul, hη_def]
      show (LinearMap.id : SL →ₗ[ℤ] SL) B ⊗ₜ[ℤ] (algebraMap ℤ SL 1 : SL) =
            B ⊗ₜ[ℤ] (1 : SL)
      rw [map_one]
      rfl
    -- Reduce: B⁻_a(○A(mul'(TP.map id (η∘ε) cmB))) = B⁻_a(○A(mul'(B⊗1))) = B⁻_a(○A(B·1)) = B⁻_a(○A B).
    rw [show ((bMinusLin_SL a).comp
          ((oudomGuinCirc (R := ℤ) A).comp ((LinearMap.mul' ℤ SL).comp
            (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL))))) cmB =
        bMinusLin_SL a (oudomGuinCirc (R := ℤ) A ((LinearMap.mul' ℤ SL)
          ((TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL)) cmB))) from rfl,
        h_lTensor_at_cmB, LinearMap.mul'_apply, mul_one]
  -- Substitute back.
  show (SymmetricAlgebra.algebraMapInv (M := LL) A •
          ((bMinusLin_SL a).comp ((LinearMap.mul' ℤ SL).comp
            (TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL))))) cmB +
        ((bMinusLin_SL a).comp
          ((oudomGuinCirc (R := ℤ) A).comp ((LinearMap.mul' ℤ SL).comp
            (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL))))) cmB =
        SymmetricAlgebra.algebraMapInv (M := LL) A • bMinusLin_SL a B +
        bMinusLin_SL a (oudomGuinCirc (R := ℤ) A B)
  rw [LinearMap.smul_apply, h_F₁_eval, h_F₂_eval]

/-! ### The cocycle identity -/

/-- The cocycle identity for `B⁻_a` with respect to `★`, from the proof of
    Prop 3.2 of [oudom-guin-2008]:

    `bMinusLin_SL a (A ★ B) = ε(A) • bMinusLin_SL a B + bMinusLin_SL a A ★ B`

    SL-side analog of the Connes-Kreimer-side `bMinusLin_gl_mul`. -/
theorem bMinusLin_SL_oudomGuinStar [DecidableEq (Nonplanar α)]
    (a : α) (A B : SL) :
    bMinusLin_SL a (oudomGuinStar A B) =
      SymmetricAlgebra.algebraMapInv (M := InsertionAlgebra α) A •
        bMinusLin_SL a B +
      oudomGuinStar (bMinusLin_SL a A) B := by
  induction A using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, oudomGuinStar_smul_left,
        oudomGuinStar_one_left]
    simp only [map_smul, map_one, bMinusLin_SL_one, smul_zero,
               oudomGuinStar_zero_left, add_zero, smul_eq_mul, mul_one]
  | ι x =>
    -- ε(ι x) = 0, so the RHS collapses; reduce the LHS via
    -- bMinusLin_SL_ι_star and psiA_L_circByT_total_eq.
    rw [SymmetricAlgebra.algebraMapInv_ι, zero_smul, zero_add,
        bMinusLin_SL_ι_star a x B, psiA_L_circByT_total_eq a x B,
        bMinusLin_SL_ι]
  | mul A₁ A₂ ih₁ ih₂ =>
    -- Key derived fact: B⁻_a(A_i ○ B) = (B⁻_a A_i) ★ B (from IH_i + star_eq).
    have hAi : ∀ Aᵢ : SL,
        (bMinusLin_SL a (oudomGuinStar Aᵢ B) =
          SymmetricAlgebra.algebraMapInv (M := InsertionAlgebra α) Aᵢ •
            bMinusLin_SL a B + oudomGuinStar (bMinusLin_SL a Aᵢ) B) →
        bMinusLin_SL a (oudomGuinCirc (R := ℤ) Aᵢ B) =
          oudomGuinStar (bMinusLin_SL a Aᵢ) B := by
      intro Aᵢ hCocycle
      -- B⁻_a(Aᵢ ★ B) = ε(Aᵢ)·B⁻_a B + B⁻_a(Aᵢ ○ B)         [star_eq]
      -- B⁻_a(Aᵢ ★ B) = ε(Aᵢ)·B⁻_a B + (B⁻_a Aᵢ) ★ B          [hCocycle]
      -- So B⁻_a(Aᵢ ○ B) = (B⁻_a Aᵢ) ★ B by add_left_cancel.
      have h_star_eq := bMinusLin_SL_star_eq a Aᵢ B
      rw [hCocycle] at h_star_eq
      exact (add_left_cancel h_star_eq).symm
    have h₁ : bMinusLin_SL a (oudomGuinCirc (R := ℤ) A₁ B) =
              oudomGuinStar (bMinusLin_SL a A₁) B := hAi A₁ ih₁
    have h₂ : bMinusLin_SL a (oudomGuinCirc (R := ℤ) A₂ B) =
              oudomGuinStar (bMinusLin_SL a A₂) B := hAi A₂ ih₂
    -- Step 1: rewrite LHS via star_eq.
    rw [bMinusLin_SL_star_eq]
    -- Goal: ε(A₁A₂)·B⁻_a B + B⁻_a((A₁A₂)○B) =
    --       ε(A₁A₂)·B⁻_a B + (B⁻_a(A₁A₂))★B
    congr 1
    -- Step 2: rewrite (A₁A₂)○B via Prop 2.7.iii.
    -- (A₁A₂)○B = mul'(TP.map (○A₁) (○A₂) (cm B)).
    -- Apply B⁻_a-counit-Leibniz pointwise + counit_circ + counit-comul triangles
    -- → B⁻_a((A₁A₂)○B) = ε(A₁)·B⁻_a(A₂○B) + ε(A₂)·B⁻_a(A₁○B).
    have h_circ_decomp :
        bMinusLin_SL a (oudomGuinCirc (R := ℤ) (A₁ * A₂) B) =
          SymmetricAlgebra.algebraMapInv (M := LL) A₁ •
            bMinusLin_SL a (oudomGuinCirc (R := ℤ) A₂ B) +
          SymmetricAlgebra.algebraMapInv (M := LL) A₂ •
            bMinusLin_SL a (oudomGuinCirc (R := ℤ) A₁ B) := by
      -- LinearMap equality on SL ⊗ SL applied to cm B, mirrors star_eq proof.
      letI inst_B : Bialgebra ℤ (SymmetricAlgebra ℤ LL) := SymmetricAlgebra.instBialgebra ℤ LL
      letI inst_Co : Coalgebra ℤ (SymmetricAlgebra ℤ LL) := inst_B.toCoalgebra
      letI inst_C : CoalgebraStruct ℤ (SymmetricAlgebra ℤ LL) := inst_Co.toCoalgebraStruct
      set cmB : SL ⊗[ℤ] SL :=
        (Bialgebra.comulAlgHom ℤ (SymmetricAlgebra ℤ LL)).toLinearMap B with hcmB
      set η : ℤ →ₗ[ℤ] SL := Algebra.linearMap ℤ SL with hη_def
      set εL : SL →ₗ[ℤ] ℤ :=
        (SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)).toLinearMap with hεL_def
      -- (A₁A₂) ○ B = mul'(TP.map (○A₁) (○A₂) (cm B)) by Prop 2.7.iii.
      -- B⁻_a applied: pointwise Leibniz → ε(A₁○B₁)·B⁻_a(A₂○B₂) + ε(A₂○B₂)·B⁻_a(A₁○B₁).
      -- Linear-map identity:
      --   B⁻_a ∘ mul' ∘ TP.map (○A₁) (○A₂) =
      --     ε(A₁) • B⁻_a ∘ ○A₂ ∘ mul' ∘ TP.map (η∘ε) id +
      --     ε(A₂) • B⁻_a ∘ ○A₁ ∘ mul' ∘ TP.map id (η∘ε)
      -- Wait: I want B⁻_a((A₁○B₁)·(A₂○B₂)) = ε(A₁)·ε(B₁)·B⁻_a(A₂○B₂) + ε(A₂)·ε(B₂)·B⁻_a(A₁○B₁).
      -- = ε(A₁) • (B⁻_a ∘ ○A₂ ∘ μ ∘ (TP.map η id ∘ TP.map ε id))(b₁ ⊗ b₂)  [where b₁⊗b₂ = cm B]
      --     -- Here ε(b₁) replaces b₁, then mul'(algMap ε(b₁) ⊗ b₂) = ε(b₁)·b₂, then ○A₂ acts.
      -- ALTERNATIVELY: apply star_eq directly to oudomGuinCirc... wait, star_eq is about ★, not ○.
      have h_lm :
          (bMinusLin_SL a).comp ((LinearMap.mul' ℤ SL).comp
              (TensorProduct.map (oudomGuinCirc (R := ℤ) A₁)
                (oudomGuinCirc (R := ℤ) A₂))) =
            (SymmetricAlgebra.algebraMapInv (M := LL) A₁ •
              ((bMinusLin_SL a).comp ((oudomGuinCirc (R := ℤ) A₂).comp
                ((LinearMap.mul' ℤ SL).comp
                  (TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL)))))) +
            (SymmetricAlgebra.algebraMapInv (M := LL) A₂ •
              ((bMinusLin_SL a).comp ((oudomGuinCirc (R := ℤ) A₁).comp
                ((LinearMap.mul' ℤ SL).comp
                  (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL)))))) := by
        apply TensorProduct.ext'
        intro b₁ b₂
        -- LHS at b₁⊗b₂: B⁻_a((A₁○b₁)·(A₂○b₂))
        --             = ε(A₁○b₁)·B⁻_a(A₂○b₂) + ε(A₂○b₂)·B⁻_a(A₁○b₁)    [Leibniz]
        --             = ε(A₁)·ε(b₁)·B⁻_a(A₂○b₂) + ε(A₂)·ε(b₂)·B⁻_a(A₁○b₁)
        -- RHS₁ at b₁⊗b₂: ε(A₁) • B⁻_a(A₂ ○ (algMap(ε(b₁)) · b₂)) = ε(A₁) • ε(b₁) • B⁻_a(A₂ ○ b₂)
        -- RHS₂ at b₁⊗b₂: ε(A₂) • B⁻_a(A₁ ○ (b₁ · algMap(ε(b₂)))) = ε(A₂) • ε(b₂) • B⁻_a(A₁ ○ b₁)
        show bMinusLin_SL a ((oudomGuinCirc (R := ℤ) A₁ b₁) *
              (oudomGuinCirc (R := ℤ) A₂ b₂)) = _
        rw [bMinusLin_SL_mul_eps, counit_circ, counit_circ]
        -- LHS: ε(A₁)·ε(b₁)·B⁻_a(A₂○b₂) + ε(A₂)·ε(b₂)·B⁻_a(A₁○b₁)
        show (SymmetricAlgebra.algebraMapInv (M := LL) A₁ *
              SymmetricAlgebra.algebraMapInv (M := LL) b₁) •
              bMinusLin_SL a (oudomGuinCirc (R := ℤ) A₂ b₂) +
            (SymmetricAlgebra.algebraMapInv (M := LL) A₂ *
              SymmetricAlgebra.algebraMapInv (M := LL) b₂) •
              bMinusLin_SL a (oudomGuinCirc (R := ℤ) A₁ b₁) =
          SymmetricAlgebra.algebraMapInv (M := LL) A₁ •
            bMinusLin_SL a (oudomGuinCirc (R := ℤ) A₂
              ((LinearMap.mul' ℤ SL)
                (algebraMap ℤ SL (SymmetricAlgebra.algebraMapInv (M := LL) b₁) ⊗ₜ[ℤ] b₂))) +
          SymmetricAlgebra.algebraMapInv (M := LL) A₂ •
            bMinusLin_SL a (oudomGuinCirc (R := ℤ) A₁
              ((LinearMap.mul' ℤ SL)
                (b₁ ⊗ₜ[ℤ] algebraMap ℤ SL (SymmetricAlgebra.algebraMapInv (M := LL) b₂))))
        rw [LinearMap.mul'_apply, LinearMap.mul'_apply]
        rw [show algebraMap ℤ SL (SymmetricAlgebra.algebraMapInv (M := LL) b₁) * b₂ =
              SymmetricAlgebra.algebraMapInv (M := LL) b₁ • b₂ from by
            rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]; rfl]
        rw [show b₁ * algebraMap ℤ SL (SymmetricAlgebra.algebraMapInv (M := LL) b₂) =
              SymmetricAlgebra.algebraMapInv (M := LL) b₂ • b₁ from by
            rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]; rfl]
        rw [map_smul, map_smul, map_smul, map_smul, mul_smul, mul_smul]
      -- Apply at cmB.
      have h_at_B := LinearMap.congr_fun h_lm cmB
      simp only [LinearMap.comp_apply] at h_at_B
      -- LHS of h_at_B: B⁻_a(mul'(TP.map (○A₁) (○A₂) cmB)) = B⁻_a((A₁A₂)○B).
      -- by `circ_mul_distrib_via_comul` (Prop 2.7.iii).
      have h_LHS_eq :
          bMinusLin_SL a (oudomGuinCirc (R := ℤ) (A₁ * A₂) B) =
            bMinusLin_SL a ((LinearMap.mul' ℤ SL)
              ((TensorProduct.map (oudomGuinCirc (R := ℤ) A₁)
                (oudomGuinCirc (R := ℤ) A₂)) cmB)) := by
        congr 1
        rw [circ_mul_distrib_via_comul, hcmB]
        rfl
      rw [h_LHS_eq]
      refine h_at_B.trans ?_
      -- Now: RHS₁ = ε(A₁) • B⁻_a(A₂○(mul'(TP.map (η∘ε) id cmB))) = ε(A₁) • B⁻_a(A₂○B)
      --   via rTensor counit triangle (mul'(1⊗B) = B).
      -- And RHS₂ = ε(A₂) • B⁻_a(A₁○(mul'(TP.map id (η∘ε) cmB))) = ε(A₂) • B⁻_a(A₁○B)
      --   via lTensor counit triangle (mul'(B⊗1) = B).
      have h_rT : (LinearMap.mul' ℤ SL)
              ((TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL)) cmB) = B := by
        have h_rTensor_at_cmB :
            (TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL)) cmB =
              (1 : SL) ⊗ₜ[ℤ] B := by
          rw [hcmB]
          show (TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL))
                  (Coalgebra.comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B) = _
          rw [show TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL) =
                  (TensorProduct.map η (LinearMap.id : SL →ₗ[ℤ] SL)).comp
                    (TensorProduct.map εL (LinearMap.id : SL →ₗ[ℤ] SL)) from by
                rw [← TensorProduct.map_comp, LinearMap.id_comp]]
          rw [LinearMap.comp_apply]
          have h_εL_eq : (TensorProduct.map εL (LinearMap.id : SL →ₗ[ℤ] SL))
                          (Coalgebra.comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B) =
                         (1 : ℤ) ⊗ₜ[ℤ] B := by
            rw [hεL_def]
            exact Coalgebra.rTensor_counit_comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B
          rw [h_εL_eq, TensorProduct.map_tmul, hη_def]
          show (algebraMap ℤ SL 1 : SL) ⊗ₜ[ℤ] (LinearMap.id : SL →ₗ[ℤ] SL) B =
                (1 : SL) ⊗ₜ[ℤ] B
          rw [map_one]
          rfl
        rw [h_rTensor_at_cmB, LinearMap.mul'_apply, one_mul]
      have h_lT : (LinearMap.mul' ℤ SL)
              ((TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL)) cmB) = B := by
        have h_lTensor_at_cmB :
            (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL)) cmB =
              B ⊗ₜ[ℤ] (1 : SL) := by
          rw [hcmB]
          show (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL))
                  (Coalgebra.comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B) = _
          rw [show TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL) =
                  (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) η).comp
                    (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) εL) from by
                rw [← TensorProduct.map_comp, LinearMap.id_comp]]
          rw [LinearMap.comp_apply]
          have h_εL_eq : (TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) εL)
                          (Coalgebra.comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B) =
                         B ⊗ₜ[ℤ] (1 : ℤ) := by
            rw [hεL_def]
            exact Coalgebra.lTensor_counit_comul (R := ℤ) (A := SymmetricAlgebra ℤ LL) B
          rw [h_εL_eq, TensorProduct.map_tmul, hη_def]
          show (LinearMap.id : SL →ₗ[ℤ] SL) B ⊗ₜ[ℤ] (algebraMap ℤ SL 1 : SL) =
                B ⊗ₜ[ℤ] (1 : SL)
          rw [map_one]
          rfl
        rw [h_lTensor_at_cmB, LinearMap.mul'_apply, mul_one]
      -- Unfold the LinearMap-composition form and substitute h_rT/h_lT.
      show SymmetricAlgebra.algebraMapInv (M := LL) A₁ •
            bMinusLin_SL a (oudomGuinCirc (R := ℤ) A₂
              ((LinearMap.mul' ℤ SL)
                ((TensorProduct.map (η.comp εL) (LinearMap.id : SL →ₗ[ℤ] SL)) cmB))) +
          SymmetricAlgebra.algebraMapInv (M := LL) A₂ •
            bMinusLin_SL a (oudomGuinCirc (R := ℤ) A₁
              ((LinearMap.mul' ℤ SL)
                ((TensorProduct.map (LinearMap.id : SL →ₗ[ℤ] SL) (η.comp εL)) cmB))) = _
      rw [h_rT, h_lT]
    rw [h_circ_decomp, h₁, h₂]
    -- Goal: ε(A₁)·(B⁻_a A₂)★B + ε(A₂)·(B⁻_a A₁)★B =
    --       (B⁻_a(A₁A₂))★B
    -- = (ε(A₁)·B⁻_a A₂ + ε(A₂)·B⁻_a A₁)★B
    -- = ε(A₁)·(B⁻_a A₂)★B + ε(A₂)·(B⁻_a A₁)★B
    rw [bMinusLin_SL_mul_eps, oudomGuinStar_add_left]
    -- Goal: ε(A₁) • ((B⁻_a A₂) ★ B) + ε(A₂) • ((B⁻_a A₁) ★ B) =
    --       (ε(A₁) • B⁻_a A₂) ★ B + (ε(A₂) • B⁻_a A₁) ★ B
    rw [show ((SymmetricAlgebra.algebraMapInv (M := LL) A₁ • bMinusLin_SL a A₂) :
              SL) ★ B =
          SymmetricAlgebra.algebraMapInv (M := LL) A₁ • (bMinusLin_SL a A₂ ★ B) from
            oudomGuinStar_smul_left _ _ _,
        show ((SymmetricAlgebra.algebraMapInv (M := LL) A₂ • bMinusLin_SL a A₁) :
              SL) ★ B =
          SymmetricAlgebra.algebraMapInv (M := LL) A₂ • (bMinusLin_SL a A₁ ★ B) from
            oudomGuinStar_smul_left _ _ _]
  | add A₁ A₂ ih₁ ih₂ =>
    rw [oudomGuinStar_add_left, map_add, map_add, map_add,
        oudomGuinStar_add_left, ih₁, ih₂, add_smul]
    abel

end SymAlg

end RootedTree
