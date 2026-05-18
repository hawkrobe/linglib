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

set_option autoImplicit false

/-!
# B⁻ operator on `SymmetricAlgebra ℤ (InsertionAlgebra α)`
@cite{oudom-guin-2008}

The SL-side analog of `bMinusLin` (defined on the CK side in `BMinus.lean`).
On a single `ι(ofTree t)` basis element of `SL = SymmetricAlgebra ℤ
(InsertionAlgebra α)`:

```
bMinusLin_SL a (ι(ofTree t)) =
  if rootLabel t = a then
    ∏ c ∈ rootChildren t, ι(ofTree c)
  else 0
```

and vanishes on length-0 (scalars) and length-≥2 (products of two or more
ι's) elements of `SL`. This is the SL-side `B⁻_a` operator from Oudom-Guin
paper §3 (page 10).

## Headline result (downstream)

The cocycle identity `B⁻_a(A ★ B) = ε(A) • B⁻_a(B) + B⁻_a(A) ★ B`
(OG Prop 3.2) — to be proved in a sibling file (Piece C of the
option-(ii) plan). This file provides the operator (Piece A) and the
ckIso-transport identity (Piece B).

## Construction (TA-descent recipe)

Mirrors `OudomGuinCircConstruct.circByT_total` (`OudomGuinCircTotal.lean:518`):

1. `psiA_basis a : Nonplanar α → SL` — per-tree assignment (children-prod or 0)
2. `psiA_L a : LL →ₗ[ℤ] SL` — linear extension via `Finsupp.linearCombination`
3. `psiA_multi a n : MultilinearMap (Fin n → LL) SL` — vanishes outside n=1
4. `psiA_pi a n : ⨂[ℤ]^n LL →ₗ[ℤ] SL` via `PiTensorProduct.lift`
5. `psiA_graded a : (⨁ n, ⨂[ℤ]^n LL) →ₗ[ℤ] SL` via `DirectSum.toModule`
6. `psiA_tensor a : TA LL →ₗ[ℤ] SL` via `TensorAlgebra.equivDirectSum`
7. Kernel vanishing: `algHomL.ker ≤ psiA_tensor.ker` — trivial because
   psiA_tensor is 0 on grade ≥ 2, so any `r · (ιX·ιY) · d` (grade ≥ 2)
   maps to 0 regardless of X, Y order
8. Descend via `Submodule.liftQ` + `LinearMap.quotKerEquivOfSurjective`

`[UPSTREAM]` candidate (joint with the sibling Prop-3.2 file).
-/

namespace RootedTree

namespace SymAlg

open TensorProduct
open scoped DirectSum
open PreLie.OudomGuinCirc

/-! ## §1: Per-tree basis assignment

For each color `a : α` and tree `t : Nonplanar α`, define the "children
as SL-product if a-rooted, else 0" assignment at the basis level. -/

variable {α : Type}

/-- Local abbreviations for readability. Use `LL` (not `L`) for
    `InsertionAlgebra α` to avoid clashing with the named argument
    `(LL := ...)` in `algHomL`. -/
local notation "LL" => InsertionAlgebra α
local notation "SL" => SymmetricAlgebra ℤ LL

/-- The `ι(ofTree)` map `Nonplanar α → SL`: embed a single tree into SL
    via the InsertionAlgebra's basis embedding `ofTree`, then via SL's
    canonical `ι`. -/
noncomputable def ιTree (t : Nonplanar α) : SL :=
  SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree t)

/-- The per-tree basis assignment for `B⁻_a`. On `t : Nonplanar α`:
    returns the SL-product of `ι(ofTree c)` over each child
    `c ∈ rootChildren t` if `rootLabel t = a`, else 0.

    Local `Classical.dec` provides decidability for `rootLabel t = a`. -/
noncomputable def psiA_basis (a : α) (t : Nonplanar α) : SL :=
  letI : Decidable (Nonplanar.rootLabel t = a) := Classical.dec _
  if Nonplanar.rootLabel t = a then
    ((Nonplanar.rootChildren t).map (fun c => ιTree c)).prod
  else 0

/-! ## §2: Linearize over `L = Nonplanar α →₀ ℤ` -/

/-- The `psiA` operator on `L`: linear extension of `psiA_basis` via
    `Finsupp.lift`. -/
noncomputable def psiA_L (a : α) : LL →ₗ[ℤ] SL :=
  Finsupp.lift SL ℤ (Nonplanar α) (psiA_basis a)

@[simp] theorem psiA_L_ofTree (a : α) (t : Nonplanar α) :
    psiA_L a (InsertionAlgebra.ofTree t) = psiA_basis a t := by
  show Finsupp.lift SL ℤ (Nonplanar α) _ (Finsupp.single t 1) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp

/-! ## §3: Per-degree multilinear maps

Length-graded structure: `psiA_multi a n` is the `Fin n → LL` multilinear
map that vanishes on `n ≠ 1` and applies `psiA_L a` to the single
argument when `n = 1`. -/

/-- The `n = 1` multilinear case: apply `psiA_L` to the single argument.

    Multilinearity is trivial since `Fin 1` has only one index, and
    `psiA_L` is already linear in that argument. -/
private noncomputable def psiA_multi_one (a : α) :
    MultilinearMap ℤ (fun _ : Fin 1 ↦ LL) SL :=
  MultilinearMap.mk' (fun f => psiA_L a (f 0))
    (fun m i x y => by
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst hi
      simp only [Function.update_self]
      exact (psiA_L a).map_add x y)
    (fun m i c x => by
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst hi
      simp only [Function.update_self]
      exact (psiA_L a).map_smul c x)

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

/-! ## §4: Per-degree lift to `⨂[ℤ]^n L` via `PiTensorProduct.lift` -/

/-- Per-degree lift of `psiA_multi a n` to `⨂[ℤ]^n L`. Mirrors
    `OudomGuinCircConstruct.circTPi`. -/
noncomputable def psiA_pi (a : α) (n : ℕ) : (⨂[ℤ]^n LL) →ₗ[ℤ] SL :=
  PiTensorProduct.lift (psiA_multi a n)

@[simp] theorem psiA_pi_tprod (a : α) (n : ℕ) (g : Fin n → LL) :
    psiA_pi a n (PiTensorProduct.tprod ℤ g) = psiA_multi a n g := by
  rw [psiA_pi, PiTensorProduct.lift.tprod]

/-! ## §5: Assembly across degrees via `DirectSum.toModule` -/

/-- Assembly of all `psiA_pi a n` into a linear map from the direct sum
    of all tensor powers. Mirrors `OudomGuinCircConstruct.circTGraded`. -/
noncomputable def psiA_graded (a : α) :
    (⨁ n : ℕ, ⨂[ℤ]^n LL) →ₗ[ℤ] SL :=
  DirectSum.toModule ℤ ℕ SL (fun n => psiA_pi a n)

@[simp] theorem psiA_graded_of (a : α) (n : ℕ) (x : ⨂[ℤ]^n LL) :
    psiA_graded a (DirectSum.of (fun n : ℕ => ⨂[ℤ]^n LL) n x) =
      psiA_pi a n x := by
  unfold psiA_graded
  show DirectSum.toModule ℤ ℕ SL (fun n => psiA_pi a n)
        (DirectSum.lof ℤ ℕ _ n x) = _
  exact DirectSum.toModule_lof (R := ℤ) (ι := ℕ) (M := fun n => ⨂[ℤ]^n LL)
    (N := SL) (φ := fun n => psiA_pi a n) n x

/-! ## §6: Composition with `TensorAlgebra.equivDirectSum` -/

/-- The TA-side `psiA` operator, assembled from per-degree `psiA_pi` via
    mathlib's `TensorAlgebra ≃ₐ ⨁_n ⨂[ℤ]^n LL`. Mirrors
    `OudomGuinCircConstruct.circTTensor`. -/
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

/-! ## §7: Kernel vanishing

`psiA_tensor a` vanishes on `ker algHomL`. Easier than `circTTensor`'s
kernel-vanishing because psiA_tensor is 0 on every tprod of degree ≥ 2:
any wrapped `r * (ι X * ι Y) * d` element has degree ≥ 2 (the X·Y factor
alone contributes 2), so both swap-orderings map to 0. -/

open PreLie.OudomGuinCircConstruct in
/-- Inlined helper: `(tprod_m a) * (ι X * ι Y) * (tprod_n b)` equals
    a single tprod of grade `m + 2 + n`. Mirrors the private
    `tprod_mul_ι_pair_mul_tprod` in `OudomGuinCircTotal.lean`. -/
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

/-- Helper: for any `k ≥ 2`, `psiA_multi a k` is the zero map. -/
private lemma psiA_multi_eq_zero_of_ge_two (a : α) {k : ℕ} (hk : k ≥ 2) :
    psiA_multi a k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  exact psiA_multi_succ_succ a j

/-- `psiA_tensor` vanishes on any `r * (ι X * ι Y) * d` regardless of X, Y
    order, because the result is grade ≥ 2 and `psiA_multi a n = 0` for
    `n ≥ 2`. -/
private lemma psiA_tensor_grade_ge_two_vanish (a : α)
    {m n : ℕ} (r' : Fin m → InsertionAlgebra α)
    (d' : Fin n → InsertionAlgebra α) (X Y : InsertionAlgebra α) :
    psiA_tensor a
        ((TensorAlgebra.tprod ℤ (InsertionAlgebra α) m r') *
          (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y) *
          (TensorAlgebra.tprod ℤ (InsertionAlgebra α) n d')) = 0 := by
  rw [tprod_mul_ι_pair_mul_tprod_inline, psiA_tensor_tprod]
  -- psiA_multi a (m + 2 + n) is the zero map since m + 2 + n ≥ 2.
  rw [psiA_multi_eq_zero_of_ge_two a (by omega : m + 2 + n ≥ 2)]
  rfl

open PreLie.OudomGuinCircConstruct in
/-- Swap-respect for `psiA_tensor` (bilinear-extension version): for any
    `r d : TA LL` and `X Y : LL`, the swap of X, Y inside `r * (ι X · ι Y) * d`
    leaves `psiA_tensor a` invariant. Trivial since both sides are 0. -/
private lemma psiA_tensor_swap_general (a : α) (X Y : LL) (r d : TensorAlgebra ℤ LL) :
    psiA_tensor a (r * (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y) * d) =
    psiA_tensor a (r * (TensorAlgebra.ι ℤ Y * TensorAlgebra.ι ℤ X) * d) := by
  -- Extend over r and d bilinearly.
  -- For each pair (r, d) of tprods, both sides reduce to
  -- psiA_tensor (tprod (concat)) = 0 by grade-vanishing.
  suffices h_fixed_d : ∀ d' : TensorAlgebra ℤ LL,
      (psiA_tensor a).comp ((LinearMap.mulRight ℤ d').comp
        (LinearMap.mulRight ℤ (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y))) =
      (psiA_tensor a).comp ((LinearMap.mulRight ℤ d').comp
        (LinearMap.mulRight ℤ (TensorAlgebra.ι ℤ Y * TensorAlgebra.ι ℤ X))) by
    have := congrArg (fun f : TensorAlgebra ℤ LL →ₗ[ℤ] SL => f r) (h_fixed_d d)
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at this
    exact this
  intro d'
  apply TA_linearMap_ext_tprod
  intro m r'
  -- Goal: f (tprod m r') = g (tprod m r') with f, g compositions of psiA_tensor + mulRight.
  show psiA_tensor a (TensorAlgebra.tprod ℤ LL m r' *
        (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y) * d') =
      psiA_tensor a (TensorAlgebra.tprod ℤ LL m r' *
        (TensorAlgebra.ι ℤ Y * TensorAlgebra.ι ℤ X) * d')
  -- Both sides will become wrappings of grade ≥ 2 around different orderings;
  -- both reduce to 0 by psiA_tensor_grade_ge_two_vanish. But the d' side is
  -- not yet a tprod, so extend over d' too.
  suffices h_at_tprod_r : ∀ d'' : TensorAlgebra ℤ LL,
      psiA_tensor a (TensorAlgebra.tprod ℤ LL m r' *
          (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y) * d'') =
      psiA_tensor a (TensorAlgebra.tprod ℤ LL m r' *
          (TensorAlgebra.ι ℤ Y * TensorAlgebra.ι ℤ X) * d'') by
    exact h_at_tprod_r d'
  intro d''
  -- Extend over d'' via TA_linearMap_ext_tprod.
  suffices h_eq : (psiA_tensor a).comp
      ((LinearMap.mulLeft ℤ (TensorAlgebra.tprod ℤ LL m r' *
          (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y)))) =
    (psiA_tensor a).comp
      ((LinearMap.mulLeft ℤ (TensorAlgebra.tprod ℤ LL m r' *
          (TensorAlgebra.ι ℤ Y * TensorAlgebra.ι ℤ X)))) by
    have := congrArg (fun f : TensorAlgebra ℤ LL →ₗ[ℤ] SL => f d'') h_eq
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at this
    exact this
  apply TA_linearMap_ext_tprod
  intro n d_tprod
  show psiA_tensor a (TensorAlgebra.tprod ℤ LL m r' *
        (TensorAlgebra.ι ℤ X * TensorAlgebra.ι ℤ Y) *
        TensorAlgebra.tprod ℤ LL n d_tprod) =
      psiA_tensor a (TensorAlgebra.tprod ℤ LL m r' *
        (TensorAlgebra.ι ℤ Y * TensorAlgebra.ι ℤ X) *
        TensorAlgebra.tprod ℤ LL n d_tprod)
  rw [psiA_tensor_grade_ge_two_vanish a r' d_tprod X Y,
      psiA_tensor_grade_ge_two_vanish a r' d_tprod Y X]

/-- `psiA_tensor a` respects `Rel SymRel` (after wrapping). Same induction
    pattern as `circTTensor_resp_Rel_strong`. -/
private lemma psiA_tensor_resp_Rel_strong (a : α) :
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

private lemma psiA_tensor_resp_Rel (a : α) {z₁ z₂ : TensorAlgebra ℤ LL}
    (h : RingQuot.Rel (TensorAlgebra.SymRel ℤ LL) z₁ z₂) :
    psiA_tensor a z₁ = psiA_tensor a z₂ := by
  have := psiA_tensor_resp_Rel_strong a h 1 1
  simpa using this

private lemma psiA_tensor_resp_EqvGen (a : α) {z₁ z₂ : TensorAlgebra ℤ LL}
    (h : Relation.EqvGen (RingQuot.Rel (TensorAlgebra.SymRel ℤ LL)) z₁ z₂) :
    psiA_tensor a z₁ = psiA_tensor a z₂ := by
  induction h with
  | rel _ _ h => exact psiA_tensor_resp_Rel a h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

open PreLie.OudomGuinCircConstruct in
/-- `psiA_tensor a` vanishes on `ker algHomL`. Mirror of
    `circTTensor_vanishes_on_ker`. -/
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

/-! ## §8: Descent to `SymmetricAlgebra` via `Submodule.liftQ` -/

open PreLie.OudomGuinCircConstruct in
/-- **The SL-side B⁻ operator** `B⁻_a : SL →ₗ[ℤ] SL`. Built via
    `Submodule.liftQ` from `psiA_tensor a` + the kernel-vanishing lemma,
    composed with the surjective-algHom-induced equivalence
    `SL ≃ TA / ker algHomL`. Mirrors `circByT_total`. -/
noncomputable def bMinusLin_SL (a : α) : SL →ₗ[ℤ] SL :=
  (Submodule.liftQ _ (psiA_tensor a) (psiA_tensor_vanishes_on_ker a)).comp
    (LinearMap.quotKerEquivOfSurjective algHomL algHomL_surjective).symm.toLinearMap

/-! ## §9: Basic identities

`bMinusLin_SL a` factors through `algHomL`: for any `z : TA L`, applying
`bMinusLin_SL a` after `algHomL` equals applying `psiA_tensor a` directly.
This is the key lemma for computing `bMinusLin_SL` on specific elements
(by lifting them through `algHomL`). -/

open PreLie.OudomGuinCircConstruct in
/-- **Factorization through algHomL**: `bMinusLin_SL a (algHomL z) =
    psiA_tensor a z` for all `z : TA L`. -/
theorem bMinusLin_SL_algHomL (a : α) (z : TensorAlgebra ℤ LL) :
    bMinusLin_SL a (algHomL z) = psiA_tensor a z := by
  -- bMinusLin_SL = (liftQ ...).comp quotKerEquivOfSurjective.symm.
  -- Strategy: compute (quotKerEquivOfSurjective).symm (algHomL z) = Submodule.Quotient.mk z,
  -- then apply Submodule.liftQ_apply.
  unfold bMinusLin_SL
  rw [LinearMap.comp_apply]
  -- Convert symm.toLinearMap to symm-apply form.
  show (Submodule.liftQ (LinearMap.ker (algHomL (R := ℤ) (L := InsertionAlgebra α)))
        (psiA_tensor a) (psiA_tensor_vanishes_on_ker a))
      ((LinearMap.quotKerEquivOfSurjective algHomL algHomL_surjective).symm
        (algHomL z)) = _
  -- Establish: (.symm) (algHomL z) = mk z. Use that quotKerEquivOfSurjective sends
  -- mk z to algHomL z (by quotKerEquivOfSurjective_apply_mk or similar).
  have h_eq : (LinearMap.quotKerEquivOfSurjective
        (algHomL (R := ℤ) (L := InsertionAlgebra α)) algHomL_surjective).symm
        (algHomL z) =
      (Submodule.Quotient.mk z : TensorAlgebra ℤ LL ⧸
        LinearMap.ker (algHomL (R := ℤ) (L := InsertionAlgebra α))) := by
    apply (LinearMap.quotKerEquivOfSurjective
      (algHomL (R := ℤ) (L := InsertionAlgebra α)) algHomL_surjective).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [h_eq]
  exact Submodule.liftQ_apply _ (psiA_tensor a) _

/-- **B⁻_a applied to ι(x)**: equals `psiA_L a x`. -/
theorem bMinusLin_SL_ι (a : α) (x : InsertionAlgebra α) :
    bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL x) = psiA_L a x := by
  -- SymmetricAlgebra.ι R L = algHom R L ∘ₗ TensorAlgebra.ι R (by definition).
  have h_factor : SymmetricAlgebra.ι ℤ LL x =
      PreLie.OudomGuinCircConstruct.algHomL (TensorAlgebra.ι ℤ x) := rfl
  rw [h_factor, bMinusLin_SL_algHomL]
  -- Now: psiA_tensor a (TA.ι ℤ x) = psiA_L a x.
  -- TA.ι ℤ x = tprod 1 (fun _ => x); psiA_tensor on tprod 1 = psiA_multi a 1.
  rw [PreLie.OudomGuinCircConstruct.ι_eq_tprod_one, psiA_tensor_tprod]
  rfl

/-- **B⁻_a applied to ιTree t**: equals `psiA_basis a t`. -/
theorem bMinusLin_SL_ιTree (a : α) (t : Nonplanar α) :
    bMinusLin_SL a (ιTree t) = psiA_basis a t := by
  show bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree t)) = _
  rw [bMinusLin_SL_ι, psiA_L_ofTree]

/-- **B⁻_a applied to 1**: equals 0 (scalars have length 0; B⁻ vanishes). -/
@[simp] theorem bMinusLin_SL_one (a : α) :
    bMinusLin_SL a (1 : SL) = 0 := by
  -- 1 = algHomL 1 (algHom preserves 1).
  have h_one : (1 : SL) = PreLie.OudomGuinCircConstruct.algHomL (1 : TensorAlgebra ℤ LL) := by
    show (1 : SL) = (SymmetricAlgebra.algHom ℤ LL).toLinearMap 1
    show (1 : SL) = SymmetricAlgebra.algHom ℤ LL 1
    rw [map_one]
  rw [h_one, bMinusLin_SL_algHomL]
  -- psiA_tensor a 1 = psiA_tensor a (tprod 0 _) — but 1 isn't directly a tprod 0.
  -- Easier route: 1 = algebraMap ℤ 1; psiA_tensor on algebraMap... actually use
  -- the TA grade structure: 1 = TA.tprod 0 (the empty function).
  have h_one_tprod : (1 : TensorAlgebra ℤ LL) =
      TensorAlgebra.tprod ℤ LL 0 Fin.elim0 := by
    rw [TensorAlgebra.tprod_apply]
    simp [List.ofFn_zero]
  rw [h_one_tprod, psiA_tensor_tprod, psiA_multi_zero]
  rfl

/-! ## §10: ckIso transport for `bMinusLin_SL`

The transport identity `bMinusLin a (ckIso X) = ckIso (bMinusLin_SL a X)`
for all X ∈ SL. The substantial work is the per-tprod-n induction over TA;
the n ≥ 2 case uses CK ε-Leibniz (a symmetric ε-twisted Leibniz rule for
the disjoint-union product on CK), which is proved separately. -/

open ConnesKreimer (counit counit_of' of'_add)
open GrossmanLarson (of' bMinusBasis bMinusBasis_zero bMinusBasis_singleton_node
  bMinusBasis_eq_zero_of_not_singleton_a bMinusLin bMinusLin_of')

/-! ### §10a: CK ε-Leibniz at basis level

`bMinusBasis a (F + G)` splits according to which of `F`, `G` is empty:
- F = ∅: equals bMinusBasis a G
- G = ∅: equals bMinusBasis a F
- Both nonempty: equals 0 (F+G has card ≥ 2, not a singleton). -/

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

/-! ### §10b: CK ε-Leibniz at basis-of'-of' level -/

/-- CK ε-Leibniz on basis: for `of'(F) * of'(G) = of'(F + G)` (CK product),
    the bMinusLin splits according to which side is empty.

    Uses `ConnesKreimer.of'` (NOT `GrossmanLarson.of'`) and CK's `*`
    (disjoint-union product, NOT GL's `productForest`). -/
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
  by_cases hF : F.card = 0
  · by_cases hG : G.card = 0
    · simp [hF, hG]
    · simp [hF, hG]
  · by_cases hG : G.card = 0
    · simp [hF, hG]
    · simp [hF, hG]

/-! ### §10c: Main transport identity (partial — see TODO)

`bMinusLin a (ckIso X) = ckIso (bMinusLin_SL a X)` for all `X ∈ SL`.

**Status (2026-05-18)**: stated with `sorry`. Closure requires:

1. **Full CK ε-Leibniz** (bilinear extension of `bMinusLin_of'_mul_of'`):
   for general `X, Y : ConnesKreimer ℤ (Nonplanar α)`,
   `bMinusLin a (X * Y) = counit X • bMinusLin a Y + counit Y • bMinusLin a X`.
   Estimated 50-80 LOC via `Finsupp.induction_linear` on Y, then X.
   Subtlety: type-alias discipline between `ConnesKreimer ℤ (Nonplanar α)`
   and `Forest (Nonplanar α) →₀ ℤ`; explicit `show` casts needed.

2. **TA-side per-tprod-n induction**: via `algHomL_surjective` +
   `TA_linearMap_ext_tprod` + induction on `n`. For `n = 0` and `n = 1`
   direct; for `n ≥ 2`, CK ε-Leibniz reduces to `0 = 0` because both
   factor counits vanish (`ε(ckIso(SL.ι _)) = ε(SL.ι _) = 0` via
   `SymmetricAlgebra.algebraMapInv_ι`).

   Estimated 80-120 LOC.

Total for closure: ~150-200 LOC additional. Targeted for the next session
on this Piece. -/

/-- **TODO**: The transport identity (Piece B). See header comment for
    closure plan. -/
theorem bMinusLin_ckIso [DecidableEq (Nonplanar α)] (a : α) (X : SL) :
    bMinusLin (R := ℤ) a (ckIsoSymmetricAlgebra X) =
    ckIsoSymmetricAlgebra (bMinusLin_SL a X) := by
  sorry

/-! ## §11: Piece D — tree decomposition `ι(node a A') = ι(•_a) ○ (∏ ι child)`

OG paper §3 Prop 3.1 (page 9): for the free pre-Lie algebra of rooted
trees `PL(X)`, the universal property gives the identity

```
• ∘ T₁ ... T_n  =  [tree with root • and children T₁, ..., T_n]
```

In our setup (`InsertionAlgebra α` is the free pre-Lie algebra on `α`,
generated by `ofTree (leaf a)` for a ∈ α), this lifts via `circ_ι_ι` and
the Multiset.induction on A' (the children-multiset).

Used in Piece C (OG Prop 3.2 proof) to write an arbitrary single tree
in the canonical `singleton ○ children` form. -/

/-- Helper: `leaf a = node a 0` in `Nonplanar α`. The singleton-vertex
    tree is the empty-children node. -/
theorem leaf_eq_node_zero (a : α) :
    (Nonplanar.leaf a : Nonplanar α) = Nonplanar.node a 0 := by
  show Nonplanar.mk (Planar.leaf a) =
    Nonplanar.node a (Multiset.ofList [])
  show Nonplanar.mk (Planar.node a []) = Nonplanar.node a (Multiset.ofList [])
  -- node a (↑[]) = mk (.node a ([].map Quotient.out)) = mk (.node a [])
  show Nonplanar.mk (Planar.node a []) =
    Nonplanar.mk (Planar.node a (([] : List (Nonplanar α)).map Quotient.out))
  rfl

/-- **Piece D**: every nonplanar tree is the OG circ-product of its
    singleton-vertex root with its children-forest.

    `ι(ofTree (node a A')) = ι(ofTree (leaf a)) ○ (∏ c ∈ A', ι(ofTree c))`

    **Status**: base case proved, cons case `sorry`. Closure via
    `Multiset.induction` on `A'`:
    - **Base case** `A' = 0`: `node a 0 = leaf a`. `Multiset.prod 0 = 1`.
      `circ_one_right` closes. ✓ (proved here)
    - **Cons case** `A' = c ::ₘ A''`: apply `circ_T_mul` (Prop 2.7.ii)
      after commuting `ι(c) * Q` to `Q * ι(c)` via `mul_comm`. The
      "first term" `(ι(leaf a) ○ Q) ○ ι(c)` reduces via IH + `circ_ι_ι`
      to `ι((node a A'') • c)`, which equals the desired
      `node a (c ::ₘ A'')` plus subtree-graft summands. The "second
      term" `ι(leaf a) ○ (Q ○ ι(c))` contains exactly the subtree-graft
      cancellation.

    Estimated cons-case LOC: ~150-200 + helpers for L-side pre-Lie
    grafting. -/
theorem iotaTree_node_via_circ (a : α) (A' : Multiset (Nonplanar α)) :
    SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree (Nonplanar.node a A')) =
    oudomGuinCirc
        (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree (Nonplanar.leaf a)))
        ((A'.map (fun c =>
            SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c))).prod) := by
  induction A' using Multiset.induction with
  | empty =>
    -- Base case: A' = 0. node a 0 = leaf a. Multiset.prod 0 = 1. circ_one_right.
    simp only [Multiset.map_zero, Multiset.prod_zero, ← leaf_eq_node_zero]
    rw [circ_one_right]
  | cons c A'' ih =>
    -- Cons case: A' = c ::ₘ A''.
    -- Setup: Q := (A''.map f).prod where f c' := ι(ofTree c').
    -- ((c ::ₘ A'').map f).prod = ι(ofTree c) * Q.
    -- By commutativity (SL is commutative algebra), ι(ofTree c) * Q = Q * ι(ofTree c).
    rw [Multiset.map_cons, Multiset.prod_cons]
    -- Goal: ι(ofTree (node a (c ::ₘ A''))) =
    --       ι(ofTree (leaf a)) ○ (ι(ofTree c) * (A''.map f).prod)
    -- Commute the product: ι(c) * Q = Q * ι(c).
    rw [mul_comm (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c))
        ((A''.map (fun c' => SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c'))).prod)]
    -- Now apply circ_T_mul: ι(leaf a) ○ (Q * ι(ofTree c)) =
    --   (ι(leaf a) ○ Q) ○ ι(ofTree c) - ι(leaf a) ○ (Q ○ ι(ofTree c))
    rw [circ_T_mul]
    -- Apply IH on A'': ι(leaf a) ○ Q = ι(ofTree (node a A''))
    -- The IH binder is `c`; the goal's binder is `c'`. Bridge via congr.
    rw [show (Multiset.map (fun c' =>
                SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c')) A'').prod =
            (Multiset.map (fun c =>
                SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c)) A'').prod from
        rfl]
    rw [← ih]
    -- Goal: ι(ofTree (node a (c ::ₘ A''))) =
    --       ι(ofTree (node a A'')) ○ ι(ofTree c) - ι(leaf a) ○ (Q ○ ι(ofTree c))
    --
    -- TODO: The cancellation argument. We need to show:
    --   ι(ofTree (node a (c ::ₘ A''))) =
    --   ι(ofMultiset (insertSum (node a A'') c)) - ι(leaf a) ○ (Q ○ ι(ofTree c))
    -- which reduces to:
    --   ι(leaf a) ○ (Q ○ ι(ofTree c)) =
    --   ι(ofMultiset (insertSum (node a A'') c \ {node a (c ::ₘ A'')}))
    -- (where the right side is the multiset of "subtree-graft" summands).
    --
    -- Each subtree-graft summand has form node a (d' ::ₘ A''.erase d) for
    -- d ∈ A'', d' ∈ insertSum d c. To match these against ι(leaf a) ○ (Q ○ ι c)
    -- we'd need:
    --   1. Notation 2.2 expansion: (∏ ι(c_i)) ○ ι(t) = Σ_i (∏_{j≠i} ι(c_j)) · ι(c_i • t in L).
    --   2. Pre-Lie product on L unfolding: ι(c) ○ ι(t) = ι(ofMultiset (insertSum c t)).
    --   3. Apply this lemma at smaller multisets (d' ::ₘ A''.erase d).
    --
    -- The challenge: Multiset.induction's IH gives the result for A''
    -- (one element smaller), but the cancellation needs the result for
    -- (d' ::ₘ A''.erase d) which has the SAME cardinality as A''.
    -- Requires either strong induction on `weight (node a A')` or a
    -- different lemma structure (e.g., extension over arbitrary x ∈ L
    -- rather than just basis trees).
    sorry

/-! ## §12: Piece C — OG Prop 3.2 on SL

`bMinusLin_SL a (A ★ B) = ε(A) • bMinusLin_SL a B + bMinusLin_SL a A ★ B`

OG paper page 10 proof, adapted:

By SymmetricAlgebra.induction on A:
1. **`algebraMap r`** (scalar): A ★ B = r • B (via 1 ★ _ = _ + scalar
   compatibility). LHS = r • bMinusLin_SL B. RHS: ε(r) = r, bMinusLin_SL r = 0.
   So ε(A) • bMinusLin_SL B + 0 ★ B = r • bMinusLin_SL B. ✓
2. **`ι x`** (substantive): use Piece D to write x's image as
   `ι(leaf rootLabel) ○ children`, then OG paper's chain via 2.8.v.
3. **`mul A₁ A₂`** (substantive): use IH on A₁ and A₂.
4. **`add A₁ A₂`** (linearity): trivial.

**Status**: stated with `sorry` pending Piece D + ε-Leibniz machinery. -/

/-- **Piece C**: OG Prop 3.2 (cocycle identity for `B⁻_SL_a` w.r.t. `★`).

    `bMinusLin_SL a (A ★ B) = ε(A) • bMinusLin_SL a B + bMinusLin_SL a A ★ B`

    SL-side analog of CK's `bMinusLin_gl_mul`. Proved via OG paper's
    page-10 argument (see header comment). The substantive case
    (`A = ι x`) uses `iotaTree_node_via_circ` (Piece D) + `circ_assoc_via_comul`
    (Prop 2.8.v, sorry-free in OudomGuinCirc.lean). -/
theorem bMinusLin_SL_oudomGuinStar (a : α) (A B : SL) :
    bMinusLin_SL a (oudomGuinStar A B) =
      SymmetricAlgebra.algebraMapInv (M := InsertionAlgebra α) A •
        bMinusLin_SL a B +
      oudomGuinStar (bMinusLin_SL a A) B := by
  induction A using SymmetricAlgebra.induction with
  | algebraMap r =>
    -- A = algebraMap r = r • 1. A ★ B = r • B (via 1 ★ B = B + scalar compat).
    -- bMinusLin_SL is linear, so bMinusLin_SL a (r • B) = r • bMinusLin_SL a B.
    -- ε(algebraMap r) = r. bMinusLin_SL (algebraMap r) = 0 (length-0 vanishes).
    -- 0 ★ B = 0. So RHS = r • bMinusLin_SL B + 0 = r • bMinusLin_SL B. ✓
    sorry
  | ι x =>
    -- The substantive case. Uses Piece D + Prop 2.8.v.
    sorry
  | mul A₁ A₂ ih₁ ih₂ =>
    -- A = A₁ * A₂. (A₁ · A₂) ★ B has its own associativity (Lemma 2.10:
    -- ★ on S(L) is associative + makes (S(L), ★, Δ) a Hopf algebra).
    -- Reduce via ih₁, ih₂ on the appropriate sub-products.
    sorry
  | add A₁ A₂ ih₁ ih₂ =>
    -- Linearity case: ★ is linear in first arg; ε linear; bMinusLin_SL linear.
    show bMinusLin_SL a (oudomGuinStar (A₁ + A₂) B) =
      SymmetricAlgebra.algebraMapInv (M := InsertionAlgebra α) (A₁ + A₂) •
        bMinusLin_SL a B +
      oudomGuinStar (bMinusLin_SL a (A₁ + A₂)) B
    -- TODO: oudomGuinStar linearity in first arg + algebraMapInv linearity
    -- + bMinusLin_SL linearity + ih₁ + ih₂. ~10 LOC mechanical.
    sorry

end SymAlg

end RootedTree
