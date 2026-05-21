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

/-! ### §9.5: Length-vanishing substrate for the ι case of Piece C

The cocycle ι case (`bMinusLin_SL_oudomGuinStar` at `A = ι Y`) reduces — via
Sweedler bashing on `cm B` — to the property that `bMinusLin_SL` extracts only
the length-1 component. We package this as two private lemmas:

- `bMinusLin_SL_ι_mul_ι`: `bMinusLin_SL a (ι Z · ι W) = 0`. Grade-2 vanishing
  via the TA-side `psiA_multi_succ_succ`.
- `bMinusLin_SL_ι_mul_eps`: `bMinusLin_SL a (ι Z · Y) = ε(Y) • bMinusLin_SL a (ι Z)`.
  The "B⁻ extracts the length-1 part" statement. Lifted from TA via
  `algHomL_surjective` + `TA_linearMap_ext_tprod`.
- `bMinusLin_SL_ι_star`: `bMinusLin_SL a (ι Y ★ B) = psiA_L a (circByT_total Y B)`.
  The length-argument identity for the ι case of OG Prop 3.2.
-/

/-- **Grade-2 vanishing**: `bMinusLin_SL a (ι Z · ι W) = 0`. Direct from
    `psiA_multi_succ_succ` (psiA_tensor vanishes on grade ≥ 2 tprods). -/
private theorem bMinusLin_SL_ι_mul_ι (a : α) (Z W : LL) :
    bMinusLin_SL a (SymmetricAlgebra.ι ℤ LL Z * SymmetricAlgebra.ι ℤ LL W) = 0 := by
  -- ι Z * ι W = algHom (ι_TA Z * ι_TA W). Push to TA side.
  have h_alg : SymmetricAlgebra.ι ℤ LL Z * SymmetricAlgebra.ι ℤ LL W =
      PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL)
        (TensorAlgebra.ι ℤ Z * TensorAlgebra.ι ℤ W) := by
    show _ = (SymmetricAlgebra.algHom ℤ LL).toLinearMap _
    show _ = SymmetricAlgebra.algHom ℤ LL (TensorAlgebra.ι ℤ Z * TensorAlgebra.ι ℤ W)
    rw [map_mul]
    rfl
  rw [h_alg, bMinusLin_SL_algHomL]
  -- ι_TA Z * ι_TA W = tprod 1 ![Z] * tprod 1 ![W] = tprod 2 (![Z] ++ ![W]).
  rw [PreLie.OudomGuinCircConstruct.ι_eq_tprod_one Z,
      PreLie.OudomGuinCircConstruct.ι_eq_tprod_one W]
  rw [PreLie.OudomGuinCircConstruct.tprod_mul_tprod]
  -- psiA_tensor (tprod 2 ...) = psiA_multi 2 ... = 0.
  rw [psiA_tensor_tprod, psiA_multi_succ_succ]
  rfl

/-- Helper: `algebraMapInv ∘ algHomL` vanishes on positive-grade tprods.
    `algHom (tprod (n+1) f) = ∏ ι(f i)` is a product of `n+1` ι-elements;
    `algebraMapInv` of any ι is 0, so the product is 0 (for n+1 ≥ 1). -/
private lemma algebraMapInv_algHom_tprod_succ (n : ℕ) (f : Fin (n+1) → LL) :
    SymmetricAlgebra.algebraMapInv (M := LL) (R := ℤ)
        ((SymmetricAlgebra.algHom ℤ LL) (TensorAlgebra.tprod ℤ LL (n+1) f)) = 0 := by
  rw [TensorAlgebra.tprod_apply, _root_.map_list_prod, List.map_ofFn,
      _root_.map_list_prod, List.map_ofFn]
  -- Goal: (List.ofFn (algebraMapInv ∘ algHom ∘ fun i => ι (f i))).prod = 0.
  -- Each composed function maps to 0: algHom (ι x) = ι_SL x; algebraMapInv (ι_SL x) = 0.
  simp only [Function.comp_def,
             show ∀ x, SymmetricAlgebra.algHom ℤ LL (TensorAlgebra.ι ℤ x) =
                 SymmetricAlgebra.ι ℤ LL x from fun _ => rfl,
             SymmetricAlgebra.algebraMapInv_ι]
  -- Goal: (List.ofFn (fun _ : Fin (n+1) => (0 : ℤ))).prod = 0.
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
  rw [show SymmetricAlgebra.ι ℤ LL Z =
        (SymmetricAlgebra.algHom ℤ LL) (TensorAlgebra.ι ℤ Z) from rfl]
  rw [← _root_.map_mul,
      PreLie.OudomGuinCircConstruct.ι_eq_tprod_one Z,
      PreLie.OudomGuinCircConstruct.tprod_mul_tprod]
  show bMinusLin_SL a (PreLie.OudomGuinCircConstruct.algHomL
        (TensorAlgebra.tprod ℤ LL (1+n) (Fin.append (fun _ => Z) f))) = _
  rw [bMinusLin_SL_algHomL, psiA_tensor_tprod]
  cases n with
  | zero =>
    -- LHS: psiA_multi a 1 (Fin.append ![Z] _) = psiA_L a Z (since (1+0 = 1) by rfl).
    -- RHS: algebraMapInv (algHom (tprod 0 f)) • bMinusLin_SL (algHom (tprod 1 ![Z])) = 1 • bMinusLin_SL (ι Z).
    show psiA_multi a 1 (Fin.append (fun _ : Fin 1 => Z) f) = _
    rw [psiA_multi_one_eq, psiA_multi_one_apply,
        show (Fin.append (fun _ : Fin 1 => Z) f) 0 = Z from rfl]
    rw [show (TensorAlgebra.tprod ℤ LL 0 f : TensorAlgebra ℤ LL) = 1 from by
      rw [TensorAlgebra.tprod_apply]; simp [List.ofFn_zero]]
    rw [_root_.map_one, _root_.map_one, one_smul]
    -- Convert RHS (algHom (tprod 1 ![Z])) back to (ι Z) and apply bMinusLin_SL_ι.
    simp only [← PreLie.OudomGuinCircConstruct.ι_eq_tprod_one]
    exact (bMinusLin_SL_ι a Z).symm
  | succ k =>
    -- LHS: psiA_multi a (1+(k+1)) (...) = 0 (grade ≥ 2 vanishing).
    -- RHS: algebraMapInv (algHom (tprod (k+1) _)) • _ = 0 • _ = 0 (positive grade).
    have h_multi_zero : psiA_multi a (1 + (k+1)) = 0 :=
      psiA_multi_eq_zero_of_ge_two a (by omega)
    rw [h_multi_zero]
    show (0 : SL) = _
    rw [algebraMapInv_algHom_tprod_succ k f, zero_smul]

/-- **B⁻ extracts the length-1 part of a left ι-multiplication**: for any
    `Z ∈ L` and `Y ∈ SL`, `bMinusLin_SL a (ι Z · Y) = ε(Y) • bMinusLin_SL a (ι Z)`.

    Proof: lift `Y = algHomL z` via `algHomL_surjective`. Reduce to a
    TA-level LinearMap equality `F = G` via `TA_linearMap_ext_tprod`. Each
    `tprod n f` case is handled by `bMinusLin_SL_ι_mul_algHom_tprod`. -/
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

/-- **Length-argument lemma** (the ι case of Piece C reduces to this): for
    `Y ∈ L` and `B ∈ SL`,
    `bMinusLin_SL a (ι Y ★ B) = psiA_L a (circByT_total Y B)`.

    Proof: unfold `★` via Def 2.9 to get a sum over Sweedler of
    `(ι Y ○ B₁) · B₂ = ι(circByT_total Y B₁) · B₂`. Apply `bMinusLin_SL_ι_mul_eps`
    to each summand: only the length-0 component of `B₂` contributes (giving
    `ε(B₂) • bMinusLin_SL (ι(circByT_total Y B₁))`). Sum collapses via the
    counit-comul triangle to `psiA_L a (circByT_total Y B)`. -/
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
    -- Compute LHS = bMinusLin_SL a (oudomGuinCirc (ι Y) b₁ * b₂)
    --         = bMinusLin_SL a (ι (circByT_total Y b₁) * b₂)
    --         = ε(b₂) • bMinusLin_SL a (ι (circByT_total Y b₁))
    --         = ε(b₂) • psiA_L a (circByT_total Y b₁).
    have h_LHS :
        ((bMinusLin_SL a).comp ((LinearMap.mul' ℤ SL).comp
          (TensorProduct.map
            (oudomGuinCirc (R := ℤ) (SymmetricAlgebra.ι ℤ LL Y))
            (LinearMap.id : SL →ₗ[ℤ] SL)))) (b₁ ⊗ₜ[ℤ] b₂) =
        SymmetricAlgebra.algebraMapInv (M := LL) b₂ •
          psiA_L a (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) Y b₁) := by
      show (bMinusLin_SL a) ((LinearMap.mul' ℤ SL)
            (((oudomGuinCirc (R := ℤ) (SymmetricAlgebra.ι ℤ LL Y)) b₁) ⊗ₜ[ℤ] b₂)) = _
      rw [LinearMap.mul'_apply]
      -- Goal: bMinusLin_SL a (oudomGuinCirc (ι Y) b₁ * b₂) = ε(b₂) • psiA_L a (circByT_total Y b₁)
      conv_lhs => rw [show oudomGuinCirc (R := ℤ) (SymmetricAlgebra.ι ℤ LL Y) b₁ =
                          SymmetricAlgebra.ι ℤ LL
                            (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ) Y b₁)
                      from by rw [oudomGuinCirc_eq_ofConv, circHom_ι]; rfl]
      rw [bMinusLin_SL_ι_mul_eps, bMinusLin_SL_ι]
    -- Compute RHS = psiA_L a (circByT_total Y (b₁ * algebraMap (ε b₂)))
    --         = psiA_L a (circByT_total Y (ε(b₂) • b₁))
    --         = ε(b₂) • psiA_L a (circByT_total Y b₁).
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
  -- Goal: psiA_L a (circByT_total Y (mul' (map id (algebraMap ∘ counit) cmB)))
  --     = psiA_L a (circByT_total Y B)
  -- Reduce inner: mul' (map id (algebraMap ∘ counit) cmB) = B via counit triangle.
  -- Force CoalgebraStruct on the unfolded type via the Bialgebra instance directly.
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

/-! ### §11.A: Substrate helpers for the cancellation argument -/

/-- **Notation 2.2** (Oudom-Guin): Leibniz formula for `oudomGuinCirc · (ι X)`
    applied to a multiset product. For any `f : β → SL` and `M : Multiset β`:

    `(M.map f).prod ○ ι X = Σ_{s ∈ M} ((M.erase s).map f).prod · (f s ○ ι X)`

    Each summand "pulls out" the factor `f s`, applies `○ ι X` to it, and keeps
    the rest of the product as-is. With duplicates in `M`: `erase` removes one
    copy, so the multinomial coefficient is implicit in iterating `Multiset.map`.

    Proof structure: `Multiset.induction` on `M`. Base case: `1 ○ ι X = 0 =
    empty sum` via `one_circ` + `algebraMapInv_ι` (since `ι X` has zero scalar
    part). Cons case `t ::ₘ M`: apply `oudomGuinCirc_mul_ι` (Leibniz form,
    Prop 2.7.iii specialization), apply IH, then equate per-summand via
    `Multiset.map_congr` (handling `(t::M).erase s = t :: M.erase s` for `s≠t`
    and `(t::M).erase t = M` for `s = t` from `cons_erase`). -/
private theorem prod_oudomGuinCirc_ι_aux {β : Type*} [DecidableEq β]
    (f : β → SL) (M : Multiset β) (X : LL) :
    oudomGuinCirc (R := ℤ) (M.map f).prod (SymmetricAlgebra.ι ℤ LL X) =
      (M.map (fun s => ((M.erase s).map f).prod *
        oudomGuinCirc (R := ℤ) (f s) (SymmetricAlgebra.ι ℤ LL X))).sum := by
  induction M using Multiset.induction with
  | empty =>
    -- LHS: oudomGuinCirc 1 (ι X) = algebraMapInv (ι X) • 1 = 0 (since ι X has 0 scalar part)
    -- RHS: empty sum = 0
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero]
    rw [one_circ, SymmetricAlgebra.algebraMapInv_ι]
    exact zero_smul _ _
  | cons t M ih =>
    -- LHS: (f t * (M.map f).prod) ○ ι X
    --    = (f t ○ ι X) * (M.map f).prod + f t * ((M.map f).prod ○ ι X)  [Leibniz]
    --    = (f t ○ ι X) * (M.map f).prod + f t * (M.map g).sum  [by IH]
    --      where g(s) = ((M.erase s).map f).prod * (f s ○ ι X)
    -- RHS: ((t ::ₘ M).map g').sum where g'(s) = ((t ::ₘ M).erase s).map f).prod * (f s ○ ι X)
    --    = g'(t) + (M.map g').sum
    --    = (M.map f).prod * (f t ○ ι X) + (M.map g').sum  [erase_cons_head]
    -- We need: (M.map g').sum = f t * (M.map g).sum.
    -- For each s ∈ M: g'(s) = ((t ::ₘ M).erase s).map f).prod * (f s ○ ι X).
    --   If s = t (t ∈ M): erase_cons_head → ((t ::ₘ M).erase t = M),
    --     so g'(t) = (M.map f).prod * (f t ○ ι X) = (t ::ₘ M.erase t).map f).prod * (f t ○ ι X)
    --     = f t * (M.erase t).map f).prod * (f t ○ ι X) = f t * g(t).  ✓
    --   If s ≠ t: erase_cons_tail → ((t ::ₘ M).erase s = t ::ₘ M.erase s),
    --     so g'(s) = (t ::ₘ M.erase s).map f).prod * (f s ○ ι X)
    --     = f t * (M.erase s).map f).prod * (f s ○ ι X) = f t * g(s).  ✓
    rw [Multiset.map_cons, Multiset.prod_cons, oudomGuinCirc_mul_ι, ih]
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
    rw [mul_comm ((M.map f).prod) (oudomGuinCirc (f t) _)]
    congr 1
    -- Goal: f t * (M.map g).sum = (M.map g').sum where g/g' per above.
    rw [← Multiset.sum_map_mul_left]
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro s hs
    -- Per-s: f t * (((M.erase s).map f).prod * (f s ○ ι X)) =
    --        ((t ::ₘ M).erase s).map f).prod * (f s ○ ι X)
    -- Split on s = t vs s ≠ t.
    by_cases hst : s = t
    · -- s = t case: subst eliminates t, replacing with s.
      subst hst
      -- After subst: Context has M : Multiset β, s : β, hs : s ∈ M
      -- Goal: f s * ((M.erase s).map f).prod * (f s ○ X) =
      --       ((s ::ₘ M).erase s).map f).prod * (f s ○ X)
      have hM : M = s ::ₘ M.erase s := (Multiset.cons_erase hs).symm
      rw [Multiset.erase_cons_head]
      -- Goal: f s * ((M.erase s).map f).prod * (f s ○ X) = (M.map f).prod * (f s ○ X)
      conv_rhs => rw [hM, Multiset.map_cons, Multiset.prod_cons]
      ring
    · -- s ≠ t case. (t :: M).erase s = t :: M.erase s
      have h_ne : t ≠ s := Ne.symm hst
      rw [Multiset.erase_cons_tail (s := M) h_ne, Multiset.map_cons,
          Multiset.prod_cons]
      ring

/-! ### Substrate for `insertSum_node_decompose`

The decomposition uses two helpers: a Multiset cons/+ swap and a
prefix-generalized list-induction lemma. -/

/-- Multiset identity: `B + (x ::ₘ C) = (x ::ₘ B) + C`. A single cons can
    swap from "right of +" to "left of +". -/
private lemma cons_add_swap {β : Type*} (x : β) (B C : Multiset β) :
    B + (x ::ₘ C) = (x ::ₘ B) + C := by
  rw [Multiset.add_cons, ← Multiset.cons_add]

/-- Prefix-generalized auxiliary form of `insertSum_node_decompose`. The
    induction substrate: list-induction on `cs` with an arbitrary prefix
    `pre` carried in the inner `node`'s children-multiset. -/
private theorem insertSumList_bind_lift_aux [DecidableEq (Nonplanar α)]
    (a : α) (pre : Multiset (Nonplanar α))
    (cs : List (Planar α)) (c_pl : Planar α) :
    (Planar.insertSumList cs c_pl).map (fun cs' =>
      Nonplanar.node a (pre + ↑(cs'.map Nonplanar.mk))) =
    (↑(cs.map Nonplanar.mk) : Multiset (Nonplanar α)).bind (fun d =>
      (Nonplanar.insertSum d (Nonplanar.mk c_pl)).map (fun d' =>
        Nonplanar.node a (d' ::ₘ pre +
          (↑(cs.map Nonplanar.mk) : Multiset (Nonplanar α)).erase d))) := by
  induction cs generalizing pre with
  | nil =>
    simp only [Planar.insertSumList_nil, Multiset.map_zero,
               List.map_nil, Multiset.coe_nil, Multiset.zero_bind]
  | cons e cs' ih =>
    rw [Planar.insertSumList_cons, Multiset.map_add,
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
          (Planar.insertSumList cs' c_pl).map (fun L' =>
            Nonplanar.node a (pre + ↑((e :: L').map Nonplanar.mk))) =
          (Planar.insertSumList cs' c_pl).map (fun L' =>
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

/-- **Nonplanar.insertSum node decomposition** (Multiset.bind form): grafting
    `c` at each vertex of `node a A''` splits into one root-graft summand
    `node a (c ::ₘ A'')` plus a bind over `A''` of subtree-grafts at each
    child `d ∈ A''`. Proof: descend through planar representatives, apply
    `Planar.insertSum_node` then bridge to the bind via the prefix-generalized
    `insertSumList_bind_lift_aux`. -/
private theorem insertSum_node_decompose [DecidableEq (Nonplanar α)]
    (a : α) (A'' : Multiset (Nonplanar α)) (c : Nonplanar α) :
    Nonplanar.insertSum (Nonplanar.node a A'') c =
      Nonplanar.node a (c ::ₘ A'') ::ₘ
      A''.bind (fun d => (Nonplanar.insertSum d c).map
        (fun d' => Nonplanar.node a (d' ::ₘ A''.erase d))) := by
  -- Step 1: Substitute c = mk c_pl and A'' = ↑(cs.map mk) for planar reps.
  obtain ⟨c_pl, rfl⟩ : ∃ c_pl : Planar α, c = Nonplanar.mk c_pl :=
    ⟨c.out, c.out_eq.symm⟩
  obtain ⟨cs, rfl⟩ : ∃ cs : List (Planar α),
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
  -- Step 2: Reduce LHS via `node_mk_planar_list` + `mk_insertSum` +
  -- `Planar.insertSum_node` + `Multiset.map_cons`.
  rw [Nonplanar.node_mk_planar_list a cs, Nonplanar.mk_insertSum,
      Planar.insertSum_node, Multiset.map_cons]
  -- Step 3: Match the two cons-heads + tails separately.
  congr 1
  · -- Heads: `mk (Planar.node a (c_pl :: cs)) = node a (mk c_pl ::ₘ ↑(cs.map mk))`
    -- by `node_mk_planar_list`-symm + `cons_coe` (rfl).
    rw [← Nonplanar.node_mk_planar_list a (c_pl :: cs)]
    rfl
  · -- Tails: `((insertSumList cs c_pl).map (Planar.node a)).map mk = bind form`.
    rw [Multiset.map_map]
    -- LHS bridge: `(mk ∘ Planar.node a) cs' = node a (0 + ↑(cs'.map mk))`.
    have hLHS_eq : (Planar.insertSumList cs c_pl).map
          (Nonplanar.mk ∘ Planar.node a) =
        (Planar.insertSumList cs c_pl).map (fun cs' =>
          Nonplanar.node a (0 + ↑(cs'.map Nonplanar.mk))) := by
      apply Multiset.map_congr rfl
      intro cs' _
      show Nonplanar.mk (Planar.node a cs') =
           Nonplanar.node a (0 + ↑(cs'.map Nonplanar.mk))
      rw [Multiset.zero_add, Nonplanar.node_mk_planar_list]
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

/-- Linearity of `ι ∘ ofMultiset`: `ι(ofMultiset M) = Σ_{t ∈ M} ι(ofTree t)`.
    Mechanical Multiset.induction on M. -/
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

/-! ### §11.B: Main theorem — `iotaTree_node_via_circ` via strong cardinality
induction -/

/-- **Piece D**: every nonplanar tree is the OG circ-product of its
    singleton-vertex root with its children-forest.

    `ι(ofTree (node a A')) = ι(ofTree (leaf a)) ○ (∏ c ∈ A', ι(ofTree c))`

    OG paper §3 Prop 3.1 (page 9): for the free pre-Lie algebra of rooted
    trees, the universal property gives this identity.

    **Proof strategy**: strong induction on `A'.card`. The cancellation
    argument requires the IH at multisets of cardinality `n - 1` of the
    form `d' ::ₘ A''.erase d` where `d ∈ A''`, `d' ∈ insertSum d c` — these
    have `card = 1 + (n - 2) = n - 1 < n`. NB: weight is NOT a valid
    induction measure: weight is conserved exactly under subtree-grafting
    (weight `node a (d' ::ₘ A''.erase d) = 1 + weight(c) + weight(A'') =
    weight(node a (c ::ₘ A''))`); only cardinality of the children-multiset
    strictly decreases. -/
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
      · -- Now LHS: ιa ○ Qιc. RHS: bind-of-IH-applied sum.
        -- Compute LHS via Notation 2.2 + ι linearity.
        show oudomGuinCirc (R := ℤ) ιa Qιc = _
        -- Unfold Qιc := oudomGuinCirc Q (ι c).
        show oudomGuinCirc (R := ℤ) ιa
          (oudomGuinCirc (R := ℤ) Q
            (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree c))) = _
        -- Q = (A''.map f).prod. Apply Notation 2.2 on Q ○ ι c.
        rw [show Q = (A''.map f).prod from rfl,
            prod_oudomGuinCirc_ι_aux f A'' (InsertionAlgebra.ofTree c)]
        -- Inner: Q ○ ι c = (A''.map (fun d => (A''.erase d).map f).prod * (f d ○ ι c))).sum.
        -- Apply ιa ○ _ linearity to distribute over the outer sum.
        rw [map_multiset_sum, Multiset.map_map]
        -- LHS: (A''.map (ιa ○ ·) ∘ (fun d => ...)).sum.
        -- Rewrite per d: ιa ○ ((A''.erase d).map f).prod * (f d ○ ι c)) = (per d sum).
        -- The RHS is a bind: Σ_{d ∈ A''} (insertSum d c).map (...).sum.
        -- Reformulate the RHS using Multiset.sum_bind:
        rw [Multiset.sum_bind]
        -- Now both sides are sums over A''. Show termwise equality.
        apply congrArg Multiset.sum
        apply Multiset.map_congr rfl
        intro d hd
        simp only [Function.comp_apply]
        -- Per-d goal: ιa ○ (Md * (f d ○ ι c)) =
        --   (insertSum d c).map (fun d' => ιa ○ ((d' ::ₘ A''.erase d).map f).prod).sum
        -- where Md = ((A''.erase d).map f).prod.
        -- Step 1: convert (d' ::ₘ A''.erase d).map f).prod = f d' * Md
        simp only [Multiset.map_cons, Multiset.prod_cons]
        -- Step 2: replace f d ○ ι c = ι(d * c) = ι(ofMultiset (insertSum d c))
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
        -- Step 3: distribute ιa ○ (Md * ι(ofMultiset (insertSum d c)))
        -- via iota_ofMultiset and linearity.
        rw [iota_ofMultiset, ← Multiset.sum_map_mul_left, map_multiset_sum,
            Multiset.map_map]
        -- Both sides are sums over (insertSum d c). Match termwise.
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

/-! ### §11.C: Helpers for the ι case of OG Prop 3.2 (`psiA_L_circByT_total_eq`)

Three helpers and the main identity, all consumed by `bMinusLin_SL_oudomGuinStar`'s
ι branch (§12). Stated separately so each helper's proof can be inspected
independently:

- `psiA_L_ofMultiset`: linearity over multiset sums.
- `psiA_L_mul_eq` (L-side cocycle): bilinear extension to the basis case;
  substantive math via `insertSum_node_decompose` + `prod_oudomGuinCirc_ι_aux`.
- `psiA_L_circByT_leaf_eq_id` (key lemma): TA-descent + n-induction;
  cancellation via `oudomGuinCirc_algHomL_tprod_ι`.
- `psiA_L_circByT_leaf_eq_zero` (a' ≠ a analog): same descent, IH ≡ 0.
- `psiA_L_circByT_total_eq`: main identity; uses Piece D
  (`iotaTree_node_via_circ`) + 2.8.v (`circ_assoc_via_comul`) +
  `bMinusLin_SL_ι` bridge + Helper 2/3 case split. -/

/-- Linearity of `psiA_L` over `ofMultiset`: `psiA_L a (ofMultiset M) =
    sum of psiA_basis a applied termwise`. Direct multiset induction. -/
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

/-- Closed-form for `psiA_basis a (node a A)` (self-color case):
    `((A.map ιTree).prod)`. -/
private lemma psiA_basis_node_self (a : α) (A : Multiset (Nonplanar α)) :
    psiA_basis a (Nonplanar.node a A) =
      (A.map (fun c => ιTree c)).prod := by
  unfold psiA_basis
  rw [Nonplanar.rootLabel_node, Nonplanar.rootChildren_node]
  exact if_pos rfl

/-- Closed-form for `psiA_basis a (node a' A)` (off-color case): `0`. -/
private lemma psiA_basis_node_neq (a a' : α) (h : a' ≠ a)
    (A : Multiset (Nonplanar α)) :
    psiA_basis a (Nonplanar.node a' A) = 0 := by
  unfold psiA_basis
  rw [Nonplanar.rootLabel_node]
  exact if_neg h

/-- **L-side cocycle for `psiA_L`** (Helper 1 of `psiA_L_circByT_total_eq`):
    `psiA_L a (Y * Z) = (psiA_L a Y) ○ ι Z + (psiA_L a Y) · ι Z` for `Y, Z ∈ L`.

    Proof: bilinear extension to basis case `(Y, Z) = (ofTree t, ofTree s)`,
    decomposed via `insertSum_node_decompose`; LHS bind-sum matches
    `Q ○ ι(ofTree s)` via `prod_oudomGuinCirc_ι_aux` + `iota_ofMultiset`. -/
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
      have hY : Y' = r • InsertionAlgebra.ofTree t :=
        (Finsupp.smul_single_one t r).symm
      rw [hY]
      have h_psi_smul :
          psiA_L a (r • InsertionAlgebra.ofTree t) =
            r • psiA_L a (InsertionAlgebra.ofTree t) :=
        map_smul _ _ _
      have h_LHS_eq :
          psiA_L a ((r • InsertionAlgebra.ofTree t) * Z) =
            r • psiA_L a (InsertionAlgebra.ofTree t * Z) := by
        rw [smul_mul_assoc, map_smul]
      have h_oudom_smul :
          oudomGuinCirc (R := ℤ) (psiA_L a (r • InsertionAlgebra.ofTree t))
              (SymmetricAlgebra.ι ℤ LL Z) =
            r • oudomGuinCirc (R := ℤ) (psiA_L a (InsertionAlgebra.ofTree t))
              (SymmetricAlgebra.ι ℤ LL Z) := by
        rw [h_psi_smul]
        rw [show oudomGuinCirc (R := ℤ)
              (r • psiA_L a (InsertionAlgebra.ofTree t))
              (SymmetricAlgebra.ι ℤ LL Z) =
              r • oudomGuinCirc (R := ℤ)
                (psiA_L a (InsertionAlgebra.ofTree t))
                (SymmetricAlgebra.ι ℤ LL Z) from by
          have := LinearMap.congr_fun
            ((oudomGuinCirc (R := ℤ)).map_smul r
              (psiA_L a (InsertionAlgebra.ofTree t)))
            (SymmetricAlgebra.ι ℤ LL Z)
          simp only [LinearMap.smul_apply] at this
          exact this]
      have h_RHS_mul :
          psiA_L a (r • InsertionAlgebra.ofTree t) *
              SymmetricAlgebra.ι ℤ LL Z =
            r • (psiA_L a (InsertionAlgebra.ofTree t) *
                  SymmetricAlgebra.ι ℤ LL Z) := by
        rw [h_psi_smul, smul_mul_assoc]
      rw [h_LHS_eq, h_oudom_smul, h_RHS_mul, ← smul_add]
      congr 1
      -- Clear the Z-dependent helper hypotheses so the inner induction's IHs
      -- don't get cluttered with preconditions.
      clear h_LHS_eq h_oudom_smul h_RHS_mul h_psi_smul hY
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
        have hZ : Z' = u • InsertionAlgebra.ofTree s :=
          (Finsupp.smul_single_one s u).symm
        rw [hZ]
        have h_RHS_circ :
            oudomGuinCirc (R := ℤ) (psiA_L a (InsertionAlgebra.ofTree t))
              (SymmetricAlgebra.ι ℤ LL (u • InsertionAlgebra.ofTree s)) =
            u • oudomGuinCirc (R := ℤ) (psiA_L a (InsertionAlgebra.ofTree t))
              (SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree s)) := by
          rw [map_smul]
          exact (oudomGuinCirc (R := ℤ)
            (psiA_L a (InsertionAlgebra.ofTree t))).map_smul u _
        have h_RHS_mul :
            psiA_L a (InsertionAlgebra.ofTree t) *
                SymmetricAlgebra.ι ℤ LL (u • InsertionAlgebra.ofTree s) =
              u • (psiA_L a (InsertionAlgebra.ofTree t) *
                    SymmetricAlgebra.ι ℤ LL (InsertionAlgebra.ofTree s)) := by
          rw [map_smul, mul_smul_comm]
        rw [mul_smul_comm, map_smul, h_RHS_circ, h_RHS_mul, ← smul_add]
        congr 1
        exact h_basis t s
  -- Basis case.
  intro t s
  obtain ⟨a', A', rfl⟩ : ∃ a' A', t = Nonplanar.node a' A' :=
    ⟨t.rootLabel, t.rootChildren, (Nonplanar.node_eta t).symm⟩
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
    rw [hQ, prod_oudomGuinCirc_ι_aux (fun c => ιTree c) A'
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
        psiA_basis a (Nonplanar.node a' B) = 0 := psiA_basis_node_neq a a' ha
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

/-- **Key lemma** (Helper 2 of `psiA_L_circByT_total_eq`): for `X ∈ SL`,
    `psiA_L a (circByT_total (leaf a) X) = X`.

    TA-descent + induction on `n`. n+1 case: apply `psiA_L_mul_eq` to the
    leading term of `circTMultilinear_succ`, then `oudomGuinCirc_algHomL_tprod_ι`
    cancels the negative sum. -/
private theorem psiA_L_circByT_leaf_eq_id [DecidableEq (Nonplanar α)]
    (a : α) (X : SL) :
    psiA_L a (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
      (InsertionAlgebra.ofTree (Nonplanar.leaf a)) X) = X := by
  classical
  obtain ⟨z, rfl⟩ := PreLie.OudomGuinCircConstruct.algHomL_surjective X
  suffices h_per_tprod : ∀ (n : ℕ) (f : Fin n → LL),
      psiA_L a (PreLie.OudomGuinCircConstruct.circTMultilinear ℤ
        (InsertionAlgebra.ofTree (Nonplanar.leaf a)) n f) =
      PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL)
        (TensorAlgebra.tprod ℤ LL n f) by
    have h_eq :
        (psiA_L a).comp
          ((PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
            (InsertionAlgebra.ofTree (Nonplanar.leaf a))).comp
          (PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL))) =
        PreLie.OudomGuinCircConstruct.algHomL := by
      apply PreLie.OudomGuinCircConstruct.TA_linearMap_ext_tprod
      intro n f
      simp only [LinearMap.comp_apply]
      have h_tot := LinearMap.congr_fun
        (PreLie.OudomGuinCircConstruct.circByT_total_comp_algHomL (R := ℤ)
          (InsertionAlgebra.ofTree (Nonplanar.leaf a)))
        (TensorAlgebra.tprod ℤ LL n f)
      simp only [LinearMap.comp_apply] at h_tot
      rw [h_tot, PreLie.OudomGuinCircConstruct.circTTensor_tprod]
      exact h_per_tprod n f
    exact LinearMap.congr_fun h_eq z
  intro n
  induction n with
  | zero =>
    intro f
    rw [PreLie.OudomGuinCircConstruct.circTMultilinear_zero, psiA_L_ofTree]
    rw [leaf_eq_node_zero, psiA_basis_node_self]
    rw [Multiset.map_zero, Multiset.prod_zero]
    rw [show TensorAlgebra.tprod ℤ LL 0 f = (1 : TensorAlgebra ℤ LL) from by
          rw [TensorAlgebra.tprod_apply]; simp [List.ofFn_zero]]
    show (1 : SL) = (SymmetricAlgebra.algHom ℤ LL).toLinearMap 1
    show (1 : SL) = SymmetricAlgebra.algHom ℤ LL 1
    rw [map_one]
  | succ n IH =>
    intro f
    rw [PreLie.OudomGuinCircConstruct.circTMultilinear_succ]
    rw [map_sub, map_sum, psiA_L_mul_eq, IH (Fin.init f)]
    rw [oudomGuinCirc_algHomL_tprod_ι (f (Fin.last n)) n (Fin.init f)]
    rw [show ∑ i, psiA_L a (PreLie.OudomGuinCircConstruct.circTMultilinear ℤ
                (InsertionAlgebra.ofTree (Nonplanar.leaf a)) n
                (Function.update (Fin.init f) i (Fin.init f i * f (Fin.last n)))) =
            ∑ i, PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL)
              (TensorAlgebra.tprod ℤ LL n
                (Function.update (Fin.init f) i (Fin.init f i * f (Fin.last n))))
          from Finset.sum_congr rfl (fun i _ => IH _)]
    rw [add_sub_cancel_left]
    rw [show PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL)
              (TensorAlgebra.tprod ℤ LL (n + 1) f) =
            PreLie.OudomGuinCircConstruct.algHomL
              (TensorAlgebra.tprod ℤ LL n (Fin.init f)) *
              SymmetricAlgebra.ι ℤ LL (f (Fin.last n))
        from by
      have h_f_eq : f = Fin.snoc (Fin.init f) (f (Fin.last n)) :=
        (Fin.snoc_init_self f).symm
      have h_tprod_succ :
          TensorAlgebra.tprod ℤ LL (n + 1) f =
          TensorAlgebra.tprod ℤ LL n (Fin.init f) *
            TensorAlgebra.ι ℤ (f (Fin.last n)) := by
        conv_lhs => rw [h_f_eq]
        rw [Fin.snoc_eq_append,
            PreLie.OudomGuinCircConstruct.ι_eq_tprod_one,
            ← PreLie.OudomGuinCircConstruct.tprod_mul_tprod]
        congr 1
      rw [h_tprod_succ]
      show (SymmetricAlgebra.algHom ℤ LL).toLinearMap _ = _
      show (SymmetricAlgebra.algHom ℤ LL) _ = _
      rw [map_mul]
      rfl]

/-- **Vanishing key lemma** (Helper 3 of `psiA_L_circByT_total_eq`): for
    `a' ≠ a` and `X ∈ SL`,
    `psiA_L a (circByT_total (leaf a') X) = 0`.

    Same TA-descent as Helper 2. n+1 step: IH gives 0 in both the leading
    term and the negative sum, so no cancellation needed. -/
private theorem psiA_L_circByT_leaf_eq_zero [DecidableEq (Nonplanar α)]
    (a a' : α) (h : a' ≠ a) (X : SL) :
    psiA_L a (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
      (InsertionAlgebra.ofTree (Nonplanar.leaf a')) X) = 0 := by
  classical
  obtain ⟨z, rfl⟩ := PreLie.OudomGuinCircConstruct.algHomL_surjective X
  suffices h_per_tprod : ∀ (n : ℕ) (f : Fin n → LL),
      psiA_L a (PreLie.OudomGuinCircConstruct.circTMultilinear ℤ
        (InsertionAlgebra.ofTree (Nonplanar.leaf a')) n f) = 0 by
    have h_eq :
        (psiA_L a).comp
          ((PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
            (InsertionAlgebra.ofTree (Nonplanar.leaf a'))).comp
          (PreLie.OudomGuinCircConstruct.algHomL (R := ℤ) (L := LL))) =
        0 := by
      apply PreLie.OudomGuinCircConstruct.TA_linearMap_ext_tprod
      intro n f
      simp only [LinearMap.comp_apply, LinearMap.zero_apply]
      have h_tot := LinearMap.congr_fun
        (PreLie.OudomGuinCircConstruct.circByT_total_comp_algHomL (R := ℤ)
          (InsertionAlgebra.ofTree (Nonplanar.leaf a')))
        (TensorAlgebra.tprod ℤ LL n f)
      simp only [LinearMap.comp_apply] at h_tot
      rw [h_tot, PreLie.OudomGuinCircConstruct.circTTensor_tprod]
      exact h_per_tprod n f
    exact LinearMap.congr_fun h_eq z
  intro n
  induction n with
  | zero =>
    intro f
    rw [PreLie.OudomGuinCircConstruct.circTMultilinear_zero, psiA_L_ofTree,
        leaf_eq_node_zero, psiA_basis_node_neq a a' h]
  | succ n IH =>
    intro f
    rw [PreLie.OudomGuinCircConstruct.circTMultilinear_succ]
    rw [map_sub, map_sum, psiA_L_mul_eq, IH (Fin.init f)]
    -- IH gives 0 for leading-term Y. So 0 ○ ι _ + 0 * ι _ = 0.
    rw [LinearMap.map_zero, LinearMap.zero_apply, zero_add, zero_mul]
    -- Σᵢ IH = Σᵢ 0 = 0. Then 0 - 0 = 0.
    rw [show ∑ i, psiA_L a (PreLie.OudomGuinCircConstruct.circTMultilinear ℤ
                (InsertionAlgebra.ofTree (Nonplanar.leaf a')) n
                (Function.update (Fin.init f) i (Fin.init f i * f (Fin.last n)))) =
            (0 : SL) from by
      rw [show (0 : SL) = ∑ _ : Fin n, (0 : SL) from
            (Finset.sum_const_zero).symm]
      exact Finset.sum_congr rfl (fun i _ => IH _)]
    rw [sub_zero]

/-- **Substantive identity** for the ι case of Piece C: for `Y ∈ L` and `B ∈ SL`,
    `psiA_L a (circByT_total Y B) = (psiA_L a Y) ★ B`.

    **Proof**: Reduce Y via `Finsupp.induction_linear` to `Y = ofTree t`.
    By `Nonplanar.node_eta`, `t = node a' A'`. Apply `iotaTree_node_via_circ`
    (Piece D) to factor `ι(ofTree(node a' A')) = ι(leaf a') ○ Q` where
    `Q = ∏_{c ∈ A'} ι(ofTree c)`; then `circ_assoc_via_comul` (Prop 2.8.v)
    converts `(ι(leaf a') ○ Q) ○ B` to `ι(leaf a') ○ (Q ★ B) =
    ι(circByT_total (leaf a') (Q ★ B))`. Bridge via `bMinusLin_SL_ι`:
    `psiA_L a (circByT_total (node a' A') B) =
     psiA_L a (circByT_total (leaf a') (Q ★ B))`. Case-split:
    - `a' = a`: Helper 2 gives `Q ★ B`, matching RHS.
    - `a' ≠ a`: Helper 3 gives 0; `psiA_basis a (node a' _) = 0` makes RHS 0. -/
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
      ⟨t.rootLabel, t.rootChildren, (Nonplanar.node_eta t).symm⟩
    set Q : SL := (A'.map (fun c => SymmetricAlgebra.ι ℤ LL
      (InsertionAlgebra.ofTree c))).prod with hQ
    have h_circ_node :
        SymmetricAlgebra.ι ℤ LL
          (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
            (InsertionAlgebra.ofTree (Nonplanar.node a' A')) B) =
        SymmetricAlgebra.ι ℤ LL
          (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
            (InsertionAlgebra.ofTree (Nonplanar.leaf a')) (oudomGuinStar Q B)) := by
      have h_LHS_circ :
          SymmetricAlgebra.ι ℤ LL
              (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
                (InsertionAlgebra.ofTree (Nonplanar.node a' A')) B) =
          oudomGuinCirc (R := ℤ) (SymmetricAlgebra.ι ℤ LL
            (InsertionAlgebra.ofTree (Nonplanar.node a' A'))) B := by
        rw [oudomGuinCirc_eq_ofConv, circHom_ι]
        rfl
      have h_RHS_circ :
          SymmetricAlgebra.ι ℤ LL
              (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
                (InsertionAlgebra.ofTree (Nonplanar.leaf a')) (oudomGuinStar Q B)) =
          oudomGuinCirc (R := ℤ) (SymmetricAlgebra.ι ℤ LL
            (InsertionAlgebra.ofTree (Nonplanar.leaf a'))) (oudomGuinStar Q B) := by
        rw [oudomGuinCirc_eq_ofConv, circHom_ι]
        rfl
      rw [h_LHS_circ, h_RHS_circ, iotaTree_node_via_circ a' A',
          circ_assoc_via_comul]
      rfl
    have h_psi_eq :
        psiA_L a (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
          (InsertionAlgebra.ofTree (Nonplanar.node a' A')) B) =
        psiA_L a (PreLie.OudomGuinCircConstruct.circByT_total (R := ℤ)
          (InsertionAlgebra.ofTree (Nonplanar.leaf a')) (oudomGuinStar Q B)) := by
      have := congrArg (bMinusLin_SL a) h_circ_node
      simp only [bMinusLin_SL_ι] at this
      exact this
    rw [h_psi_eq, psiA_L_ofTree]
    by_cases ha : a' = a
    · subst ha
      rw [psiA_L_circByT_leaf_eq_id, psiA_basis_node_self]
      rfl
    · rw [psiA_L_circByT_leaf_eq_zero a a' ha,
          psiA_basis_node_neq a a' ha, oudomGuinStar_zero_left]

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
theorem bMinusLin_SL_oudomGuinStar [DecidableEq (Nonplanar α)]
    (a : α) (A B : SL) :
    bMinusLin_SL a (oudomGuinStar A B) =
      SymmetricAlgebra.algebraMapInv (M := InsertionAlgebra α) A •
        bMinusLin_SL a B +
      oudomGuinStar (bMinusLin_SL a A) B := by
  induction A using SymmetricAlgebra.induction with
  | algebraMap r =>
    -- A = algebraMap r = r • 1. (r • 1) ★ B = r • (1 ★ B) = r • B.
    -- bMinusLin_SL (r • 1) = r • bMinusLin_SL 1 = 0. ε(algebraMap r) = r.
    -- LHS = bMinusLin_SL (r • B) = r • bMinusLin_SL B.
    -- RHS = r • bMinusLin_SL B + 0 ★ B = r • bMinusLin_SL B + 0.
    rw [Algebra.algebraMap_eq_smul_one, oudomGuinStar_smul_left,
        oudomGuinStar_one_left]
    simp only [map_smul, map_one, bMinusLin_SL_one, smul_zero,
               oudomGuinStar_zero_left, add_zero, smul_eq_mul, mul_one]
  | ι x =>
    -- The substantive case. ε(ι x) = 0 (primitive), so RHS collapses to
    -- (bMinusLin_SL (ι x)) ★ B = (psiA_L a x) ★ B.
    -- LHS reduces via length-argument (bMinusLin_SL_ι_star) to
    -- psiA_L a (circByT_total x B). Equality via psiA_L_circByT_total_eq
    -- (the substantive OG combinatorial identity, currently `sorry`).
    rw [SymmetricAlgebra.algebraMapInv_ι, zero_smul, zero_add,
        bMinusLin_SL_ι_star a x B, psiA_L_circByT_total_eq a x B,
        bMinusLin_SL_ι]
  | mul A₁ A₂ ih₁ ih₂ =>
    -- A = A₁ * A₂. (A₁ · A₂) ★ B has its own associativity (Lemma 2.10:
    -- ★ on S(L) is associative + makes (S(L), ★, Δ) a Hopf algebra).
    -- Reduce via ih₁, ih₂ on the appropriate sub-products.
    sorry
  | add A₁ A₂ ih₁ ih₂ =>
    -- Linearity: ★ left-linear, bMinusLin_SL linear, ε linear.
    rw [oudomGuinStar_add_left, map_add, map_add, map_add,
        oudomGuinStar_add_left, ih₁, ih₂, add_smul]
    abel

end SymAlg

end RootedTree
