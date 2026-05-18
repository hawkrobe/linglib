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

/-- **Nonplanar.insertSum node decomposition** (Multiset.bind form): when the
    left operand is a `Nonplanar.node a A''` and the right operand is `c`, the
    insertion-sum decomposes as one root-graft summand plus a bind over A''
    of "subtree-grafts":

    `insertSum (node a A'') c = node a (c ::ₘ A'') ::ₘ
       A''.bind (fun d => (insertSum d c).map (fun d' => node a (d' ::ₘ A''.erase d)))`

    **Proof plan** (~150-250 LOC):
    1. Pick a planar representative for A'': use `A''.toList.map Quotient.out`
       (a `List (Planar α)`). Set `cs := A''.toList.map Quotient.out`; then
       `Nonplanar.node a A'' = mk (Planar.node a cs)` and
       `A'' = ↑(cs.map mk)`. Pick `c_pl := c.out`; `c = mk c_pl`.
    2. Reduce LHS to planar via `mk_insertSum`:
       `Nonplanar.insertSum (mk (Planar.node a cs)) (mk c_pl) =
        (Planar.insertSum (Planar.node a cs) c_pl).map mk`.
    3. Apply `Planar.insertSum_node`:
       `Planar.insertSum (Planar.node a cs) c_pl =
        Planar.node a (c_pl :: cs) ::ₘ (insertSumList cs c_pl).map (Planar.node a)`.
    4. Distribute `.map mk` over the cons. First summand: `mk (Planar.node a
       (c_pl :: cs)) = Nonplanar.node a (mk c_pl ::ₘ ↑(cs.map mk)) =
       Nonplanar.node a (c ::ₘ A'')` (via `node_mk_planar_list`).
    5. Show the second summand equals the bind: this is a separate list
       induction lemma `insertSumList_bind_lift`. Stated:

       `(insertSumList cs c_pl).map (mk ∘ Planar.node a) =
        ↑(cs.map mk).bind (fun d => (Nonplanar.insertSum d (mk c_pl)).map
          (fun d' => Nonplanar.node a (d' ::ₘ (↑(cs.map mk)).erase d)))`

       Induct on `cs`:
       - nil: both sides 0. ✓
       - cons e cs': use `Planar.insertSumList_cons` + `Multiset.cons_bind`
         to split each side into "graft at first child" + "graft deeper".
         For the first summand: equate
         `(Planar.insertSum e c_pl).map (mk ∘ Planar.node a ∘ (·:: cs'))`
         with `(Nonplanar.insertSum (mk e) (mk c_pl)).map (fun d' =>
         Nonplanar.node a (d' ::ₘ ↑(cs'.map mk)))`. (Uses erase_cons_head
         to simplify the multiset erase: `(mk e ::ₘ A_cs').erase (mk e) = A_cs'`.)
         For the second summand: apply IH on cs', but need to handle the new
         `mk e` factor. Since `(mk e ::ₘ A_cs').erase d` for `d ∈ A_cs'`:
         if `d = mk e` (duplicate), this is `A_cs'`; if `d ≠ mk e`, this is
         `mk e ::ₘ A_cs'.erase d`. The IH-as-stated may need adjustment.

    **Alternative**: state and prove via `Pathed.vertices` path-indexed form
    (using `insertSum_eq_coe_map_insertAt`). May be cleaner. -/
private theorem insertSum_node_decompose [DecidableEq (Nonplanar α)]
    (a : α) (A'' : Multiset (Nonplanar α)) (c : Nonplanar α) :
    Nonplanar.insertSum (Nonplanar.node a A'') c =
      Nonplanar.node a (c ::ₘ A'') ::ₘ
      A''.bind (fun d => (Nonplanar.insertSum d c).map
        (fun d' => Nonplanar.node a (d' ::ₘ A''.erase d))) := by
  -- TODO: descend through planar representatives + list induction (see docstring).
  sorry

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
