/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.PreLie.OudomGuinCircConstruct
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false

/-!
# Q1b Step 1: assemble per-degree `circT T n` into `circByT_total T : SymmetricAlgebra → L`

For each `n`, `OudomGuinCircConstruct.circTMultilinear R T n` gives a
symmetric multilinear map `(Fin n → L) → L` (sorry-free per Lemma 2.5 at
0.231.112). This file assembles these per-degree pieces into a single
linear map

  `circByT_total T : SymmetricAlgebra R L →ₗ[R] L`

via the **TensorAlgebra detour**:

1. For each `n`, lift `circTMultilinear T n` to a linear map on the
   `n`-th `PiTensorProduct` via `PiTensorProduct.lift`.
2. Assemble across all `n` via `DirectSum.toModule` to get
   `(⨁ n, ⨂[R]^n L) →ₗ[R] L`.
3. Compose with mathlib's `TensorAlgebra.equivDirectSum` to get
   `TensorAlgebra R L →ₗ[R] L`.
4. Show this respects `TensorAlgebra.SymRel` (the symmetric-algebra
   relation `ι(x)·ι(y) ~ ι(y)·ι(x)`) — substantive content uses
   `circTMultilinear_symm` (Lemma 2.5).
5. Lift through the `SymmetricAlgebra = RingQuot SymRel` quotient.

Composed with mathlib's `SymmetricAlgebra.ι : L →ₗ[R] SymmetricAlgebra R L`
on the codomain, this is the per-T operation `ι(T) ○ ·` of the OG ○.
The full `oudomGuinCirc` (Q1b Step 3) extends this to general
left-arguments via OG Prop 2.7.iii.

## Status (2026-05-16)

**Step 1 mostly landed** (~165 LOC, 1 sorry).
- Items 1–3 (per-degree `circTPi`, graded `circTGraded`,
  TensorAlgebra-level `circTTensor`) — sorry-free.
- Item 4 (`circTTensor_symRel`: respects SymRel at n = 2 via
  `circTMultilinear_two_eval` + `RightPreLieRing.assoc_symm'`) — sorry-free.
- Item 5 (`circByT_total`: lift through the `RingQuot` quotient to
  `SymmetricAlgebra R L →ₗ[R] L`) — **sorry-fenced**. Requires either a
  `RingQuot.liftLinearMap` mathlib helper (currently only
  `RingHom`/`AlgHom` versions exist) OR a `Submodule.liftQ`-style
  construction via `ker (algHom : TensorAlgebra → SymmetricAlgebra)`.
  See §5 docstring for the detailed plan.

## References

* @cite{oudom-guin-2008} Def 2.4 + Lemma 2.5 (per-degree symmetry).
-/

namespace PreLie

namespace OudomGuinCircConstruct

open TensorProduct
open scoped DirectSum

variable {R : Type} [CommRing R]
variable {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]

/-! ## §1: Per-degree lift via `PiTensorProduct.lift` -/

/-- Per-degree lift of `circTMultilinear R T n` to the `n`-th
    `PiTensorProduct` (i.e., `⨂[R]^n L`). -/
noncomputable def circTPi (T : L) (n : ℕ) : (⨂[R]^n L) →ₗ[R] L :=
  PiTensorProduct.lift (circTMultilinear R T n)

@[simp]
theorem circTPi_tprod (T : L) (n : ℕ) (g : Fin n → L) :
    circTPi (R := R) T n (PiTensorProduct.tprod R g) = circTMultilinear R T n g := by
  rw [circTPi, PiTensorProduct.lift.tprod]

/-! ## §2: Assembly across degrees via `DirectSum.toModule` -/

/-- Assembly of all `circTPi T n` into a linear map from the direct sum
    of all tensor powers. -/
noncomputable def circTGraded (T : L) : (⨁ n : ℕ, ⨂[R]^n L) →ₗ[R] L :=
  DirectSum.toModule R ℕ L (fun n => circTPi T n)

@[simp]
theorem circTGraded_of (T : L) (n : ℕ) (x : ⨂[R]^n L) :
    circTGraded T (DirectSum.of (fun n : ℕ => ⨂[R]^n L) n x) =
      circTPi T n x := by
  show circTGraded T (DirectSum.lof R ℕ _ n x) = _
  unfold circTGraded
  rw [DirectSum.toModule_lof]

/-! ## §3: Composition with `TensorAlgebra.equivDirectSum` -/

/-- Per-T OG operation, on the `TensorAlgebra` level. Assembled from per-degree
    `circTPi T n` via mathlib's `TensorAlgebra ≃ₐ ⨁_n ⨂[R]^n L`. -/
noncomputable def circTTensor (T : L) : TensorAlgebra R L →ₗ[R] L :=
  (circTGraded T).comp
    (TensorAlgebra.equivDirectSum (R := R) (M := L)).toLinearMap

@[simp]
theorem circTTensor_ι (T : L) (x : L) :
    circTTensor T (TensorAlgebra.ι R x) = T * x := by
  unfold circTTensor
  rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      TensorAlgebra.equivDirectSum_apply, TensorAlgebra.toDirectSum_ι,
      circTGraded_of, circTPi_tprod]
  -- Goal: circTMultilinear R T 1 (fun _ => x) = T * x
  exact circTMultilinear_one_eval T (fun _ => x)

/-- `circTTensor T (TensorAlgebra.tprod R L n f) = circTMultilinear R T n f`. -/
@[simp]
theorem circTTensor_tprod (T : L) (n : ℕ) (f : Fin n → L) :
    circTTensor T (TensorAlgebra.tprod R L n f) = circTMultilinear R T n f := by
  unfold circTTensor
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
             TensorAlgebra.equivDirectSum_apply,
             TensorAlgebra.toDirectSum_tensorPower_tprod,
             circTGraded_of, circTPi_tprod]

/-! ## §4: `circTTensor` respects `SymRel` (consequence of Lemma 2.5)

The substantive content: `circTTensor T (ι(x) * ι(y)) = circTTensor T (ι(y) * ι(x))`,
which reduces to `circTMultilinear T 2 (x, y) = circTMultilinear T 2 (y, x)` via
`circTMultilinear_symm` (Lemma 2.5). -/

/-- `circTTensor T` respects the symmetric-algebra relation `SymRel`. -/
theorem circTTensor_symRel (T : L) {a b : TensorAlgebra R L}
    (h : TensorAlgebra.SymRel R L a b) :
    circTTensor T a = circTTensor T b := by
  -- Single constructor: `mul_comm x y : SymRel (ι R x * ι R y) (ι R y * ι R x)`.
  induction h with
  | mul_comm x y =>
    -- Show: circTTensor T (ι x * ι y) = circTTensor T (ι y * ι x).
    -- Each side unfolds via TensorAlgebra.toDirectSum on a degree-2 tprod to
    -- `circTMultilinear T 2 (vector)`, then `circTMultilinear_two_eval` gives
    -- `(T*a)*b - T*(a*b)`, and `RightPreLieRing.assoc_symm` closes.
    have h_xy_eq : TensorAlgebra.ι R x * TensorAlgebra.ι R y =
                    TensorAlgebra.tprod R L 2 (fun i : Fin 2 => if i = 0 then x else y) := by
      rw [TensorAlgebra.tprod_apply]
      simp [List.ofFn_succ, List.ofFn_zero]
    have h_yx_eq : TensorAlgebra.ι R y * TensorAlgebra.ι R x =
                    TensorAlgebra.tprod R L 2 (fun i : Fin 2 => if i = 0 then y else x) := by
      rw [TensorAlgebra.tprod_apply]
      simp [List.ofFn_succ, List.ofFn_zero]
    rw [h_xy_eq, h_yx_eq]
    unfold circTTensor
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
               TensorAlgebra.equivDirectSum_apply,
               TensorAlgebra.toDirectSum_tensorPower_tprod,
               circTGraded_of, circTPi_tprod]
    -- Goal: circTMultilinear T 2 (x at 0, y at 1) = circTMultilinear T 2 (y at 0, x at 1)
    rw [circTMultilinear_two_eval, circTMultilinear_two_eval]
    -- Goal: (T*x)*y - T*(x*y) = (T*y)*x - T*(y*x).
    have key := RightPreLieRing.assoc_symm' T x y
    simp only [associator] at key
    -- key : T * x * y - T * (x * y) = T * y * x - T * (y * x)
    -- Goal: reduces to `key` after if-reduction on `fun i => if i = 0 then ... else ...`.
    simp only [if_pos, show (1 : Fin 2) ≠ 0 from by decide]
    convert key using 2

/-! ## §5: Lift to `SymmetricAlgebra` via `Submodule.liftQ`

Use `Submodule.liftQ` after expressing `SymmetricAlgebra R L` as
`TensorAlgebra R L ⧸ (ker algHom)` via `LinearMap.quotKerEquivOfSurjective`
(`algHom` is surjective by `RingQuot.mkAlgHom_surjective`).

The kernel-containment `ker algHom ≤ ker (circTTensor T)` is the
substantive content. Reduces to: for any `r, c ∈ TensorAlgebra R L`
and `X, Y ∈ L`,

  `circTTensor T (r * (ι X * ι Y) * c) = circTTensor T (r * (ι Y * ι X) * c)`,

which follows from the FULL symmetric-group action on
`circTMultilinear T n` (Lemma 2.5 across all positions, not just adjacent)
applied to the concatenated tuple `[r's positions, X, Y, c's positions]`. -/

/-- `algHom` (the quotient map) as a `LinearMap`. -/
private noncomputable def algHomL : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
  (SymmetricAlgebra.algHom R L).toLinearMap

private theorem algHomL_surjective :
    Function.Surjective (algHomL (R := R) (L := L)) :=
  SymmetricAlgebra.algHom_surjective R L

/-- **Kernel-containment**: `circTTensor T` vanishes on `ker algHom`.

    **Sorry-fenced.** The substantive content: for any `r, c ∈ TensorAlgebra`
    and `X, Y ∈ L`,
    `circTTensor T (r * (ι X * ι Y) * c) = circTTensor T (r * (ι Y * ι X) * c)`.
    Reduces to `circTMultilinear_symm` applied to the (m+1, m+2)-position
    transposition in the concatenated tuple.

    Proof plan (~80-120 LOC):
    1. Compute `(tprod_m a) * (ι X * ι Y) * (tprod_k b) = tprod_{m+2+k} (Fin.append a (Fin.append ![X,Y] b))`
       via `TensorAlgebra.tprod_apply` + `List` associativity.
    2. `circTTensor T ∘ tprod = circTMultilinear T n` (via the per-degree
       interface: `toDirectSum_tensorPower_tprod` + `circTGraded_of` +
       `circTPi_tprod`).
    3. Swap of X and Y at positions m+1, m+2 in the tuple corresponds to
       `(Equiv.swap (Fin.castSucc (Fin.last (m+1))) (Fin.last (m+2)))` ∘ tuple.
       By `circTMultilinear_symm` applied to this perm, equal.
    4. Extend from tprods to general elements via bilinear linearity (the
       difference is a bilinear map vanishing on tprods, hence everywhere). -/
private theorem circTTensor_vanishes_on_ker (T : L) :
    LinearMap.ker (algHomL (R := R) (L := L)) ≤ LinearMap.ker (circTTensor T) := by
  sorry

/-- The per-T OG operation, on `SymmetricAlgebra R L`. Lands in `L`.

    Built via `Submodule.liftQ` + `LinearMap.quotKerEquivOfSurjective`
    applied to the surjective `algHom : TensorAlgebra → SymmetricAlgebra`. -/
noncomputable def circByT_total (T : L) : SymmetricAlgebra R L →ₗ[R] L :=
  (Submodule.liftQ _ (circTTensor T) (circTTensor_vanishes_on_ker T)).comp
    (LinearMap.quotKerEquivOfSurjective algHomL algHomL_surjective).symm.toLinearMap

end OudomGuinCircConstruct

end PreLie
