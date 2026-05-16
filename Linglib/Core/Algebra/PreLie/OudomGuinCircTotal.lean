/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.PreLie.OudomGuinCircConstruct
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
import Mathlib.Algebra.DirectSum.Module

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

/-! ## §5: Lift to `SymmetricAlgebra` via `RingQuot` quotient

`SymmetricAlgebra R L = RingQuot (SymRel R L)`. To lift `circTTensor T`
through the quotient, we need to show it respects the full `RingQuot.Rel`
closure of `SymRel`, not just `SymRel` itself.

`RingQuot.Rel` has four constructors: `of` (base), `add_left`, `mul_left`,
`mul_right`. For our linear map:
- `of`: handled by `circTTensor_symRel` (Lemma 2.5 at n = 2).
- `add_left`: automatic from linearity.
- `mul_left` / `mul_right`: SUBSTANTIVE. Requires the FULL symmetric-group
  action on `circTMultilinear T n` (Lemma 2.5 across all positions, not
  just adjacent). The argument: `circTTensor T ((a · ι X · ι Y · c)) =
  circTMultilinear T (deg) (a's tuple, X, Y, c's tuple) = (with X ↔ Y
  swapped by `circTMultilinear_symm` applied to the corresponding
  transposition) = circTTensor T ((a · ι Y · ι X · c))`.

Mathlib's `RingQuot.lift` / `RingQuot.liftAlgHom` only handles `RingHom`s
and `AlgHom`s — not arbitrary `LinearMap`s. The mathlib gap here is:
a `RingQuot.liftLinearMap` that takes a linear `f : R →ₗ[T] N` respecting
the base relation `r` (under the multilinear-from-grading structure of
TensorAlgebra) and gives `RingQuot r →ₗ[T] N`.

**Plan for the next session:** prove a generalization of
`circTTensor_symRel` that handles arbitrary embedding of the swap inside
a product `a · (ι X · ι Y) · b → a · (ι Y · ι X) · b`. Then assemble
the four-constructor induction to lift through `Quot.lift` + manual
linearity verification (`AddHom.mk` + `smul`). Estimated ~80-150 LOC.

Alternative: prove `SymmetricAlgebra R L ≃ₗ TensorAlgebra R L ⧸ (ker algHom)`
(via algHom_surjective + quotient iso), then use `Submodule.liftQ`
(simpler API). This requires showing `ker algHom ≤ ker circTTensor T`,
which is the same multilinear-symmetry argument generalized to ideals. -/

/-- The per-T OG operation, on `SymmetricAlgebra R L`. Lands in `L`.

    **Sorry-fenced (Q1b Step 1 final piece).** See §5 docstring for the
    plan. The TensorAlgebra-level operation `circTTensor T` is sorry-free;
    only the quotient lift is pending. -/
noncomputable def circByT_total (T : L) : SymmetricAlgebra R L →ₗ[R] L :=
  sorry

end OudomGuinCircConstruct

end PreLie
