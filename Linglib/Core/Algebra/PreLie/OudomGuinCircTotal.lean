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
import Mathlib.Data.List.OfFn

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
5. Lift through the `SymmetricAlgebra = (ringConGen SymRel).Quotient` quotient.

Composed with mathlib's `SymmetricAlgebra.ι : L →ₗ[R] SymmetricAlgebra R L`
on the codomain, this is the per-T operation `ι(T) ○ ·` of the OG ○.
The full `oudomGuinCirc` (Q1b Step 3) extends this to general
left-arguments via OG Prop 2.7.iii.

## Status (2026-05-16)

**Step 1 fully landed sorry-free** (~370 LOC).
- Items 1–3 (per-degree `circTPi`, graded `circTGraded`,
  TensorAlgebra-level `circTTensor`) — sorry-free.
- Item 4 (`circTTensor_symRel`: respects SymRel at n = 2 via
  `circTMultilinear_two_eval` + `RightPreLieRing.assoc_symm'`) — sorry-free.
- Item 5 (`circByT_total`: lift through the `RingCon` quotient to
  `SymmetricAlgebra R L →ₗ[R] L`) — sorry-free via `Submodule.liftQ` +
  `LinearMap.quotKerEquivOfSurjective` on surjective `algHomL`. The kernel
  containment `ker algHomL ≤ ker (circTTensor T)` is proven through:
  (a) `TA_linearMap_ext_tprod` (helper — linear maps from `TensorAlgebra`
  agreeing on tprods are equal, via `equivDirectSum` + `DirectSum.linearMap_ext`
  + `PiTensorProduct.ext`);
  (b) `circTTensor_swap_general` (bilinear extension of `circTTensor_swap_tprod`
  to general `r, d ∈ TensorAlgebra`);
  (c) `RingConGen.Rel` induction with the strong motive
  `∀ r d, circTTensor T (r * z₁ * d) = circTTensor T (r * z₂ * d)`,
  closing under `add`/`mul` via associativity + additivity.

## References

* [oudom-guin-2008] Def 2.4 + Lemma 2.5 (per-degree symmetry).
-/

namespace PreLie

namespace OudomGuinCircConstruct

open TensorProduct
open scoped DirectSum

variable {R : Type*} [CommRing R]
variable {L : Type*} [RightPreLieRing L] [RightPreLieAlgebra R L]

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

/-! ### §3.A: tprod multiplication

`(tprod_m a) * (tprod_n b) = tprod_{m+n} (Fin.append a b)`. Derived from
`TensorAlgebra.tprod_apply` (which expresses `tprod` as `List.prod` of
`ι`s) + `List.prod_append` + `List.ofFn_fin_append`. -/

/-- The product of two tprods is the tprod of the concatenated tuple. -/
theorem tprod_mul_tprod (m n : ℕ) (a : Fin m → L) (b : Fin n → L) :
    (TensorAlgebra.tprod R L m a) * (TensorAlgebra.tprod R L n b) =
      TensorAlgebra.tprod R L (m + n) (Fin.append a b) := by
  have h_append :
      (Fin.append (fun i => TensorAlgebra.ι R (a i))
                  (fun i => TensorAlgebra.ι R (b i)) :
                  Fin (m + n) → TensorAlgebra R L) =
      (fun i => TensorAlgebra.ι R (Fin.append a b i)) := by
    funext i
    induction i using Fin.addCases with
    | left j => simp [Fin.append_left]
    | right j => simp [Fin.append_right]
  simp only [TensorAlgebra.tprod_apply, ← List.prod_append, ← List.ofFn_fin_append, h_append]

/-- `ι R x = tprod 1 (fun _ => x)`. -/
theorem ι_eq_tprod_one (x : L) :
    TensorAlgebra.ι R x = TensorAlgebra.tprod R L 1 (fun _ => x) := by
  rw [TensorAlgebra.tprod_apply]
  simp

/-! ### §3.B: Swap-in-product lemma on tprods

The KEY substantive lemma reducing the kernel-containment to Lemma 2.5.
For tprods of `a, b` with an `ι X * ι Y` insert: the swap of X and Y
corresponds to a transposition of two adjacent positions in the
concatenated tuple, which `circTMultilinear_symm` makes invariant. -/

/-- Express `(tprod_m a) * (ι X * ι Y) * (tprod_n b)` as a single
    `tprod_{m+2+n}` over the concatenated tuple. -/
private theorem tprod_mul_ι_pair_mul_tprod
    (m n : ℕ) (a : Fin m → L) (b : Fin n → L) (X Y : L) :
    (TensorAlgebra.tprod R L m a) *
      (TensorAlgebra.ι R X * TensorAlgebra.ι R Y) *
      (TensorAlgebra.tprod R L n b) =
    TensorAlgebra.tprod R L (m + 2 + n)
      (Fin.append (Fin.append a
                    (Fin.append (fun _ : Fin 1 => X) (fun _ : Fin 1 => Y)))
                  b) := by
  rw [ι_eq_tprod_one X, ι_eq_tprod_one Y]
  rw [tprod_mul_tprod 1 1, tprod_mul_tprod m (1 + 1), tprod_mul_tprod (m + 2) n]

/-- **Swap-in-product on tprods**: invariance under swap of the X, Y
    factors inserted between tprods.

    Reduces (via `tprod_mul_ι_pair_mul_tprod` + `circTTensor_tprod`) to
    `circTMultilinear_symm` applied to the transposition of positions
    `m, m+1` in `Fin (m+2+n)`. -/
private theorem circTTensor_swap_tprod (T : L)
    {m n : ℕ} (a : Fin m → L) (b : Fin n → L) (X Y : L) :
    circTTensor T
        ((TensorAlgebra.tprod R L m a) *
          (TensorAlgebra.ι R X * TensorAlgebra.ι R Y) *
          (TensorAlgebra.tprod R L n b)) =
    circTTensor T
        ((TensorAlgebra.tprod R L m a) *
          (TensorAlgebra.ι R Y * TensorAlgebra.ι R X) *
          (TensorAlgebra.tprod R L n b)) := by
  rw [tprod_mul_ι_pair_mul_tprod, tprod_mul_ι_pair_mul_tprod,
      circTTensor_tprod, circTTensor_tprod]
  classical
  -- σ swaps the two adjacent positions where X and Y sit (positions m, m+1
  -- in `Fin (m+2+n)`), expressed via the addCases structure.
  set σ : Equiv.Perm (Fin (m + 2 + n)) :=
    Equiv.swap
      (Fin.castAdd n (Fin.natAdd m (Fin.castAdd 1 (0 : Fin 1))))
      (Fin.castAdd n (Fin.natAdd m (Fin.natAdd 1 (0 : Fin 1)))) with hσ_def
  -- Key: `tuple_YX = fun i => tuple_XY (σ i)`. Pointwise by 4-case Fin.addCases.
  have h_tuple :
      (Fin.append (Fin.append a
            (Fin.append (fun _ : Fin 1 => Y) (fun _ : Fin 1 => X))) b) =
      (fun i => (Fin.append (Fin.append a
            (Fin.append (fun _ : Fin 1 => X) (fun _ : Fin 1 => Y))) b) (σ i)) := by
    funext i
    induction i using Fin.addCases with
    | left j =>
      induction j using Fin.addCases with
      | left j' =>
        -- Position is `Fin.castAdd n (Fin.castAdd 2 j')`, value `j'.val < m`.
        -- σ fixes it; both tuples give `a j'`.
        have hσi : σ (Fin.castAdd n (Fin.castAdd 2 j' : Fin (m + 2))) =
                   Fin.castAdd n (Fin.castAdd 2 j') := by
          rw [hσ_def, Equiv.swap_apply_of_ne_of_ne]
          · apply Fin.ne_of_val_ne
            simp [Fin.val_castAdd, Fin.val_natAdd]; omega
          · apply Fin.ne_of_val_ne
            simp [Fin.val_castAdd, Fin.val_natAdd]; omega
        simp only [hσi, Fin.append_left]
      | right k' =>
        induction k' using Fin.addCases with
        | left z =>
          -- Position is `Fin.castAdd n (Fin.natAdd m (Fin.castAdd 1 0))` = posX.
          -- σ posX = posY; LHS = tuple_YX posX = Y; RHS = tuple_XY posY = Y.
          obtain rfl : z = 0 := Subsingleton.elim _ _
          have hσi : σ (Fin.castAdd n (Fin.natAdd m (Fin.castAdd 1 (0 : Fin 1)))) =
                     Fin.castAdd n (Fin.natAdd m (Fin.natAdd 1 (0 : Fin 1))) := by
            rw [hσ_def]; exact Equiv.swap_apply_left _ _
          simp only [hσi, Fin.append_left, Fin.append_right]
        | right z =>
          -- Position is `Fin.castAdd n (Fin.natAdd m (Fin.natAdd 1 0))` = posY.
          obtain rfl : z = 0 := Subsingleton.elim _ _
          have hσi : σ (Fin.castAdd n (Fin.natAdd m (Fin.natAdd 1 (0 : Fin 1)))) =
                     Fin.castAdd n (Fin.natAdd m (Fin.castAdd 1 (0 : Fin 1))) := by
            rw [hσ_def]; exact Equiv.swap_apply_right _ _
          simp only [hσi, Fin.append_left, Fin.append_right]
    | right k =>
      -- Position is `Fin.natAdd (m+2) k`, value `m+2+k.val ≥ m+2`. σ fixes it.
      have hσi : σ (Fin.natAdd (m + 2) k) = Fin.natAdd (m + 2) k := by
        rw [hσ_def, Equiv.swap_apply_of_ne_of_ne]
        · apply Fin.ne_of_val_ne
          simp [Fin.val_castAdd, Fin.val_natAdd]; omega
        · apply Fin.ne_of_val_ne
          simp [Fin.val_castAdd, Fin.val_natAdd]; omega
      simp only [hσi, Fin.append_right]
  -- Apply circTMultilinear_symm: `circTMultilinear T n (fun i => g (σ i)) = circTMultilinear T n g`.
  rw [h_tuple]
  have h_symm := circTMultilinear_symm R T (m + 2 + n) σ
  have h_apply :=
    congr_fun (congr_arg (fun (f : MultilinearMap R _ L) => f.toFun) h_symm)
      (Fin.append (Fin.append a
        (Fin.append (fun _ : Fin 1 => X) (fun _ : Fin 1 => Y))) b)
  exact h_apply.symm

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
    convert key using 2 <;> simp

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
noncomputable def algHomL : TensorAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
  (SymmetricAlgebra.algHom R L).toLinearMap

theorem algHomL_surjective :
    Function.Surjective (algHomL (R := R) (L := L)) :=
  SymmetricAlgebra.algHom_surjective R L

/-! ### §5.A: Helper — linear maps from `TensorAlgebra` agree iff they agree on tprods

Bilinear extension lemma: two linear maps `TA → L` that agree on
`TensorAlgebra.tprod R L n a` for every `n, a` are equal. The proof transfers
through `TensorAlgebra.equivDirectSum` (algebra equivalence to `⨁ⁿ ⨂ⁿ L`),
then uses `DirectSum.linearMap_ext` (per-summand check) and
`PiTensorProduct.ext` (per-tprod check) — both `@[ext]` lemmas in mathlib.
-/

lemma TA_linearMap_ext_tprod {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : TensorAlgebra R L →ₗ[R] N}
    (h : ∀ n (a : Fin n → L),
      f (TensorAlgebra.tprod R L n a) = g (TensorAlgebra.tprod R L n a)) :
    f = g := by
  -- Transfer through `equivDirectSum`: `f = g ↔ f ∘ e.symm = g ∘ e.symm`.
  set e : TensorAlgebra R L ≃ₐ[R] ⨁ n, ⨂[R]^n L := TensorAlgebra.equivDirectSum
  suffices h_eq : f.comp e.symm.toLinearMap = g.comp e.symm.toLinearMap by
    ext z
    have := congrArg (fun (φ : (⨁ n, ⨂[R]^n L) →ₗ[R] N) => φ (e z)) h_eq
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
               AlgEquiv.symm_apply_apply] at this
    exact this
  -- Per-summand + per-tprod check via the two `@[ext]` lemmas.
  ext n a
  -- Goal: (f.comp e.symm.toLinearMap).comp (lof R ℕ _ n) (tprod R a) = same with g
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
             AlgEquiv.toLinearMap_apply]
  have h_e_symm :
      e.symm (DirectSum.lof R ℕ (fun n => ⨂[R]^n L) n (PiTensorProduct.tprod R a)) =
      TensorAlgebra.tprod R L n a := by
    rw [DirectSum.lof_eq_of]
    exact TensorAlgebra.ofDirectSum_of_tprod (R := R) (M := L) a
  rw [h_e_symm]
  exact h n a

/-! ### §5.B: Bilinear extension of `circTTensor_swap_tprod`

`circTTensor T (r * (ι X * ι Y) * d) = circTTensor T (r * (ι Y * ι X) * d)`
for all `r, d ∈ TensorAlgebra R L`. Proven by bilinear extension from the
tprod case (`circTTensor_swap_tprod`) via two applications of
`TA_linearMap_ext_tprod`. -/

private lemma circTTensor_swap_general (T : L) (X Y : L) (r d : TensorAlgebra R L) :
    circTTensor T (r * (TensorAlgebra.ι R X * TensorAlgebra.ι R Y) * d) =
    circTTensor T (r * (TensorAlgebra.ι R Y * TensorAlgebra.ι R X) * d) := by
  -- The linear map `r' ↦ circTTensor T (r' * w * d)` for fixed d, where w = ι X * ι Y,
  -- equals the same with w' = ι Y * ι X.
  -- Use TA_linearMap_ext_tprod twice (for r' first, then for d').
  -- Build the linear maps via composition with `LinearMap.mulRight`.
  suffices h_fixed_d : ∀ d' : TensorAlgebra R L,
      (circTTensor T).comp ((LinearMap.mulRight R d').comp
        (LinearMap.mulRight R (TensorAlgebra.ι R X * TensorAlgebra.ι R Y))) =
      (circTTensor T).comp ((LinearMap.mulRight R d').comp
        (LinearMap.mulRight R (TensorAlgebra.ι R Y * TensorAlgebra.ι R X))) by
    have := congrArg (fun (φ : TensorAlgebra R L →ₗ[R] L) => φ r) (h_fixed_d d)
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at this
    exact this
  intro d'
  -- Extend over d' first (use TA_linearMap_ext_tprod on the d' variable).
  -- For fixed r', the map d' ↦ ... is also linear, via a different composition.
  -- Strategy: prove the equality of the curried bilinear maps, by ext on r' then on d'.
  apply TA_linearMap_ext_tprod
  intro m a
  -- Goal: circTTensor T (tprod_m a * w * d') = circTTensor T (tprod_m a * w' * d')
  -- where w = ι X * ι Y, w' = ι Y * ι X.
  -- For fixed tprod_m a, the map d' ↦ circTTensor T (tprod * w * d') is linear in d'.
  -- Vanishes on tprods d' by circTTensor_swap_tprod.
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
  -- Now: circTTensor T (tprod_m a * w * d') = circTTensor T (tprod_m a * w' * d')
  -- Use TA_linearMap_ext_tprod on the d' direction.
  have h_d : ∀ d'' : TensorAlgebra R L,
      circTTensor T (TensorAlgebra.tprod R L m a *
        (TensorAlgebra.ι R X * TensorAlgebra.ι R Y) * d'') =
      circTTensor T (TensorAlgebra.tprod R L m a *
        (TensorAlgebra.ι R Y * TensorAlgebra.ι R X) * d'') := by
    intro d''
    -- Extend over d'' via TA_linearMap_ext_tprod on the d''-variable map.
    have h_eq : (circTTensor T).comp ((LinearMap.mulLeft R
        (TensorAlgebra.tprod R L m a *
          (TensorAlgebra.ι R X * TensorAlgebra.ι R Y)))) =
      (circTTensor T).comp ((LinearMap.mulLeft R
        (TensorAlgebra.tprod R L m a *
          (TensorAlgebra.ι R Y * TensorAlgebra.ι R X)))) := by
      apply TA_linearMap_ext_tprod
      intro n b
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      -- Goal: circTTensor T (tprod_m a * (ι X * ι Y) * tprod_n b) =
      --       circTTensor T (tprod_m a * (ι Y * ι X) * tprod_n b)
      exact circTTensor_swap_tprod T a b X Y
    have := congrArg (fun (φ : TensorAlgebra R L →ₗ[R] L) => φ d'') h_eq
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at this
    exact this
  exact h_d d'

/-! ### §5.C: Kernel containment via `RingConGen.Rel` induction

`ker algHomL ≤ ker (circTTensor T)`. `SymmetricAlgebra R L` is the quotient of
`TensorAlgebra R L` by the ring congruence `symRingCon R L = ringConGen SymRel`,
whose underlying relation is `RingConGen.Rel SymRel` — already closed under
`refl`/`symm`/`trans` (unlike `RingQuot.Rel`, which needed a separate `EqvGen`
wrapper). `algHomL z = 0` iff `RingConGen.Rel SymRel z 0` (via `RingCon.eq`).
Via `RingConGen.Rel` induction with a strong motive
(`∀ r d, circTTensor T (r * z₁ * d) = circTTensor T (r * z₂ * d)`), the
algebraic closure under `add` and `mul` is preserved, and the base case is
`circTTensor_swap_general`. -/

/-- Strong respects-relation property: invariant under `RingConGen.Rel SymRel`-
    related elements, even after wrapping by arbitrary `r * · * d`. -/
private lemma circTTensor_resp_Rel_strong (T : L) :
    ∀ {z₁ z₂ : TensorAlgebra R L},
    RingConGen.Rel (TensorAlgebra.SymRel R L) z₁ z₂ →
    ∀ r d : TensorAlgebra R L,
      circTTensor T (r * z₁ * d) = circTTensor T (r * z₂ * d) := by
  intro z₁ z₂ h
  induction h with
  | of x y h_sym =>
    induction h_sym with
    | mul_comm X Y =>
      intro r d
      exact circTTensor_swap_general T X Y r d
  | refl x =>
    intro r d; rfl
  | symm _ ih =>
    intro r d
    exact (ih r d).symm
  | trans _ _ ih₁ ih₂ =>
    intro r d
    exact (ih₁ r d).trans (ih₂ r d)
  | @add w x y z _ _ ih₁ ih₂ =>
    intro r d
    -- (w + y) ~ (x + z) with Rel w x, Rel y z.
    -- r * (w + y) * d = r * w * d + r * y * d
    simp only [mul_add, add_mul, map_add, ih₁ r d, ih₂ r d]
  | @mul w x y z _ _ ih₁ ih₂ =>
    intro r d
    -- (w * y) ~ (x * z) with Rel w x, Rel y z. Chain: fix d' = y * d first (ih₁),
    -- then fix r' = r * x (ih₂).
    have hL : r * (w * y) * d = r * w * (y * d) := by simp only [mul_assoc]
    have hR : r * (x * z) * d = r * x * z * d := by simp only [mul_assoc]
    have hM : r * x * (y * d) = r * x * y * d := by simp only [mul_assoc]
    rw [hL, hR, ih₁ r (y * d), hM, ih₂ (r * x) d]

/-- `circTTensor T` respects `RingConGen.Rel SymRel` (pointwise). -/
private lemma circTTensor_resp_Rel (T : L) {z₁ z₂ : TensorAlgebra R L}
    (h : RingConGen.Rel (TensorAlgebra.SymRel R L) z₁ z₂) :
    circTTensor T z₁ = circTTensor T z₂ := by
  have := circTTensor_resp_Rel_strong T h 1 1
  simpa using this

/-- **Kernel-containment**: `circTTensor T` vanishes on `ker algHomL`.

    Proof: `algHomL z = algHomL 0` iff `(z : SymmetricAlgebra R L) = ↑(0 : TensorAlgebra R L)`
    iff `RingConGen.Rel SymRel z 0` (via `symRingCon = ringConGen SymRel` and
    `RingCon.eq`). Apply `circTTensor_resp_Rel` and conclude
    `circTTensor T z = circTTensor T 0 = 0`. -/
private theorem circTTensor_vanishes_on_ker (T : L) :
    LinearMap.ker (algHomL (R := R) (L := L)) ≤ LinearMap.ker (circTTensor T) := by
  intro z hz
  rw [LinearMap.mem_ker] at hz ⊢
  -- algHomL z = 0 = algHomL 0
  rw [← (algHomL (R := R) (L := L)).map_zero] at hz
  -- algHomL is the canonical map into the `symRingCon`-quotient; extract the congruence.
  have h_coe : (z : SymmetricAlgebra R L) = ((0 : TensorAlgebra R L) : SymmetricAlgebra R L) := hz
  have h_rel : RingConGen.Rel (TensorAlgebra.SymRel R L) z 0 :=
    (TensorAlgebra.symRingCon R L).eq.mp h_coe
  rw [circTTensor_resp_Rel T h_rel, (circTTensor T).map_zero]

/-- The per-T OG operation, on `SymmetricAlgebra R L`. Lands in `L`.

    Built via `Submodule.liftQ` + `LinearMap.quotKerEquivOfSurjective`
    applied to the surjective `algHom : TensorAlgebra → SymmetricAlgebra`. -/
noncomputable def circByT_total (T : L) : SymmetricAlgebra R L →ₗ[R] L :=
  (Submodule.liftQ _ (circTTensor T) (circTTensor_vanishes_on_ker T)).comp
    (LinearMap.quotKerEquivOfSurjective algHomL algHomL_surjective).symm.toLinearMap

/-! ## §6: `T`-linearity (Q1b Step 2.1)

Each of `circTMultilinear`, `circTTensor`, `circByT_total` is linear in
its `T : L` argument. Proven by descent: induction at the multilinear
level, then transferred through `PiTensorProduct.lift`, `DirectSum.toModule`,
`equivDirectSum`, and the `Submodule.liftQ` descent.

The final output `circByT_totalLM : L →ₗ[R] SymmetricAlgebra R L →ₗ[R] L`
is the input to `SymmetricAlgebra.lift` (Q1b Step 2.2). -/

/-- `circTMultilinear R T n` is additive in `T`. Induction on `n`. -/
private theorem circTMultilinear_T_add (n : ℕ) (T₁ T₂ : L) :
    circTMultilinear R (T₁ + T₂) n = circTMultilinear R T₁ n + circTMultilinear R T₂ n := by
  induction n with
  | zero =>
    ext f
    simp only [circTMultilinear_zero, add_apply]
  | succ n ih =>
    ext f
    simp only [add_apply]
    rw [circTMultilinear_succ, circTMultilinear_succ, circTMultilinear_succ]
    have h_init : ∀ (g : Fin n → L),
        circTMultilinear R (T₁ + T₂) n g =
        circTMultilinear R T₁ n g + circTMultilinear R T₂ n g := by
      intro g; rw [ih]; rfl
    rw [h_init, add_mul]
    have h_sum :
        (∑ i : Fin n, circTMultilinear R (T₁ + T₂) n
            (Function.update (Fin.init f) i (Fin.init f i * f (Fin.last n)))) =
        (∑ i : Fin n, circTMultilinear R T₁ n
            (Function.update (Fin.init f) i (Fin.init f i * f (Fin.last n)))) +
        (∑ i : Fin n, circTMultilinear R T₂ n
            (Function.update (Fin.init f) i (Fin.init f i * f (Fin.last n)))) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => h_init _)
    rw [h_sum]
    abel

/-- `circTMultilinear R T n` is `R`-homogeneous in `T`. Induction on `n`. -/
private theorem circTMultilinear_T_smul (n : ℕ) (r : R) (T : L) :
    circTMultilinear R (r • T) n = r • circTMultilinear R T n := by
  induction n with
  | zero =>
    ext f
    simp only [circTMultilinear_zero, smul_apply]
  | succ n ih =>
    ext f
    simp only [smul_apply]
    rw [circTMultilinear_succ, circTMultilinear_succ]
    have h_init : ∀ (g : Fin n → L),
        circTMultilinear R (r • T) n g = r • circTMultilinear R T n g := by
      intro g; rw [ih]; rfl
    rw [h_init, smul_mul_assoc]
    have h_sum :
        (∑ i : Fin n, circTMultilinear R (r • T) n
            (Function.update (Fin.init f) i (Fin.init f i * f (Fin.last n)))) =
        r • (∑ i : Fin n, circTMultilinear R T n
            (Function.update (Fin.init f) i (Fin.init f i * f (Fin.last n)))) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun i _ => h_init _)
    rw [h_sum, ← smul_sub]

/-- `circTTensor` is additive in `T`. Via `TA_linearMap_ext_tprod`. -/
private theorem circTTensor_T_add (T₁ T₂ : L) :
    circTTensor (R := R) (T₁ + T₂) = circTTensor T₁ + circTTensor T₂ := by
  apply TA_linearMap_ext_tprod
  intro n a
  rw [circTTensor_tprod, circTMultilinear_T_add, add_apply,
      LinearMap.add_apply, circTTensor_tprod, circTTensor_tprod]

/-- `circTTensor` is `R`-homogeneous in `T`. Via `TA_linearMap_ext_tprod`. -/
private theorem circTTensor_T_smul (r : R) (T : L) :
    circTTensor (R := R) (r • T) = r • circTTensor T := by
  apply TA_linearMap_ext_tprod
  intro n a
  rw [circTTensor_tprod, circTMultilinear_T_smul, smul_apply,
      LinearMap.smul_apply, circTTensor_tprod]

/-- **Key characterization**: `circByT_total T` agrees with `circTTensor T`
    when precomposed with `algHomL`. -/
theorem circByT_total_comp_algHomL (T : L) :
    (circByT_total T).comp (algHomL (R := R) (L := L)) = circTTensor T := by
  ext z
  unfold circByT_total
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
             LinearMap.quotKerEquivOfSurjective_symm_apply,
             Submodule.liftQ_apply]

/-- `circByT_total` is additive in `T`. Via the algHomL characterization +
    surjectivity. -/
theorem circByT_total_T_add (T₁ T₂ : L) :
    circByT_total (R := R) (T₁ + T₂) =
      circByT_total T₁ + circByT_total T₂ := by
  ext B
  obtain ⟨z, hz⟩ := algHomL_surjective B
  subst hz
  have h₁ := congrArg (fun (f : TensorAlgebra R L →ₗ[R] L) => f z)
                      (circByT_total_comp_algHomL (R := R) (T₁ + T₂))
  have h₂ := congrArg (fun (f : TensorAlgebra R L →ₗ[R] L) => f z)
                      (circByT_total_comp_algHomL (R := R) T₁)
  have h₃ := congrArg (fun (f : TensorAlgebra R L →ₗ[R] L) => f z)
                      (circByT_total_comp_algHomL (R := R) T₂)
  simp only [LinearMap.comp_apply] at h₁ h₂ h₃
  rw [h₁, circTTensor_T_add, LinearMap.add_apply, ← h₂, ← h₃, LinearMap.add_apply]

/-- `circByT_total` is `R`-homogeneous in `T`. -/
theorem circByT_total_T_smul (r : R) (T : L) :
    circByT_total (R := R) (r • T) = r • circByT_total T := by
  ext B
  obtain ⟨z, hz⟩ := algHomL_surjective B
  subst hz
  have h₁ := congrArg (fun (f : TensorAlgebra R L →ₗ[R] L) => f z)
                      (circByT_total_comp_algHomL (R := R) (r • T))
  have h₂ := congrArg (fun (f : TensorAlgebra R L →ₗ[R] L) => f z)
                      (circByT_total_comp_algHomL (R := R) T)
  simp only [LinearMap.comp_apply] at h₁ h₂
  rw [h₁, circTTensor_T_smul, LinearMap.smul_apply, ← h₂, LinearMap.smul_apply]

/-- **`circByT_total` as a linear map in `T`**. Input to `SymmetricAlgebra.lift`
    (Q1b Step 2.2). -/
noncomputable def circByT_totalLM :
    L →ₗ[R] (SymmetricAlgebra R L →ₗ[R] L) where
  toFun := circByT_total
  map_add' := circByT_total_T_add
  map_smul' := circByT_total_T_smul

@[simp]
theorem circByT_totalLM_apply (T : L) (B : SymmetricAlgebra R L) :
    circByT_totalLM (R := R) T B = circByT_total T B := rfl

/-! ### §6.A: Base-case evaluations of `circByT_total`

For Prop 2.7 (i) / `circ_one_right` (Q1b Step 3.1): need
`circByT_total T 1 = T`. Traces through the construction chain
`circByT_total → circTTensor → circTGraded → circTPi → circTMultilinear`
to the degree-0 base case `circTMultilinear T 0 = T`. -/

/-- `circTTensor T 1 = T`. Base case via `DirectSum.one_def` + `TensorPower.gOne_def`. -/
theorem circTTensor_one (T : L) :
    circTTensor (R := R) T 1 = T := by
  unfold circTTensor
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one,
             DirectSum.one_def, TensorPower.gOne_def,
             circTGraded_of, circTPi_tprod, circTMultilinear_zero]

/-- `circByT_total T 1 = T`. The `T ○ 1 = T` base case (OG Def 2.4 base).
    Via `circByT_total_comp_algHomL` + `algHomL 1 = 1` + `circTTensor_one`. -/
theorem circByT_total_one (T : L) :
    circByT_total (R := R) T 1 = T := by
  -- algHomL 1 = 1 (algHom preserves 1).
  have h_alg_one : algHomL (R := R) (L := L) (1 : TensorAlgebra R L) =
                   (1 : SymmetricAlgebra R L) := by
    show (SymmetricAlgebra.algHom R L) (1 : TensorAlgebra R L) = 1
    exact map_one _
  have h := congrArg (fun (f : TensorAlgebra R L →ₗ[R] L) => f (1 : TensorAlgebra R L))
                     (circByT_total_comp_algHomL (R := R) T)
  simp only [LinearMap.comp_apply, h_alg_one] at h
  rw [h, circTTensor_one]

/-- `circByT_total T (ι X) = T * X`. The degree-1 case (`T ○ X = T · X`
    in the pre-Lie product on L). -/
theorem circByT_total_ι (T X : L) :
    circByT_total (R := R) T (SymmetricAlgebra.ι R L X) = T * X := by
  have h_alg_ι : algHomL (R := R) (L := L) (TensorAlgebra.ι R X) =
                 SymmetricAlgebra.ι R L X := rfl
  have h := congrArg (fun (f : TensorAlgebra R L →ₗ[R] L) => f (TensorAlgebra.ι R X))
                     (circByT_total_comp_algHomL (R := R) T)
  simp only [LinearMap.comp_apply, h_alg_ι] at h
  rw [h, circTTensor_ι]

end OudomGuinCircConstruct

end PreLie
