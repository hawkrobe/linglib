/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Merge.MinimalYieldGrading
import Linglib.Core.Algebra.RootedTree.HopfAlgebraNonplanar

/-!
# The Minimal-Yield character ϕt : H → Laurent series (MCB Prop. 3.5.3, Lemma 3.5.5)
[marcolli-chomsky-berwick-2025] §3.5.2.2

The character `ϕt` of MCB Prop. 3.5.3 (eq. 3.5.6) as an **algebra homomorphism** from the Hopf
algebra `H = ConnesKreimer R (Nonplanar α)` of nonplanar rooted forests to the Laurent-series ring,
in the **lean t-grading model**: rather than coefficients in the full algebra `DM` of free Merge
derivations (Def. 3.5.1), we record only the grading `tᵟ`. With `δ = δα`, the grading of the
canonical construction `L(F) → F` is exactly `α(F) = Forest.alpha F` (the leaves carry `α = 0`), so

  `ϕt(F) = t^{α(F)}`.

Since `α(F) ≥ 0`, `ϕt` lands entirely in the **nonpolar** subring `DM[[t]] = (1 − R)·DM[t⁻¹][[t]]`
(**MCB Lemma 3.5.5**): `R·ϕt(F) = 0` for every forest `F`. This is exactly why `ϕt` alone cannot
detect Sideward Merge — the intermediate-derivation character `ψt` (Cor. 3.5.4) and the full Birkhoff
factorization (Prop. 3.5.6) are needed to separate Internal/External from Sideward Merge.

## Main definitions

- `Minimalist.Merge.gradingChar`: the algebra hom `ϕt : H →ₐ[R] LaurentSeries R`.

## References

[marcolli-chomsky-berwick-2025] (Prop. 3.5.3, eq. 3.5.6, Lemma 3.5.5)
-/

namespace Minimalist.Merge

open RootedTree RootedTree.ConnesKreimer LaurentSeries

variable {α : Type*} {R : Type*} [CommRing R]

/-! ### `gradeMonomial` is a multiplicative grading -/

@[simp] theorem gradeMonomial_zero : gradeMonomial (A := R) 0 = 1 := rfl

/-- `tᵃ · tᵇ = tᵃ⁺ᵇ`: the grading monomials multiply by adding exponents. -/
theorem gradeMonomial_mul (a b : ℤ) :
    gradeMonomial (A := R) a * gradeMonomial b = gradeMonomial (a + b) := by
  rw [gradeMonomial, gradeMonomial, gradeMonomial, HahnSeries.single_mul_single, one_mul]

/-! ### The character ϕt (MCB Prop. 3.5.3, `δα` grading) -/

/-- The per-tree value of `ϕt`: `t^{α(T)} = t^{accCount T}` (the `δα` grading of `L(T) → T`). -/
noncomputable def gradingMonomialTree (T : Nonplanar α) : LaurentSeries R :=
  gradeMonomial (T.accCount : ℤ)

/-- `ϕt` extended multiplicatively to forests (`ϕt(F ⊔ F') = ϕt(F)·ϕt(F')`); mirrors
    `antipodeMonoidHomN`. -/
noncomputable def gradingMonoidHom :
    Multiplicative (Forest (Nonplanar α)) →* LaurentSeries R where
  toFun F := (F.toAdd.map (gradingMonomialTree (R := R))).prod
  map_one' := by
    show ((0 : Forest (Nonplanar α)).map _).prod = 1
    rw [Multiset.map_zero, Multiset.prod_zero]
  map_mul' F G := by
    show ((F.toAdd + G.toAdd).map (gradingMonomialTree (R := R))).prod =
         (F.toAdd.map _).prod * (G.toAdd.map _).prod
    rw [Multiset.map_add, Multiset.prod_add]

/-- **The Minimal-Yield character** `ϕt : H →ₐ[R] DM[t⁻¹][[t]]` (MCB Prop. 3.5.3, eq. 3.5.6) in the
    lean t-grading model. -/
noncomputable def gradingChar : ConnesKreimer R (Nonplanar α) →ₐ[R] LaurentSeries R :=
  AddMonoidAlgebra.lift R (LaurentSeries R) (Forest (Nonplanar α)) gradingMonoidHom

@[simp] theorem gradingChar_apply_of' (F : Forest (Nonplanar α)) :
    gradingChar (R := R) (of' F) = (F.map (gradingMonomialTree (R := R))).prod := by
  show AddMonoidAlgebra.lift R (LaurentSeries R) (Forest (Nonplanar α)) gradingMonoidHom
      (AddMonoidAlgebra.of R (Forest (Nonplanar α)) (Multiplicative.ofAdd F)) = _
  rw [AddMonoidAlgebra.lift_of]
  rfl

/-- `ϕt(F) = t^{α(F)}`: the forest value is the single grading monomial at the accessible-term
    count (the product of per-tree monomials collapses since `α` is additive). -/
theorem prod_gradingMonomialTree (F : Forest (Nonplanar α)) :
    (F.map (gradingMonomialTree (R := R))).prod = gradeMonomial (Forest.alpha F : ℤ) := by
  induction F using Multiset.induction with
  | empty => rw [Multiset.map_zero, Multiset.prod_zero, Forest.alpha_zero]; rfl
  | cons T F ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, gradingMonomialTree, gradeMonomial_mul,
      Forest.alpha_cons]
    push_cast; rfl

theorem gradingChar_apply_of'_eq (F : Forest (Nonplanar α)) :
    gradingChar (R := R) (of' F) = gradeMonomial (Forest.alpha F : ℤ) := by
  rw [gradingChar_apply_of', prod_gradingMonomialTree]

@[simp] theorem gradingChar_apply_ofTree (T : Nonplanar α) :
    gradingChar (R := R) (ofTree T) = gradeMonomial (T.accCount : ℤ) := by
  unfold ofTree
  rw [gradingChar_apply_of', Multiset.map_singleton, Multiset.prod_singleton]
  rfl

/-! ### MCB Lemma 3.5.5: ϕt is entirely nonpolar -/

/-- **MCB Lemma 3.5.5**: `ϕt(F)` always lies in the nonpolar subring — `R·ϕt(F) = 0` — because the
    `δα`-grading `α(F) ≥ 0`. Hence `ϕt` cannot detect Sideward Merge (regardless of which Merge
    operations build `F`), motivating the intermediate-derivation character `ψt`. -/
theorem polarHahn_gradingChar_of' (F : Forest (Nonplanar α)) :
    polarHahn (gradingChar (R := R) (of' F)) = 0 := by
  rw [gradingChar_apply_of'_eq, polarHahn_gradeMonomial,
    if_neg (by omega : ¬ ((Forest.alpha F : ℤ) < 0))]

/-- Lemma 3.5.5 on a single tree: `R·ϕt(T) = 0`. -/
theorem polarHahn_gradingChar_ofTree (T : Nonplanar α) :
    polarHahn (gradingChar (R := R) (ofTree T)) = 0 := by
  rw [gradingChar_apply_ofTree, polarHahn_gradeMonomial,
    if_neg (by omega : ¬ ((T.accCount : ℤ) < 0))]

end Minimalist.Merge
