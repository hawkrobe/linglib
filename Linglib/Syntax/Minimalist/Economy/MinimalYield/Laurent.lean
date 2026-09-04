/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Economy.MinimalYield.Basic
import Linglib.Core.Algebra.RotaBaxterLaurent
import Linglib.Core.Algebra.RootedTree.HopfAlgebra
import Linglib.Core.Algebra.RootedTree.BirkhoffLaurent

/-!
# Minimal Yield in the Laurent-series ring

Minimal Yield can be restated as a Birkhoff factorization in the ring of Laurent series
`DM[t⁻¹][[t]]` over the algebra of free Merge derivations, weighting a transformation `F → F'` by
`tᵟ` for a grading `δ` read off the size measures. This file defines the gradings

  `δb₀ F F' = b₀ F − b₀ F'`,  `δα F F' = α F' − α F`,  `δσ F F' = σ F' − σ F`,

shows Minimal Yield is `0 ≤ δb₀ ∧ 0 ≤ δα ∧ δσ = 1`, and connects the gradings to the polar-part
operator `R = LaurentSeries.polarHahn`: a transformation satisfies weak Minimal Yield iff its
`δb₀`- and `δα`-monomials are both nonpolar (`weak_iff_polarHahn`).

The character `ϕt : H →ₐ[R] LaurentSeries R` on the Hopf algebra of nonplanar forests records,
in place of the derivation coefficients of `DM`, only the grading `tᵟ` with `δ = δα`; on a forest
it is `t^{α(F)}`. Since `α(F) ≥ 0` it is nonpolar on every forest, so its Bogolyubov negative part
vanishes and it is its own renormalization: `ϕt` cannot see Sideward Merge, which is why the
intermediate-derivation character `ψt` is needed. Summing monomials over a family of
transformations, as `ψt` does, the polar part is the sum over the divergent ones
(`LaurentSeries.polarHahn_sum_map_single`).

## Main definitions

* `Minimalist.MinimalYield.δb₀`, `δα`, `δσ`: the signed gradings.
* `Minimalist.MinimalYield.gradingChar`: the character `ϕt`.
* `Minimalist.MinimalYield.renormGradingChar`: its Birkhoff-renormalized part `ϕt,+`.

## Main results

* `Minimalist.MinimalYield.iff_gradings`, `weak_iff_polarHahn`: Minimal Yield as sign conditions
  and as nonpolarity.
* `Minimalist.MinimalYield.polarHahn_gradingChar_of'`: `ϕt` is nonpolar.
* `Minimalist.MinimalYield.birkhoffMinusTree_gradingChar`: its negative part vanishes.

## References

* [marcolli-chomsky-berwick-2025], §3.5.2 (Propositions 3.5.2, 3.5.3, 3.5.6, Corollary 3.5.4,
  Lemma 3.5.5)
-/

namespace Minimalist.MinimalYield

open RoseTree UnorderedTree ConnesKreimer LaurentSeries

variable {α β R : Type*} [CommRing R]

/-! ### The gradings -/

section Gradings

variable (F F' : Forest (UnorderedTree (α ⊕ β)))

/-- `δb₀ F F' = b₀ F − b₀ F'`, nonnegative iff `F → F'` does not diverge. -/
def δb₀ : ℤ := (Multiset.card F : ℤ) - Multiset.card F'

/-- `δα F F' = α F' − α F`, nonnegative iff `F → F'` loses no information. -/
def δα : ℤ := (Forest.numEdges F' : ℤ) - Forest.numEdges F

/-- `δσ F F' = σ F' − σ F`, equal to `1` iff `F → F'` has minimal yield. -/
def δσ : ℤ := (Forest.numNodes F' : ℤ) - Forest.numNodes F

theorem δσ_eq : δσ F F' = δα F F' - δb₀ F F' := by
  simp only [δσ, δα, δb₀, Forest.numNodes_eq_card_add_numEdges]; omega

theorem weak_iff_gradings : MinimalYieldWeak F F' ↔ 0 ≤ δb₀ F F' ∧ 0 ≤ δα F F' := by
  simp only [δb₀, δα, sub_nonneg, Nat.cast_le]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem iff_gradings : MinimalYield F F' ↔ 0 ≤ δb₀ F F' ∧ 0 ≤ δα F F' ∧ δσ F F' = 1 := by
  rw [← and_assoc, ← weak_iff_gradings, δσ, sub_eq_iff_eq_add']
  exact ⟨fun h => ⟨h.1, by exact_mod_cast h.2⟩, fun h => ⟨h.1, by exact_mod_cast h.2⟩⟩

/-- Weak Minimal Yield holds iff the `δb₀`- and `δα`-monomials of `F → F'` are both nonpolar. -/
theorem weak_iff_polarHahn [Nontrivial R] :
    MinimalYieldWeak F F' ↔
      polarHahn (HahnSeries.single (δb₀ F F') (1 : R)) = 0 ∧
        polarHahn (HahnSeries.single (δα F F') (1 : R)) = 0 := by
  simp only [weak_iff_gradings, polarHahn_single_eq_zero_iff one_ne_zero]

end Gradings

/-! ### The character `ϕt` -/

/-- The value of `ϕt` on a tree: `t^{α(T)}`. -/
noncomputable def gradingMonomialTree (T : UnorderedTree α) : LaurentSeries R :=
  HahnSeries.single (T.numEdges : ℤ) 1

/-- `ϕt` on forests, multiplicative over disjoint union. -/
noncomputable def gradingMonoidHom :
    Multiplicative (Forest (UnorderedTree α)) →* LaurentSeries R where
  toFun F := (F.toAdd.map (gradingMonomialTree (R := R))).prod
  map_one' := by
    show ((0 : Forest (UnorderedTree α)).map _).prod = 1
    rw [Multiset.map_zero, Multiset.prod_zero]
  map_mul' F G := by
    show ((F.toAdd + G.toAdd).map (gradingMonomialTree (R := R))).prod =
         (F.toAdd.map _).prod * (G.toAdd.map _).prod
    rw [Multiset.map_add, Multiset.prod_add]

/-- The character `ϕt : H →ₐ[R] LaurentSeries R`, `ϕt(F) = t^{α(F)}`. -/
noncomputable def gradingChar : ConnesKreimer R (UnorderedTree α) →ₐ[R] LaurentSeries R :=
  ConnesKreimer.lift gradingMonoidHom

@[simp] theorem gradingChar_apply_of' (F : Forest (UnorderedTree α)) :
    gradingChar (R := R) (of' F) = (F.map (gradingMonomialTree (R := R))).prod := by
  rw [gradingChar, ConnesKreimer.lift_of']
  rfl

/-- `ϕt(F) = t^{α(F)}`, since `α` is additive over forests. -/
theorem prod_gradingMonomialTree (F : Forest (UnorderedTree α)) :
    (F.map (gradingMonomialTree (R := R))).prod = HahnSeries.single (Forest.numEdges F : ℤ) 1 := by
  induction F using Multiset.induction with
  | empty => rw [Multiset.map_zero, Multiset.prod_zero, Forest.numEdges_zero]; rfl
  | cons T F ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, gradingMonomialTree,
      HahnSeries.single_mul_single, one_mul, Forest.numEdges_cons]
    push_cast; rfl

theorem gradingChar_apply_of'_eq (F : Forest (UnorderedTree α)) :
    gradingChar (R := R) (of' F) = HahnSeries.single (Forest.numEdges F : ℤ) 1 := by
  rw [gradingChar_apply_of', prod_gradingMonomialTree]

@[simp] theorem gradingChar_apply_ofTree (T : UnorderedTree α) :
    gradingChar (R := R) (ofTree T) = HahnSeries.single (T.numEdges : ℤ) 1 := by
  unfold ofTree
  rw [gradingChar_apply_of', Multiset.map_singleton, Multiset.prod_singleton]
  rfl

/-! ### `ϕt` is nonpolar -/

/-- `ϕt` is nonpolar on every forest, since `α(F) ≥ 0`. -/
theorem polarHahn_gradingChar_of' (F : Forest (UnorderedTree α)) :
    polarHahn (gradingChar (R := R) (of' F)) = 0 := by
  rw [gradingChar_apply_of'_eq, polarHahn_single,
    if_neg (by omega : ¬ ((Forest.numEdges F : ℤ) < 0))]

theorem polarHahn_gradingChar_ofTree (T : UnorderedTree α) :
    polarHahn (gradingChar (R := R) (ofTree T)) = 0 := by
  rw [gradingChar_apply_ofTree, polarHahn_single,
    if_neg (by omega : ¬ ((T.numEdges : ℤ) < 0))]

/-! ### Birkhoff renormalization -/

/-- The Bogolyubov negative part of `ϕt` vanishes on every tree. -/
theorem birkhoffMinusTree_gradingChar (T : UnorderedTree α) :
    birkhoffMinusTree (gradingChar (R := R)).toLinearMap rotaBaxterPolar T = 0 :=
  birkhoffMinusTree_eq_zero_of_nonpolar gradingChar (fun T => polarHahn_gradingChar_ofTree T) T

/-- The renormalized character `ϕt,+ = birkhoffPlus ϕt`. -/
noncomputable def renormGradingChar : ConnesKreimer R (UnorderedTree α) →ₐ[R] LaurentSeries R :=
  birkhoffPlus (gradingChar (R := R)).toLinearMap rotaBaxterPolar

/-- `ϕt,+` coincides with the Bogolyubov preparation of `ϕt` on every tree. -/
theorem birkhoffPlusTree_gradingChar (T : UnorderedTree α) :
    birkhoffPlusTree (gradingChar (R := R)).toLinearMap rotaBaxterPolar T
      = birkhoffPrepTree (gradingChar (R := R)).toLinearMap rotaBaxterPolar T := by
  rw [birkhoffPlusTree_eq_prep_add_minus, birkhoffMinusTree_gradingChar, add_zero]

end Minimalist.MinimalYield
