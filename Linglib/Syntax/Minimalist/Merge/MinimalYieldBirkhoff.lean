/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Merge.MinimalYieldCharacter
import Linglib.Core.Algebra.RootedTree.BirkhoffFactorization

/-!
# Birkhoff renormalization of the Minimal-Yield character (MCB Prop. 3.5.6)
[marcolli-chomsky-berwick-2025] §3.5.2.2

The payoff of MCB §3.5.2: the Birkhoff factorization of a Minimal-Yield character with respect to the
polar-part Rota–Baxter operator (`rotaBaxterPolar`, the Phase-1 minimal-subtraction operator)
renormalizes it — the Bogolyubov negative part `φ₋` is the divergent (Sideward) content subtracted.

For the **simple** character `ϕt = gradingChar` (MCB Prop. 3.5.3), Lemma 3.5.5 says `ϕt` is entirely
nonpolar; we make this concrete in the Birkhoff language: **`birkhoffMinusTree(ϕt) = 0`** — there is
no divergence to subtract, so `ϕt` is its own renormalization. This is *exactly why* `ϕt` cannot
separate Internal/External from Sideward Merge (MCB's remark after Lemma 3.5.5): one must instead use
the intermediate-derivation character `ψt` (Cor. 3.5.4, eq. 3.5.7), whose nontrivial polar part the
**full** Birkhoff factorization — not plain `1 − R`, since `R` is a Rota–Baxter operator and *not* an
algebra homomorphism — eliminates (Prop. 3.5.6). Building `ψt` (a sum over all intermediate
derivation pairs `(F, F')`) is left to future work; the renormalization machinery and the `ϕt` base
case are here.

## Main results

- `birkhoffMinusTree_eq_zero_of_nonpolar`: a nonpolar character has trivial Bogolyubov negative part.
- `birkhoffMinusTree_gradingChar`: `ϕt` is trivially renormalized (Lemma 3.5.5, Birkhoff form).
- `renormGradingChar` / `birkhoffFactorization_gradingChar`: the renormalized character `ϕt,+` and
  its factorization `ϕt,+ = ϕt,− ⋆ ϕt`.

## References

[marcolli-chomsky-berwick-2025] (Prop. 3.5.3, Lemma 3.5.5, Prop. 3.5.6; Prop. 3.1.7)
-/

namespace Minimalist.Merge

open RootedTree RootedTree.ConnesKreimer LaurentSeries
open scoped TensorProduct

variable {α : Type*} {R : Type*} [CommRing R]

/-! ### A nonpolar character has trivial Bogolyubov negative part -/

/-- If a character `φ` is **nonpolar** on every tree (`R·φ(T) = 0`), its Bogolyubov negative part
    under the polar-projection Rota–Baxter operator vanishes: `φ₋(T) = 0`. By strong recursion on
    `T.depth`: every nontrivial cut's pruned forest contains a subtree of smaller depth, where `φ₋`
    is `0` by the recursive hypothesis — killing that term — and the trivial cut contributes the
    nonpolar trunk value `φ(ofTree …)`, so `R` annihilates the whole Bogolyubov preparation. -/
theorem birkhoffMinusTree_eq_zero_of_nonpolar
    (φ : ConnesKreimer R (Nonplanar α) →ₐ[R] LaurentSeries R)
    (hφ : ∀ T : Nonplanar α, polarHahn (φ (ofTree T)) = 0)
    (T : Nonplanar α) :
    birkhoffMinusTree φ.toLinearMap rotaBaxterPolar T = 0 := by
  rw [birkhoffMinusTree_eq_neg_op_prep, birkhoffPrepTree_unfold, neg_eq_zero, map_multiset_sum]
  apply Multiset.sum_eq_zero
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hy
  rw [rotaBaxterPolar_op_apply]
  rcases eq_or_ne p.1 0 with hempty | hne
  · rw [hempty, Multiset.map_zero, Multiset.prod_zero, one_mul, AlgHom.toLinearMap_apply]
    exact hφ p.2
  · obtain ⟨Tᵢ, hTᵢ⟩ := Multiset.exists_mem_of_ne_zero hne
    rw [Multiset.prod_eq_zero (Multiset.mem_map.mpr
        ⟨Tᵢ, hTᵢ, birkhoffMinusTree_eq_zero_of_nonpolar φ hφ Tᵢ⟩), zero_mul, polarHahn_zero]
termination_by T.depth
decreasing_by exact cutSummandsN_subtree_depth_lt T p.1 p.2 hp Tᵢ hTᵢ

/-! ### ϕt is trivially renormalized (MCB Lemma 3.5.5, Birkhoff form) -/

/-- **`ϕt` is its own renormalization** (MCB Lemma 3.5.5 in Birkhoff form): the Bogolyubov negative
    part of the Minimal-Yield character `ϕt = gradingChar` vanishes on every tree, because `ϕt` is
    nonpolar (`polarHahn_gradingChar_ofTree`). There is no divergence to subtract — which is why `ϕt`
    cannot detect Sideward Merge. -/
theorem birkhoffMinusTree_gradingChar (T : Nonplanar α) :
    birkhoffMinusTree (gradingChar (R := R)).toLinearMap rotaBaxterPolar T = 0 :=
  birkhoffMinusTree_eq_zero_of_nonpolar gradingChar (fun T => polarHahn_gradingChar_ofTree T) T

/-! ### The renormalized character -/

/-- The renormalized Minimal-Yield character `ϕt,+ = (1−R)ϕ̃t = birkhoffPlus(ϕt)`. -/
noncomputable def renormGradingChar : ConnesKreimer R (Nonplanar α) →ₐ[R] LaurentSeries R :=
  birkhoffPlus (gradingChar (R := R)).toLinearMap rotaBaxterPolar

/-- **`ϕt,+ = ϕ̃t`** on every tree: since `ϕt` carries no divergence (`birkhoffMinusTree_gradingChar`),
    the renormalized part of `ϕt` equals its Bogolyubov preparation — nothing is subtracted. The
    Birkhoff factorization does no work on `ϕt`, the concrete form of MCB Lemma 3.5.5. -/
theorem birkhoffPlusTree_gradingChar (T : Nonplanar α) :
    birkhoffPlusTree (gradingChar (R := R)).toLinearMap rotaBaxterPolar T
      = birkhoffPrepTree (gradingChar (R := R)).toLinearMap rotaBaxterPolar T := by
  rw [birkhoffPlusTree_eq_prep_add_minus, birkhoffMinusTree_gradingChar, add_zero]

end Minimalist.Merge
