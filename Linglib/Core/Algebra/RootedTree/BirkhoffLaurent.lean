/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.BirkhoffFactorization
import Linglib.Core.Algebra.RotaBaxterLaurent

/-!
# Birkhoff renormalization of Laurent-series characters  `[UPSTREAM]`

The Birkhoff factorization (`BirkhoffFactorization.lean`) of a character `φ : H → A⸨X⸩` from the
Connes–Kreimer Hopf algebra of nonplanar rooted forests into a ring of Laurent series, with respect
to the **polar-part Rota–Baxter operator** `rotaBaxterPolar` (`RotaBaxterLaurent.lean`) — the
minimal-subtraction scheme of Connes–Kreimer renormalization. Two framework-agnostic facts:

* the renormalized part `φ₊ = (1−R)φ̃` always lands in the **nonpolar subring** `A[[t]]`, since `1−R`
  projects onto it (`polarHahn_birkhoffPlusTree`, `polarHahn_birkhoffPlus_of'`);
* a character that is already nonpolar on every tree has a **trivial** negative part `φ₋ = 0`
  (`birkhoffMinusTree_eq_zero_of_nonpolar`) — no divergence to subtract.

These are the algebraic core of [marcolli-chomsky-berwick-2025]'s "Minimal Yield as Birkhoff
factorization" (§3.5.2); the syntactic interpretation (the Minimal-Yield character and its grading)
lives downstream in `Syntax/Minimalist/Merge/`.

## Main results

- `birkhoffMinusTree_eq_zero_of_nonpolar`: a nonpolar character has trivial Bogolyubov negative part.
- `polarHahn_birkhoffPlusTree` / `polarHahn_birkhoffPlus_of'`: the renormalized part is nonpolar.

## References

[marcolli-chomsky-berwick-2025] (§3.5.2, Prop. 3.1.7, Prop. 3.5.6)
-/

namespace RootedTree.ConnesKreimer

open LaurentSeries

variable {R : Type*} [CommRing R] {α : Type*}
  (φ : ConnesKreimer R (Nonplanar α) →ₐ[R] LaurentSeries R)

/-! ### A nonpolar character has trivial Bogolyubov negative part -/

/-- If a character `φ` is **nonpolar** on every tree (`R·φ(ofTree T) = 0`), its Bogolyubov negative
    part under the polar-projection Rota–Baxter operator vanishes: `φ₋(T) = 0`. By strong recursion
    on `T.depth`: every nontrivial cut's pruned forest contains a subtree of smaller depth, where
    `φ₋` is `0` by the recursive hypothesis — killing that term — and the trivial cut contributes the
    nonpolar trunk value `φ(ofTree …)`, so `R` annihilates the whole Bogolyubov preparation. -/
theorem birkhoffMinusTree_eq_zero_of_nonpolar
    (hφ : ∀ T : Nonplanar α, polarHahn (φ (ofTree T)) = 0) (T : Nonplanar α) :
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
        ⟨Tᵢ, hTᵢ, birkhoffMinusTree_eq_zero_of_nonpolar hφ Tᵢ⟩), zero_mul, polarHahn_zero]
termination_by T.depth
decreasing_by exact cutSummandsN_subtree_depth_lt T p.1 p.2 hp Tᵢ hTᵢ

/-! ### The renormalized part always lands in the nonpolar subring -/

/-- **The renormalized character lands in `A[[t]]`** ([marcolli-chomsky-berwick-2025] Prop. 3.5.6's
    `ψt,+ : H → DM[[t]]`): for *any* character `φ`, the renormalized part `φ₊(T) = (1−R)(φ̃(T))` is
    **nonpolar** — `R·φ₊(T) = 0` — because `R` is idempotent, so `φ₊` is in the range of `1 − R`. -/
theorem polarHahn_birkhoffPlusTree (T : Nonplanar α) :
    polarHahn (birkhoffPlusTree φ.toLinearMap rotaBaxterPolar T) = 0 := by
  unfold birkhoffPlusTree
  rw [rotaBaxterPolar_op_apply, polarHahn_sub_self]

/-- **`φ₊ : H → A[[t]]` on every workspace** (Prop. 3.5.6, forest level): the renormalized character
    is nonpolar on each forest basis element, being the product of the nonpolar per-tree renormalized
    parts (the nonpolar series form a subalgebra). -/
theorem polarHahn_birkhoffPlus_of' (F : Forest (Nonplanar α)) :
    polarHahn (birkhoffPlus φ.toLinearMap rotaBaxterPolar (of' F)) = 0 := by
  rw [birkhoffPlus_apply_of']
  induction F using Multiset.induction with
  | empty => rw [Multiset.map_zero, Multiset.prod_zero, polarHahn_one]
  | cons T F ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact polarHahn_mul _ _ (polarHahn_birkhoffPlusTree φ T) ih

end RootedTree.ConnesKreimer
