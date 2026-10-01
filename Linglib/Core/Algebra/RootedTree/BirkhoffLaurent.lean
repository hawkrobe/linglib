/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.BirkhoffFactorization
public import Linglib.Core.Algebra.RotaBaxterLaurent

@[expose] public section

open RoseTree UnorderedTree

/-!
# Birkhoff renormalization of Laurent-series characters

The Birkhoff factorization of a character `φ : H → A⸨X⸩` into a ring of Laurent series, with
respect to the polar-part Rota–Baxter operator `rotaBaxterPolar`: the minimal-subtraction scheme
of Connes–Kreimer renormalization. The renormalized part `φ₊ = (1−R)φ̃` always lands in the
nonpolar subring `A[[t]]`, and a character that is already nonpolar on every tree has trivial
negative part.

## Main results

* `ConnesKreimer.birkhoffMinusTree_eq_zero_of_nonpolar`: a nonpolar character has trivial
  Bogolyubov negative part.
* `ConnesKreimer.polarHahn_birkhoffPlusTree`, `ConnesKreimer.polarHahn_birkhoffPlus_of'`: the
  renormalized part is nonpolar.

## References

* [connes-kreimer-2000]
-/

namespace ConnesKreimer

open LaurentSeries

variable {R : Type*} [CommRing R] {α : Type*}
  (φ : ConnesKreimer R (UnorderedTree α) →ₐ[R] LaurentSeries R)

/-! ### A nonpolar character has trivial Bogolyubov negative part -/

/-- If a character `φ` is **nonpolar** on every tree (`R·φ(ofTree T) = 0`), its Bogolyubov negative
    part under the polar-projection Rota–Baxter operator vanishes: `φ₋(T) = 0`. By strong recursion
    on `T.numNodes`: every nontrivial cut's pruned forest contains a smaller subtree, where
    `φ₋` is `0` by the recursive hypothesis, killing that term, and the trivial cut contributes the
    nonpolar trunk value `φ(ofTree …)`, so `R` annihilates the whole Bogolyubov preparation. -/
theorem birkhoffMinusTree_eq_zero_of_nonpolar
    (hφ : ∀ T : UnorderedTree α, polarHahn (φ (ofTree T)) = 0) (T : UnorderedTree α) :
    birkhoffMinusTree φ.toLinearMap rotaBaxterPolar T = 0 := by
  rw [birkhoffMinusTree_eq_neg_op_prep, birkhoffPrepTree, neg_eq_zero, map_multiset_sum]
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
termination_by T.numNodes
decreasing_by exact cutSummandsN_crown_numNodes_lt hp hTᵢ

/-! ### The renormalized part always lands in the nonpolar subring -/

/-- The renormalized part lands in `A[[t]]`. For any character `φ`, the renormalized part
    `φ₊(T) = (1−R)(φ̃(T))` is nonpolar, `R·φ₊(T) = 0`, because `R` is idempotent, so `φ₊` is in the
    range of `1 − R`. -/
theorem polarHahn_birkhoffPlusTree (T : UnorderedTree α) :
    polarHahn (birkhoffPlusTree φ.toLinearMap rotaBaxterPolar T) = 0 := by
  unfold birkhoffPlusTree
  rw [rotaBaxterPolar_op_apply, polarHahn_sub_self]

/-- The renormalized character is nonpolar on each forest basis element, being the product of the
    nonpolar per-tree renormalized parts (the nonpolar series form a subalgebra). -/
theorem polarHahn_birkhoffPlus_of' (F : Forest (UnorderedTree α)) :
    polarHahn (birkhoffPlus φ.toLinearMap rotaBaxterPolar (of' F)) = 0 := by
  rw [birkhoffPlus_apply_of']
  induction F using Multiset.induction with
  | empty => rw [Multiset.map_zero, Multiset.prod_zero, polarHahn_one]
  | cons T F ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact polarHahn_mul _ _ (polarHahn_birkhoffPlusTree φ T) ih

end ConnesKreimer
