/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.Multiset.Antidiagonal
import Linglib.Core.Data.RoseTree.DecEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Multiset.Antidiagonal
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# Automorphism cardinality for rooted nonplanar trees

For a rooted nonplanar tree whose children form the multiset `M = {c₁ × k₁, …, cₙ × kₙ}`
(distinct subtrees `cᵢ` with multiplicity `kᵢ`), the automorphism group has cardinality
`∏ᵢ kᵢ! · |Aut(cᵢ)| ^ kᵢ`; the same formula applied to the top-level multiset counts the
automorphisms of a forest.

## Main definitions

* `RootedTree.Nonplanar.autCard`: the automorphism count `|Aut(t)|` of a rooted nonplanar tree.
* `RootedTree.Nonplanar.forestAutCard`: the automorphism count of a forest (multiset of rooted
  nonplanar trees).

## Main results

* `RootedTree.Nonplanar.autCard_node`: the recursion `autCard (node a M) = forestAutCard M`.
* `RootedTree.Nonplanar.forestAutCard_add`: the multinomial split identity
  `forestAutCard (F + G) = (antidiagonal (F + G)).count (F, G) * (forestAutCard F *
  forestAutCard G)`, the combinatorial core of the pairing's product-coproduct adjunction.
-/

namespace RootedTree

namespace Nonplanar

variable {α : Type*} [DecidableEq α]

/-! ### RoseTree-representative substrate

`treeAutCard` computes `|Aut(mk t)|` on a planar `RoseTree` representative
`t`; `Perm`-invariance (below) lets it descend to `Nonplanar.autCard`
through the quotient. -/

/-- Symmetry-factor at one node: `∏_{distinct c ∈ M} (M.count c)!`. -/
def multinomialFactor (M : Multiset (Nonplanar α)) : ℕ :=
  M.toFinset.prod fun t => (M.count t).factorial

/-- The automorphism count `|Aut(mk t)|` of the nonplanar tree represented by a planar
    `RoseTree` `t`; substrate for `Nonplanar.autCard`. -/
def treeAutCard : RoseTree α → ℕ
  | .node _ cs =>
      (cs.map treeAutCard).prod * multinomialFactor (Multiset.ofList (cs.map mk))

theorem treeAutCard_node (a : α) (cs : List (RoseTree α)) :
    treeAutCard (RoseTree.node a cs) =
      (cs.map treeAutCard).prod * multinomialFactor (Multiset.ofList (cs.map mk)) := by
  rw [treeAutCard]

/-! #### `treeAutCard` is `Perm`-invariant -/

mutual
/-- `treeAutCard` is invariant under `RoseTree.Perm`. -/
theorem treeAutCard_perm : ∀ {t s : RoseTree α}, RoseTree.Perm t s →
    treeAutCard t = treeAutCard s
  | _, _, .node h => by
    rw [treeAutCard_node, treeAutCard_node]
    obtain ⟨hprod, hmk⟩ := treeAutCard_permList h
    rw [hprod, hmk]
  | _, _, .trans h₁ h₂ => (treeAutCard_perm h₁).trans (treeAutCard_perm h₂)

/-- The child-`treeAutCard` product and the `mk`-multiset are `PermList`-invariant. -/
theorem treeAutCard_permList : ∀ {cs ds : List (RoseTree α)}, RoseTree.PermList cs ds →
    (cs.map treeAutCard).prod = (ds.map treeAutCard).prod ∧
      (Multiset.ofList (cs.map mk) : Multiset (Nonplanar α)) = Multiset.ofList (ds.map mk)
  | _, _, .nil => ⟨rfl, rfl⟩
  | _, _, .cons h hs => by
    obtain ⟨hprod, hmk⟩ := treeAutCard_permList hs
    refine ⟨by simp only [List.map_cons, List.prod_cons, treeAutCard_perm h, hprod], ?_⟩
    simp only [List.map_cons, ← Multiset.cons_coe]
    rw [mk_eq_mk_iff.mpr h, hmk]
  | _, _, .swap c d cs =>
    ⟨by simp only [List.map_cons, List.prod_cons]; exact mul_left_comm _ _ _,
     by simp only [List.map_cons, ← Multiset.cons_coe]; exact Multiset.cons_swap _ _ _⟩
  | _, _, .trans h₁ h₂ =>
    match treeAutCard_permList h₁, treeAutCard_permList h₂ with
    | ⟨p₁, m₁⟩, ⟨p₂, m₂⟩ => ⟨p₁.trans p₂, m₁.trans m₂⟩
end

/-! #### Positivity of `treeAutCard` -/

/-- `multinomialFactor` is positive. -/
private theorem multinomialFactor_pos (M : Multiset (Nonplanar α)) :
    0 < multinomialFactor M :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

/-- `treeAutCard` is positive. -/
theorem treeAutCard_pos (t : RoseTree α) : 0 < treeAutCard t := by
  induction t with
  | node a cs ih =>
    rw [treeAutCard_node]
    refine Nat.mul_pos ?_ (multinomialFactor_pos _)
    exact List.prod_pos_iff_forall_pos_nat.mpr (by simpa using ih)

/-! ### Nonplanar automorphism count via lift -/

/-- The cardinality `|Aut(t)|` of the automorphism group of a rooted nonplanar tree:
    `∏_{distinct c ∈ M} (M.count c)! · autCard c ^ M.count c` at `node a M`
    (`autCard_node`), `1` at a leaf (`autCard_leaf`). -/
def autCard : Nonplanar α → ℕ :=
  Nonplanar.lift treeAutCard (fun _ _ h => treeAutCard_perm h)

@[simp] theorem autCard_mk (t : RoseTree α) : autCard (mk t) = treeAutCard t := rfl

/-- A leaf has trivial aut group. -/
@[simp] theorem autCard_leaf (a : α) : autCard (Nonplanar.leaf a : Nonplanar α) = 1 := by
  show treeAutCard (RoseTree.leaf a) = 1
  rw [RoseTree.leaf_def, treeAutCard_node]
  simp [multinomialFactor]

/-- `autCard` is positive: the automorphism group contains the identity. -/
theorem autCard_pos (t : Nonplanar α) : 0 < autCard t :=
  Quotient.inductionOn t treeAutCard_pos

/-- The automorphism count `|Aut(F)|` of a forest of nonplanar trees:
    `∏_{distinct T ∈ F} (F.count T)! · autCard T ^ F.count T`. -/
def forestAutCard (F : Multiset (Nonplanar α)) : ℕ :=
  F.toFinset.prod fun t => (F.count t).factorial * autCard t ^ F.count t

/-- The empty forest has trivial aut group. -/
@[simp] theorem forestAutCard_zero :
    forestAutCard (0 : Multiset (Nonplanar α)) = 1 := by
  simp [forestAutCard]

/-- `forestAutCard` is positive. -/
theorem forestAutCard_pos (F : Multiset (Nonplanar α)) : 0 < forestAutCard F := by
  unfold forestAutCard
  exact Finset.prod_pos fun t _ =>
    Nat.mul_pos (Nat.factorial_pos _) (pow_pos (autCard_pos t) _)

/-- `treeAutCard` of a representative equals `autCard` of its class. -/
private theorem treeAutCard_out (x : Nonplanar α) :
    treeAutCard x.out = autCard x := by
  conv_rhs => rw [← x.out_eq]
  rfl

/-- The `treeAutCard`-product over `Quotient.out` representatives is the `autCard`-product. -/
private theorem prod_out_treeAutCard (lst : List (Nonplanar α)) :
    ((lst.map Quotient.out).map treeAutCard).prod = (lst.map autCard).prod := by
  congr 1
  rw [List.map_map]
  exact List.map_congr_left fun x _ => treeAutCard_out x

omit [DecidableEq α] in
/-- `mk ∘ Quotient.out` is the identity on lists of nonplanar trees. -/
private theorem ofList_map_mk_qout (lst : List (Nonplanar α)) :
    (Multiset.ofList (((lst.map Quotient.out).map mk)) :
        Multiset (Nonplanar α)) = Multiset.ofList lst := by
  rw [List.map_map]
  congr 1
  exact (List.map_congr_left (fun x _ => x.out_eq)).trans (List.map_id lst)

/-- `forestAutCard` as the `autCard`-product over all members times the symmetry factor:
    the forest analogue of `treeAutCard_node`'s shape. -/
theorem forestAutCard_eq_prod_mul_multinomialFactor (F : Multiset (Nonplanar α)) :
    forestAutCard F = (F.map autCard).prod * multinomialFactor F := by
  unfold forestAutCard multinomialFactor
  rw [Finset.prod_multiset_map_count, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t _ => mul_comm _ _

/-- `autCard` at a node is `forestAutCard` of the children: the recursive formula. -/
@[simp] theorem autCard_node (a : α) (F : Multiset (Nonplanar α)) :
    autCard (Nonplanar.node a F) = forestAutCard F := by
  induction F using Quotient.inductionOn with
  | h lst =>
    show treeAutCard (RoseTree.node a (lst.map Quotient.out)) = _
    rw [treeAutCard_node, prod_out_treeAutCard lst, ofList_map_mk_qout lst,
        forestAutCard_eq_prod_mul_multinomialFactor]
    rfl

/-! ### Multinomial split identity

`Multiset.count_antidiagonal_eq_count_powerset` and `Multiset.count_powerset_of_le`
compute the split multiplicity; `Nat.add_choose_mul_factorial_mul_factorial` recombines
it with the factorials per distinct tree. This identity is the combinatorial core of the
pairing's product-coproduct adjunction (`GrossmanLarsonPairing.pairing_of'_mul_of'`). -/

/-- **Multinomial split identity** for `forestAutCard`:
    `|Aut (F+G)| = count (F,G) (antidiagonal (F+G)) · |Aut F| · |Aut G|`. -/
theorem forestAutCard_add (F G : Multiset (Nonplanar α)) :
    forestAutCard (F + G) = (Multiset.antidiagonal (F + G)).count (F, G) *
      (forestAutCard F * forestAutCard G) := by
  have hext : ∀ M : Multiset (Nonplanar α), M ≤ F + G →
      forestAutCard M
        = (F + G).toFinset.prod (fun t => (M.count t).factorial * autCard t ^ M.count t) := by
    intro M hM
    refine Finset.prod_subset
      (Multiset.toFinset_subset.mpr (Multiset.subset_of_le hM)) fun x _ hx => ?_
    rw [Multiset.count_eq_zero.mpr fun hm => hx (Multiset.mem_toFinset.mpr hm)]
    simp
  rw [Multiset.count_antidiagonal_eq_count_powerset,
      Multiset.count_powerset_of_le (Multiset.le_add_left G F),
      hext F (Multiset.le_add_right F G), hext G (Multiset.le_add_left G F),
      hext (F + G) le_rfl, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Multiset.count_add, pow_add,
      ← Nat.add_choose_mul_factorial_mul_factorial (F.count t) (G.count t)]
  ring

end Nonplanar

end RootedTree
