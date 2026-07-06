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
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# Automorphism cardinality for rooted nonplanar trees

For a rooted nonplanar tree whose children form the multiset `M = {c₁ × k₁, …, cₙ × kₙ}`
(distinct subtrees `cᵢ` with multiplicity `kᵢ`), the automorphism group has cardinality
`∏ᵢ kᵢ! · |Aut(cᵢ)| ^ kᵢ`; the same formula applied to the top-level multiset counts the
automorphisms of a forest. These counts are the symmetry weights of the Connes-Kreimer /
Grossman-Larson pairing (`Linglib.Core.Algebra.RootedTree.GrossmanLarsonPairing`).

## Main definitions

* `RootedTree.Nonplanar.autCard`: the automorphism count `|Aut(t)|` of a rooted nonplanar tree.
* `RootedTree.Nonplanar.forestAutCard`: the automorphism count of a forest (multiset of rooted
  nonplanar trees).

## Main results

* `RootedTree.Nonplanar.autCard_node`: the recursion `autCard (node a M) = forestAutCard M`.
* `RootedTree.Nonplanar.forestAutCard_add`: the multinomial split identity
  `count (F, G) (antidiagonal (F + G)) * (forestAutCard F * forestAutCard G) =
  forestAutCard (F + G)`, the combinatorial core of the pairing's product-coproduct adjunction.

## Implementation notes

`treeAutCard` computes the count by structural recursion on a planar `RoseTree` representative;
`Perm`-invariance (`treeAutCard_perm`) descends it to `Nonplanar.autCard` through the quotient.
`[UPSTREAM]` candidate; eventual mathlib home would be `Mathlib.Combinatorics.RootedTree.Aut`.

## Tags

rooted tree, automorphism, symmetry factor, multinomial
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

/-- The automorphism count `|Aut(mk t)|` of the nonplanar tree represented
    by a planar `RoseTree` `t`. Substrate for `Nonplanar.autCard` (which lifts
    it through the `Perm` quotient). At a node, the product of the
    children's counts times `multinomialFactor` on the multiset of
    nonplanar-`mk` children (counting symmetric rearrangements). -/
def treeAutCard : RoseTree α → ℕ
  | .node _ cs =>
      (cs.map treeAutCard).prod * multinomialFactor (Multiset.ofList (cs.map mk))

theorem treeAutCard_node (a : α) (cs : List (RoseTree α)) :
    treeAutCard (RoseTree.node a cs) =
      (cs.map treeAutCard).prod * multinomialFactor (Multiset.ofList (cs.map mk)) := by
  rw [treeAutCard]

/-! #### `treeAutCard` is `Perm`-invariant -/

mutual
/-- `treeAutCard` is invariant under `Perm`. At a node the algebra reads the
    children only through the child-`treeAutCard` product and the `mk`-multiset,
    both fixed by the `PermList` companion. -/
theorem treeAutCard_perm : ∀ {t s : RoseTree α}, RoseTree.Perm t s →
    treeAutCard t = treeAutCard s
  | _, _, .node h => by
    rw [treeAutCard_node, treeAutCard_node]
    obtain ⟨hprod, hmk⟩ := treeAutCard_permList h
    rw [hprod, hmk]
  | _, _, .trans h₁ h₂ => (treeAutCard_perm h₁).trans (treeAutCard_perm h₂)

/-- The two children statistics `treeAutCard` reads — the child-`treeAutCard`
    product and the `mk`-multiset — are `PermList`-invariant: `cons` matches heads
    by the mutual `treeAutCard_perm` and `mk_eq_mk_iff`, `swap` by commutativity
    of `*` and `Multiset.cons_swap`. -/
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

/-- Every factor in `multinomialFactor M` is positive (each is a factorial). -/
private theorem multinomialFactor_pos (M : Multiset (Nonplanar α)) :
    0 < multinomialFactor M :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

/-- `treeAutCard` is positive: at a node, `multinomialFactor` is positive
    (factorials) and the children product is positive by the IH. -/
theorem treeAutCard_pos (t : RoseTree α) : 0 < treeAutCard t := by
  induction t with
  | node a cs ih =>
    rw [treeAutCard_node]
    refine Nat.mul_pos ?_ (multinomialFactor_pos _)
    exact List.prod_pos_iff_forall_pos_nat.mpr (by simpa using ih)

/-! ### Nonplanar automorphism count via lift -/

/-- The cardinality `|Aut(t)|` of the automorphism group of a rooted
    nonplanar tree `t`.

    Recursive structure: for `t = node a M` with children-multiset `M`,
    `autCard t = ∏ distinct c ∈ M, (M.count c)! * (autCard c)^(M.count c)`
    (see `autCard_node`). A leaf has `autCard = 1` (`autCard_leaf`).

    Defined by lifting `treeAutCard` through the `Perm` quotient. -/
def autCard : Nonplanar α → ℕ :=
  Nonplanar.lift treeAutCard (fun _ _ h => treeAutCard_perm h)

@[simp] theorem autCard_mk (t : RoseTree α) : autCard (mk t) = treeAutCard t := rfl

/-- A leaf has trivial aut group. -/
@[simp] theorem autCard_leaf (a : α) : autCard (Nonplanar.leaf a : Nonplanar α) = 1 := by
  show treeAutCard (RoseTree.leaf a) = 1
  rw [RoseTree.leaf_def, treeAutCard_node]
  simp [multinomialFactor]

/-- The automorphism group of any tree is non-trivial (contains identity).
    Stated as positivity of the cardinality. Descends from
    `treeAutCard_pos` via the quotient. -/
theorem autCard_pos (t : Nonplanar α) : 0 < autCard t :=
  Quotient.inductionOn t treeAutCard_pos

/-- The cardinality `|Aut(F)|` of the automorphism group of a forest
    `F` (multiset of nonplanar trees), defined as the product over
    distinct trees `T ∈ F`:
    ```
    forestAutCard F = ∏_{distinct T ∈ F} (F.count T)! · (autCard T)^(F.count T)
    ```
    Stays in `Nonplanar` namespace (rather than `Forest`) because
    `Forest = Multiset` is just a stylistic alias used at the
    `ConnesKreimer` algebra layer; here we work directly with
    `Multiset (Nonplanar α)` to keep the combinatorics layer free of
    algebra-layer abbreviations. -/
def forestAutCard (F : Multiset (Nonplanar α)) : ℕ :=
  F.toFinset.prod fun t => Nat.factorial (F.count t) * autCard t ^ F.count t

/-- The empty forest has trivial aut group. -/
@[simp] theorem forestAutCard_zero :
    forestAutCard (0 : Multiset (Nonplanar α)) = 1 := by
  simp [forestAutCard]

/-- The aut group of any forest is non-trivial (contains identity).
    Each factor `(F.count t)! * autCard t ^ F.count t` is positive
    (factorial always positive; `autCard_pos` gives the tree factor). -/
theorem forestAutCard_pos (F : Multiset (Nonplanar α)) : 0 < forestAutCard F := by
  unfold forestAutCard
  exact Finset.prod_pos fun t _ =>
    Nat.mul_pos (Nat.factorial_pos _) (pow_pos (autCard_pos t) _)

/-- `treeAutCard` of a representative equals `autCard` of its class. -/
private theorem treeAutCard_out (x : Nonplanar α) :
    treeAutCard x.out = autCard x := by
  conv_rhs => rw [← x.out_eq]
  rfl

/-- The `treeAutCard`-product over `Quotient.out`-representatives of a list
    of nonplanar trees equals the `autCard`-product over the list. -/
private theorem prod_out_treeAutCard (lst : List (Nonplanar α)) :
    ((lst.map Quotient.out).map treeAutCard).prod = (lst.map autCard).prod := by
  congr 1
  rw [List.map_map]
  exact List.map_congr_left fun x _ => treeAutCard_out x

omit [DecidableEq α] in
/-- The mk-multiset of `Q.out`-lifted list of nonplanar trees equals the
    original list. -/
private theorem ofList_map_mk_qout (lst : List (Nonplanar α)) :
    (Multiset.ofList (((lst.map Quotient.out).map mk)) :
        Multiset (Nonplanar α)) = Multiset.ofList lst := by
  rw [List.map_map]
  congr 1
  exact (List.map_congr_left (fun x _ => x.out_eq)).trans (List.map_id lst)

/-- `autCard` on the smart `node` constructor: the recursive definition.
    Proof: induct on `F` to get a list rep `lst`; `treeAutCard` on the
    tree node splits into a children-product factor (which lifts to
    `(lst.map autCard).prod` via `prod_out_treeAutCard`) and a
    `multinomialFactor` factor (which lifts to `multinomialFactor F` via
    `ofList_map_mk_qout`). Combine via `Finset.prod_multiset_map_count`
    (to express `(F.map autCard).prod` as a Finset prod over `F.toFinset`)
    and `Finset.prod_mul_distrib` (to recombine the two legs into
    `forestAutCard F`). -/
@[simp] theorem autCard_node (a : α) (F : Multiset (Nonplanar α)) :
    autCard (Nonplanar.node a F) = forestAutCard F := by
  induction F using Quotient.inductionOn with
  | h lst =>
    -- Convert `Quotient.mk _ lst` to `Multiset.ofList lst` (definitionally equal).
    show treeAutCard (RoseTree.node a (lst.map Quotient.out)) =
        forestAutCard (Multiset.ofList lst)
    rw [treeAutCard_node, prod_out_treeAutCard lst, ofList_map_mk_qout lst]
    -- LHS: (lst.map autCard).prod * multinomialFactor (Multiset.ofList lst).
    -- RHS: forestAutCard (Multiset.ofList lst) =
    --      (Multiset.ofList lst).toFinset.prod fun t => (count t)! * autCard t ^ count t.
    unfold forestAutCard multinomialFactor
    -- (lst.map autCard).prod = ((Multiset.ofList lst).map autCard).prod
    --                       = ∏ t ∈ toFinset, autCard t ^ count t.
    have hprod_lst : ((Multiset.ofList lst).map autCard).prod
                  = ((Multiset.ofList lst).toFinset).prod
                      fun t => autCard t ^ (Multiset.ofList lst).count t :=
      Finset.prod_multiset_map_count (Multiset.ofList lst) autCard
    have hcoe : (lst.map autCard).prod = ((Multiset.ofList lst).map autCard).prod := rfl
    rw [hcoe, hprod_lst]
    -- Combine the two Finset prods via Finset.prod_mul_distrib.
    rw [← Finset.prod_mul_distrib]
    -- Match summands: pow * factorial = factorial * pow.
    apply Finset.prod_congr rfl
    intro t _
    ring

/-! ### Multinomial split identity

The antidiagonal multiplicity `count (F, G) (antidiagonal (F + G))` is the binomial
product `∏ t, C((F+G).count t, G.count t)`
(`Multiset.count_antidiagonal_eq_count_powerset` + `Multiset.count_powerset_of_le`);
recombining it with the factorials per distinct tree
(`Nat.add_choose_mul_factorial_mul_factorial`) yields the split identity below — the
combinatorial core of the pairing's product-coproduct adjunction
(`GrossmanLarsonPairing.pairing_of'_mul_of'`). -/

/-- **Multinomial split identity** for `forestAutCard`:
    `count (F,G) (antidiagonal (F+G)) · |Aut F| · |Aut G| = |Aut (F+G)|`. -/
theorem forestAutCard_add (F G : Multiset (Nonplanar α)) :
    Multiset.count (F, G) (Multiset.antidiagonal (F + G)) *
      (forestAutCard F * forestAutCard G) = forestAutCard (F + G) := by
  have hext : ∀ M : Multiset (Nonplanar α), M ≤ F + G →
      M.toFinset.prod (fun t => Nat.factorial (M.count t) * autCard t ^ M.count t)
        = (F + G).toFinset.prod
            (fun t => Nat.factorial (M.count t) * autCard t ^ M.count t) := by
    intro M hM
    refine Finset.prod_subset
      (Multiset.toFinset_subset.mpr (Multiset.subset_of_le hM)) fun x _ hx => ?_
    rw [Multiset.count_eq_zero.mpr fun hm => hx (Multiset.mem_toFinset.mpr hm)]
    simp
  rw [Multiset.count_antidiagonal_eq_count_powerset,
      Multiset.count_powerset_of_le (Multiset.le_add_left G F)]
  unfold forestAutCard
  rw [hext F (Multiset.le_add_right F G), hext G (Multiset.le_add_left G F),
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Multiset.count_add, pow_add,
      ← Nat.add_choose_mul_factorial_mul_factorial (F.count t) (G.count t)]
  ring

end Nonplanar

end RootedTree
