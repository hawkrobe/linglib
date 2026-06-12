/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.Nonplanar
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false

/-!
# Automorphism cardinality for rooted nonplanar trees

The cardinality of the automorphism group of a rooted nonplanar tree
(or a forest of such trees), used as the symmetry-weight in the
Connes-Kreimer / Grossman-Larson pairing
(`Linglib/Core/Algebra/RootedTree/GrossmanLarsonPairing.lean`).

## Tree-level formula

For a node with children-multiset `M = {c₁ × k₁, c₂ × k₂, …}` (distinct
trees `cᵢ` with multiplicities `kᵢ`):
```
|Aut(node a M)| = ∏ᵢ kᵢ! · |Aut(cᵢ)|^kᵢ
```
A leaf has `|Aut(leaf)| = 1`.

The factorial factor `kᵢ!` accounts for permutations of identical
children; the power `|Aut(cᵢ)|^kᵢ` accounts for independent choice of
auts within each copy.

## Forest-level formula

For a forest (multiset of trees) `F = {T₁ × m₁, T₂ × m₂, …}`:
```
|Aut(F)| = ∏ⱼ mⱼ! · |Aut(Tⱼ)|^mⱼ
```
Same formula structure as the tree-level case, applied to the
top-level multiset of constituent trees.

## Implementation status

`[UPSTREAM]` candidate. Eventual mathlib home would be
`Mathlib.Combinatorics.RootedTree.Aut`. **Sorry-free.**

`Nonplanar.autCard` descends from `Planar.autCard`, defined by mutual
structural recursion through the children list (`autCardList`
aggregator). `PlanarStep`-invariance is established via the standard
swap/recurse case split, and the lift to `Nonplanar` uses
`Nonplanar.lift`. `autCard_node` bridges to the
`forestAutCard`-as-Finset-product form via `Finset.prod_multiset_map_count`
(turning the all-children prod into a `∏ distinct, c ^ count`-form) +
`Finset.prod_mul_distrib`.

`forestAutCard` is defined in terms of `autCard`.
-/

namespace RootedTree

variable {α : Type*}

/-! ## §1: Planar substrate -/

namespace Planar

/-- Symmetry-factor at one node: `∏_{distinct c ∈ M} (M.count c)!`. Uses
    `Classical.decEq` for `Multiset.toFinset` and `Multiset.count`. -/
noncomputable def multinomialFactor (M : Multiset (Nonplanar α)) : ℕ :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  M.toFinset.prod fun t => Nat.factorial (M.count t)

mutual
/-- Planar version of `Nonplanar.autCard`. Defined by mutual structural
    recursion on the planar tree (with `autCardList` aggregating the
    children product), using `multinomialFactor` on the multiset of
    nonplanar-mk children to count "symmetric" rearrangements; the
    `autCardList cs` factor is the product over all children with
    multiplicity (which equals
    `∏ distinct c, autCard c ^ count c` by
    `Finset.prod_multiset_map_count`). -/
noncomputable def autCard : Planar α → ℕ
  | .node _ cs =>
      autCardList cs *
        multinomialFactor (Multiset.ofList (cs.map Nonplanar.mk))
/-- Mutual aux: product of `autCard` over a children list. -/
noncomputable def autCardList : List (Planar α) → ℕ
  | []      => 1
  | c :: cs => autCard c * autCardList cs
end

@[simp] theorem autCard_node_planar (a : α) (cs : List (Planar α)) :
    autCard (Planar.node a cs) =
      autCardList cs *
        multinomialFactor (Multiset.ofList (cs.map Nonplanar.mk)) := rfl

@[simp] theorem autCardList_nil :
    autCardList ([] : List (Planar α)) = 1 := rfl

@[simp] theorem autCardList_cons (c : Planar α) (cs : List (Planar α)) :
    autCardList (c :: cs) = autCard c * autCardList cs := rfl

/-- `autCardList cs = (cs.map autCard).prod` — bridge to mathlib's
    `List.prod` over a `List.map`. -/
theorem autCardList_eq_prod_map (cs : List (Planar α)) :
    autCardList cs = (cs.map autCard).prod := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [autCardList_cons, List.map_cons, List.prod_cons, ih]

/-! ### `autCard` is `PlanarEquiv`-invariant -/

/-- `autCardList` is invariant under list permutation (it is `List.prod`
    of `List.map autCard` up to `autCardList_eq_prod_map`). -/
private theorem autCardList_perm {cs ds : List (Planar α)}
    (h : List.Perm cs ds) :
    autCardList cs = autCardList ds := by
  rw [autCardList_eq_prod_map, autCardList_eq_prod_map]
  exact (h.map autCard).prod_eq

/-- The mk-multiset is invariant under list permutation. -/
private theorem mk_multiset_perm {cs ds : List (Planar α)} (h : List.Perm cs ds) :
    (Multiset.ofList (cs.map Nonplanar.mk) :
        Multiset (Nonplanar α)) = Multiset.ofList (ds.map Nonplanar.mk) :=
  Multiset.coe_eq_coe.mpr (h.map _)

/-- `Planar.autCard` is invariant under `PlanarStep`. -/
private theorem autCard_planarStep {t s : Planar α} (h : PlanarStep t s) :
    autCard t = autCard s := by
  induction h with
  | @swapAtRoot a l r pre post =>
    -- Children lists are permutations: same `autCardList` and same mk-multiset.
    rw [autCard_node_planar, autCard_node_planar]
    have hperm : List.Perm (pre ++ l :: r :: post) (pre ++ r :: l :: post) :=
      List.Perm.append_left pre (List.Perm.swap r l post)
    rw [autCardList_perm hperm, mk_multiset_perm hperm]
  | @recurse a pre old new post _hstep ih =>
    -- Children lists agree componentwise except at the spot where old → new.
    have hmk : (Nonplanar.mk old : Nonplanar α) = Nonplanar.mk new :=
      Nonplanar.mk_eq_mk_iff.mpr (PlanarEquiv.of_step _hstep)
    -- autCardList legs match by ih.
    have hlist : autCardList (pre ++ old :: post)
               = autCardList (pre ++ new :: post) := by
      rw [autCardList_eq_prod_map, autCardList_eq_prod_map]
      rw [List.map_append, List.map_append, List.map_cons, List.map_cons,
          List.prod_append, List.prod_append, List.prod_cons, List.prod_cons, ih]
    have hmsmk : (Multiset.ofList ((pre ++ old :: post).map Nonplanar.mk) :
                    Multiset (Nonplanar α)) =
                 Multiset.ofList ((pre ++ new :: post).map Nonplanar.mk) := by
      rw [List.map_append, List.map_cons, List.map_append, List.map_cons, hmk]
    rw [autCard_node_planar, autCard_node_planar, hlist, hmsmk]

/-- `Planar.autCard` is invariant under `PlanarEquiv`. -/
theorem autCard_planarEquiv {t s : Planar α} (h : PlanarEquiv t s) :
    autCard t = autCard s := by
  induction h with
  | rel _ _ hstep => exact autCard_planarStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Positivity of `Planar.autCard` -/

/-- Every factor in `multinomialFactor M` is positive (each is a factorial). -/
private theorem multinomialFactor_pos (M : Multiset (Nonplanar α)) :
    0 < multinomialFactor M := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  unfold multinomialFactor
  exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

mutual
/-- `Planar.autCard` is positive. By structural induction: a node's
    autCard is `autCardList * multinomialFactor`; the second factor
    is positive (factorials), and the first is positive iff every child's
    autCard is positive (IH). -/
theorem autCard_pos_planar : ∀ (t : Planar α), 0 < autCard t
  | .node _ cs => by
    rw [autCard_node_planar]
    exact Nat.mul_pos (autCardList_pos cs) (multinomialFactor_pos _)
/-- Mutual aux: `autCardList` is positive. -/
theorem autCardList_pos : ∀ (cs : List (Planar α)), 0 < autCardList cs
  | []      => by rw [autCardList_nil]; exact Nat.one_pos
  | c :: cs => by
    rw [autCardList_cons]
    exact Nat.mul_pos (autCard_pos_planar c) (autCardList_pos cs)
end

end Planar

/-! ## §2: Nonplanar `autCard` via lift -/

namespace Nonplanar

/-- The cardinality `|Aut(t)|` of the automorphism group of a rooted
    nonplanar tree `t`.

    Recursive structure: for `t = node a M` with children-multiset `M`,
    `autCard t = ∏ distinct c ∈ M, (M.count c)! * (autCard c)^(M.count c)`
    (see `autCard_node`). A leaf has `autCard = 1` (`autCard_leaf`).

    Defined by lifting `Planar.autCard` through the `PlanarEquiv`
    quotient. -/
noncomputable def autCard : Nonplanar α → ℕ :=
  Nonplanar.lift Planar.autCard (fun _ _ h => Planar.autCard_planarEquiv h)

@[simp] theorem autCard_mk (t : Planar α) : autCard (mk t) = Planar.autCard t := rfl

/-- A leaf has trivial aut group. -/
@[simp] theorem autCard_leaf (a : α) : autCard (Nonplanar.leaf a : Nonplanar α) = 1 := by
  show Planar.autCard (Planar.leaf a) = 1
  unfold Planar.leaf
  rw [Planar.autCard_node_planar, Planar.autCardList_nil]
  simp [Planar.multinomialFactor]

/-- The automorphism group of any tree is non-trivial (contains identity).
    Stated as positivity of the cardinality. Descends from
    `Planar.autCard_pos_planar` via the quotient. -/
theorem autCard_pos (t : Nonplanar α) : 0 < autCard t := by
  induction t using Quotient.inductionOn with
  | h p => exact Planar.autCard_pos_planar p

/-- The cardinality `|Aut(F)|` of the automorphism group of a forest
    `F` (multiset of nonplanar trees), defined as the product over
    distinct trees `T ∈ F`:
    ```
    forestAutCard F = ∏_{distinct T ∈ F} (F.count T)! · (autCard T)^(F.count T)
    ```
    Uses `Classical.decEq` for the multiset operations (the function is
    noncomputable regardless).

    Stays in `Nonplanar` namespace (rather than `Forest`) because
    `Forest = Multiset` is just a stylistic alias used at the
    `ConnesKreimer` algebra layer; here we work directly with
    `Multiset (Nonplanar α)` to keep the combinatorics layer free of
    algebra-layer abbreviations. -/
noncomputable def forestAutCard (F : Multiset (Nonplanar α)) : ℕ :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  F.toFinset.prod fun t => Nat.factorial (F.count t) * autCard t ^ F.count t

/-- The empty forest has trivial aut group. -/
@[simp] theorem forestAutCard_zero :
    forestAutCard (0 : Multiset (Nonplanar α)) = 1 := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  simp [forestAutCard]

/-- The aut group of any forest is non-trivial (contains identity).
    Each factor `(F.count t)! * autCard t ^ F.count t` is positive
    (factorial always positive; `autCard_pos` gives the tree factor). -/
theorem forestAutCard_pos (F : Multiset (Nonplanar α)) : 0 < forestAutCard F := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  unfold forestAutCard
  exact Finset.prod_pos fun t _ =>
    Nat.mul_pos (Nat.factorial_pos _) (pow_pos (autCard_pos t) _)

/-- The "all children with multiplicity" prod factor in `autCard`, in
    nonplanar form. -/
private theorem autCardList_qout_eq (lst : List (Nonplanar α)) :
    Planar.autCardList (lst.map Quotient.out) =
      (lst.map autCard).prod := by
  induction lst with
  | nil => rfl
  | cons x xs ih =>
    -- ((x :: xs).map Quotient.out) = Quotient.out x :: xs.map Quotient.out
    -- autCardList (Q.out x :: rest.map Q.out) = autCard (Q.out x) * autCardList rest
    rw [show (x :: xs).map autCard = autCard x :: xs.map autCard from rfl,
        List.prod_cons]
    rw [show ((x :: xs).map Quotient.out : List (Planar α)) =
              Quotient.out x :: xs.map Quotient.out from rfl,
        Planar.autCardList_cons, ih]
    -- Goal: Planar.autCard (Q.out x) * (xs.map autCard).prod = autCard x * (xs.map autCard).prod
    congr 1
    -- autCard x = autCard (mk (Q.out x)) = Planar.autCard (Q.out x).
    conv_rhs => rw [← x.out_eq]
    rfl

/-- The mk-multiset of `Q.out`-lifted list of nonplanar trees equals the
    original list. -/
private theorem ofList_map_mk_qout (lst : List (Nonplanar α)) :
    (Multiset.ofList (((lst.map Quotient.out).map Nonplanar.mk)) :
        Multiset (Nonplanar α)) = Multiset.ofList lst := by
  rw [List.map_map]
  congr 1
  exact (List.map_congr_left (fun x _ => x.out_eq)).trans (List.map_id lst)

/-- `autCard` on the smart `node` constructor: the recursive definition.
    Proof: induct on `F` to get a list rep `lst`; unfold `node`, then
    `Planar.autCard` on the planar node; the autCardList factor lifts to
    `(lst.map autCard).prod`; the multinomialFactor factor lifts to
    `multinomialFactor F`. Combine via `Finset.prod_multiset_map_count`
    (to express `(F.map autCard).prod` as a Finset prod over
    `F.toFinset`) and `Finset.prod_mul_distrib` (to recombine the two
    legs into `forestAutCard F`). -/
@[simp] theorem autCard_node (a : α) (F : Multiset (Nonplanar α)) :
    autCard (Nonplanar.node a F) = forestAutCard F := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  induction F using Quotient.inductionOn with
  | h lst =>
    -- Convert `Quotient.mk _ lst` to `Multiset.ofList lst` (definitionally equal).
    show Planar.autCard (Planar.node a (lst.map Quotient.out)) =
        forestAutCard (Multiset.ofList lst)
    rw [Planar.autCard_node_planar, autCardList_qout_eq lst, ofList_map_mk_qout lst]
    -- LHS: (lst.map autCard).prod * multinomialFactor (Multiset.ofList lst).
    -- RHS: forestAutCard (Multiset.ofList lst) =
    --      (Multiset.ofList lst).toFinset.prod fun t => (count t)! * autCard t ^ count t.
    unfold forestAutCard Planar.multinomialFactor
    -- (lst.map autCard).prod = ((Multiset.ofList lst).map autCard).prod
    --                       = ∏ t ∈ toFinset, autCard t ^ count t.
    have hprod_lst : ((Multiset.ofList lst).map autCard).prod
                  = ((Multiset.ofList lst).toFinset).prod
                      fun t => autCard t ^ (Multiset.ofList lst).count t :=
      Finset.prod_multiset_map_count (Multiset.ofList lst) autCard
    -- Massage LHS prod via Multiset coercion: (lst.map autCard).prod = Multiset.prod ↑(...).
    have hcoe : (lst.map autCard).prod = ((Multiset.ofList lst).map autCard).prod := rfl
    rw [hcoe, hprod_lst]
    -- Combine the two Finset prods via Finset.prod_mul_distrib.
    rw [← Finset.prod_mul_distrib]
    -- Match summands: pow * factorial = factorial * pow.
    apply Finset.prod_congr rfl
    intro t _
    ring

end Nonplanar

end RootedTree
