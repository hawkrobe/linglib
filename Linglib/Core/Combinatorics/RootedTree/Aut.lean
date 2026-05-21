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
import Mathlib.Tactic.Ring

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

In this file the formula is realised as
```
|Aut(node a cs_planar)| = (∏_{t ∈ distinct nonplanar classes} kₜ!) *
                          (∏_{c ∈ cs_planar} |Aut(c)|)
```
which is structurally equivalent (each distinct class `t` contributes
`kₜ!` once, and the per-child product over the planar list contributes
`|Aut(c)|^kₜ` once per class once we group identical children).

## Forest-level formula

For a forest (multiset of trees) `F = {T₁ × m₁, T₂ × m₂, …}`:
```
|Aut(F)| = ∏ⱼ mⱼ! · |Aut(Tⱼ)|^mⱼ
```
Same formula structure as the tree-level case, applied to the
top-level multiset of constituent trees.

## Implementation strategy

`Planar.autCard` is defined by structural recursion via a mutual
companion `Planar.autCardList`. Children are grouped by Nonplanar
equivalence (via `Nonplanar.mk`) for the stabiliser-factor; the
per-child product runs over the planar list directly. PlanarStep /
PlanarEquiv invariance follows from list-permutation invariance
(swapAtRoot) + per-child equality (recurse). `Nonplanar.autCard` is
the lift via `Nonplanar.lift`.

## Layer status

`[UPSTREAM]` candidate. Eventual mathlib home would be
`Mathlib.Combinatorics.RootedTree.Aut`. Sorry-free.
-/

namespace RootedTree

namespace Planar

variable {α : Type*}

/-! ### Planar-level autCard via mutual recursion -/

mutual

/-- Planar-level autCard. Children are grouped by Nonplanar equivalence
    class (via `Nonplanar.mk`); each class contributes its multiplicity
    factorial to the stabiliser factor. The per-child product runs over
    the planar list directly. Together this realises the
    `∏ kᵢ! · |Aut(cᵢ)|^kᵢ` formula. -/
noncomputable def autCard : Planar α → ℕ
  | .node _ cs =>
    letI : DecidableEq (Nonplanar α) := Classical.decEq _
    let ns : Multiset (Nonplanar α) := Multiset.ofList (cs.map Nonplanar.mk)
    (ns.toFinset.prod fun t => Nat.factorial (ns.count t)) * autCardList cs

/-- List companion: per-child autCard product. -/
noncomputable def autCardList : List (Planar α) → ℕ
  | []      => 1
  | c :: cs => autCard c * autCardList cs

end

@[simp] theorem autCardList_nil :
    autCardList ([] : List (Planar α)) = 1 := rfl

@[simp] theorem autCardList_cons (c : Planar α) (cs : List (Planar α)) :
    autCardList (c :: cs) = autCard c * autCardList cs := rfl

theorem autCard_node (a : α) (cs : List (Planar α)) :
    autCard (Planar.node a cs) =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       let ns : Multiset (Nonplanar α) := Multiset.ofList (cs.map Nonplanar.mk)
       (ns.toFinset.prod fun t => Nat.factorial (ns.count t)) * autCardList cs) := rfl

@[simp] theorem autCard_leaf (a : α) : autCard (Planar.leaf a : Planar α) = 1 := by
  show autCard (Planar.node a []) = 1
  rw [autCard_node]
  simp [autCardList]

/-! ### Invariance under permutation, PlanarStep, PlanarEquiv -/

theorem autCardList_perm {l₁ l₂ : List (Planar α)} (h : l₁.Perm l₂) :
    autCardList l₁ = autCardList l₂ := by
  induction h with
  | nil => rfl
  | @cons c _ _ _ ih => simp [autCardList, ih]
  | @swap _ _ _ => simp only [autCardList_cons]; ring
  | @trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem autCardList_subst_at_position
    (pre : List (Planar α)) {old new : Planar α} (post : List (Planar α))
    (heq : autCard old = autCard new) :
    autCardList (pre ++ old :: post) = autCardList (pre ++ new :: post) := by
  induction pre with
  | nil =>
    show autCard old * autCardList post = autCard new * autCardList post
    rw [heq]
  | cons _ cs ih_cs =>
    show autCard _ * autCardList (cs ++ old :: post) =
         autCard _ * autCardList (cs ++ new :: post)
    rw [ih_cs]

/-- `autCard` is invariant under `PlanarStep`. Proven by induction on
    the step: `swapAtRoot` uses list-permutation invariance of both
    the children-multiset and the per-child product; `recurse` uses
    per-child equality via IH. -/
theorem autCard_planarStep : ∀ {t s : Planar α}, PlanarStep t s → autCard t = autCard s
  | _, _, @PlanarStep.swapAtRoot _ a l r pre post => by
    rw [autCard_node, autCard_node]
    have hperm : (pre ++ l :: r :: post).Perm (pre ++ r :: l :: post) :=
      List.Perm.append_left _ (.swap r l post)
    have hms_eq :
        Multiset.ofList (List.map Nonplanar.mk (pre ++ l :: r :: post)) =
        Multiset.ofList (List.map Nonplanar.mk (pre ++ r :: l :: post)) :=
      Multiset.coe_eq_coe.mpr (hperm.map _)
    rw [hms_eq, autCardList_perm hperm]
  | _, _, @PlanarStep.recurse _ a pre old new post hstep => by
    rw [autCard_node, autCard_node]
    have heq : autCard old = autCard new := autCard_planarStep hstep
    have hmk : Nonplanar.mk old = Nonplanar.mk new :=
      Nonplanar.mk_eq_mk_iff.mpr (PlanarEquiv.of_step hstep)
    have hmk_list :
        (List.map Nonplanar.mk (pre ++ old :: post)) =
        (List.map Nonplanar.mk (pre ++ new :: post)) := by
      simp only [List.map_append, List.map_cons, hmk]
    rw [hmk_list, autCardList_subst_at_position pre post heq]

/-- `autCard` is invariant under `PlanarEquiv`, the equivalence closure
    of `PlanarStep`. -/
theorem autCard_planarEquiv {t s : Planar α} (h : PlanarEquiv t s) :
    autCard t = autCard s := by
  induction h with
  | rel _ _ hstep => exact autCard_planarStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Positivity -/

mutual

/-- Every planar tree has positive autCard (the identity automorphism). -/
theorem autCard_pos : ∀ (t : Planar α), 0 < autCard t
  | .node _ cs => by
    rw [autCard_node]
    letI : DecidableEq (Nonplanar α) := Classical.decEq _
    exact Nat.mul_pos
      (Finset.prod_pos (fun _ _ => Nat.factorial_pos _))
      (autCardList_pos cs)

theorem autCardList_pos : ∀ (cs : List (Planar α)), 0 < autCardList cs
  | [] => by simp [autCardList]
  | c :: cs => by
    rw [autCardList_cons]
    exact Nat.mul_pos (autCard_pos c) (autCardList_pos cs)

end

end Planar

namespace Nonplanar

variable {α : Type*}

/-- The cardinality `|Aut(t)|` of the automorphism group of a rooted
    nonplanar tree `t`. Lifted from `Planar.autCard` via
    `PlanarEquiv`-invariance.

    Concrete formula (for `t = mk (node a cs)`):
    ```
    autCard t = (∏_{c ∈ (cs.map mk).toFinset}
                   ((cs.map mk).count c).factorial)
              * (∏_{c ∈ cs} Planar.autCard c)
    ```
    The first factor counts permutations of equivalent children; the
    second is the product of children's individual aut cards. -/
noncomputable def autCard : Nonplanar α → ℕ :=
  Nonplanar.lift Planar.autCard
    (fun _ _ h => Planar.autCard_planarEquiv h)

@[simp] theorem autCard_mk (t : Planar α) :
    autCard (Nonplanar.mk t) = t.autCard := rfl

@[simp] theorem autCard_leaf (a : α) :
    autCard (Nonplanar.leaf a : Nonplanar α) = 1 := by
  show (Planar.leaf a).autCard = 1
  exact Planar.autCard_leaf a

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

/-- Every nonplanar tree has positive autCard. -/
theorem autCard_pos (t : Nonplanar α) : 0 < autCard t := by
  induction t using Quotient.inductionOn with
  | h t => exact Planar.autCard_pos t

/-- Every forest has positive autCard. -/
theorem forestAutCard_pos (F : Multiset (Nonplanar α)) : 0 < forestAutCard F := by
  unfold forestAutCard
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  exact Finset.prod_pos
    (fun t _ => Nat.mul_pos (Nat.factorial_pos _) (pow_pos (autCard_pos t) _))

/-- A node's autCard equals the forest-aut card of its children-multiset.
    Proof: take a planar representative of `Nonplanar.node a F`, unfold
    `Planar.autCard` (= `stabilizer * autCardList`), and show
    `(stabilizer × autCardList over children) = forestAutCard F` using
    `prod_multiset_map_count` to convert per-list product to per-distinct
    pow. -/
theorem autCard_node (a : α) (F : Multiset (Nonplanar α)) :
    autCard (Nonplanar.node a F) = forestAutCard F := by
  obtain ⟨lst, hlst⟩ : ∃ lst : List (Nonplanar α), F = ↑lst :=
    ⟨F.toList, F.coe_toList.symm⟩
  subst hlst
  show autCard (Nonplanar.node a (Multiset.ofList lst)) =
       forestAutCard (Multiset.ofList lst)
  show Planar.autCard (Planar.node a (lst.map Quotient.out)) =
       forestAutCard (Multiset.ofList lst)
  rw [Planar.autCard_node]
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- Identify (lst.map Quotient.out).map mk = lst.
  have h_lst_map : List.map Nonplanar.mk (List.map Quotient.out lst) = lst := by
    rw [List.map_map]
    induction lst with
    | nil => rfl
    | cons head tail ih =>
      show (Nonplanar.mk ∘ Quotient.out) head ::
            List.map (Nonplanar.mk ∘ Quotient.out) tail = head :: tail
      rw [ih]
      show (Nonplanar.mk ∘ Quotient.out) head :: tail = head :: tail
      rw [show (Nonplanar.mk ∘ Quotient.out) head = head from head.out_eq]
  -- Goal: stabilizer-factor * Planar.autCardList = forestAutCard ↑lst.
  show ((Multiset.ofList (List.map Nonplanar.mk (List.map Quotient.out lst))).toFinset.prod
          fun t => (Multiset.count t
            (Multiset.ofList (List.map Nonplanar.mk (List.map Quotient.out lst)))).factorial) *
        Planar.autCardList (List.map Quotient.out lst) =
        forestAutCard (Multiset.ofList lst)
  rw [h_lst_map]
  -- Bridge planar autCardList to a list-product of Nonplanar.autCard's.
  have h_autList : ∀ (xs : List (Nonplanar α)),
      Planar.autCardList (List.map Quotient.out xs) =
      (List.map Nonplanar.autCard xs).prod := by
    intro xs
    induction xs with
    | nil => rfl
    | cons head tail ih =>
      show Planar.autCard (Quotient.out head) * Planar.autCardList _ =
           Nonplanar.autCard head * (List.map Nonplanar.autCard tail).prod
      rw [ih]
      congr 1
      show Planar.autCard (Quotient.out head) = Nonplanar.autCard head
      conv_rhs => rw [← head.out_eq]
      rfl
  rw [h_autList]
  -- Bridge list-product to (↑lst).toFinset.prod via Finset.prod_multiset_map_count.
  have h_prod_count := Finset.prod_multiset_map_count (Multiset.ofList lst)
                         Nonplanar.autCard
  rw [Multiset.map_coe, Multiset.prod_coe] at h_prod_count
  -- h_prod_count : (lst.map autCard).prod = (↑lst).toFinset.prod (autCard · ^ count ·)
  rw [h_prod_count]
  -- Now: (∏ count!) * (∏ autCard^count) = ∏ (count! * autCard^count).
  unfold forestAutCard
  rw [← Finset.prod_mul_distrib]

end Nonplanar

end RootedTree
