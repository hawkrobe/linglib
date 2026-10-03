/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Get

/-!
# Licensed trees

The local trees of a rose tree are its nodes' values, each paired with the values of the node's
children (`RoseTree.localTrees`). A relation `R` between a value and a list of values licenses a
tree when every local tree of the tree satisfies it, and a set of trees defined this way is a
local set. The derivation trees of a context-free grammar are the trees its rules license, and
any well-formedness condition stated on a node and its children takes the same form. A condition
on the root alone is a separate conjunct.

## Main definitions

* `RoseTree.Licensed R t`: every local tree of `t` satisfies `R`.

## Main results

* `RoseTree.licensed_node_iff`: a tree is licensed when its root's local tree satisfies `R` and
  its children are licensed.
* `RoseTree.Licensed.of_subtreeAt`, `RoseTree.licensed_iff_forall_isSubtree`: licensing passes to
  subtrees, and a tree is licensed when every subtree's root local tree satisfies `R`.
* `RoseTree.Licensed.replaceAt`: replacing a subtree by a licensed tree with the same root value
  keeps the tree licensed.
-/

@[expose] public section

namespace RoseTree

open Core.Order.Branching

variable {α : Type*} {R : α → List α → Prop}

/-- A relation `R` licenses `t` when every local tree of `t` satisfies it. -/
def Licensed (R : α → List α → Prop) (t : RoseTree α) : Prop := ∀ e ∈ t.localTrees, R e.1 e.2

instance [∀ a ks, Decidable (R a ks)] (t : RoseTree α) : Decidable (t.Licensed R) :=
  inferInstanceAs (Decidable (∀ e ∈ t.localTrees, R e.1 e.2))

theorem licensed_node_iff {a : α} {cs : List (RoseTree α)} :
    (node a cs).Licensed R ↔ R a (cs.map value) ∧ ∀ c ∈ cs, c.Licensed R := by
  simp only [Licensed, localTrees_node, List.mem_cons, forall_eq_or_imp, List.mem_flatten,
    List.mem_map]
  refine and_congr_right fun _ ↦ ⟨fun h c hc e he ↦ h e ⟨_, ⟨c, hc, rfl⟩, he⟩, ?_⟩
  rintro h e ⟨_, ⟨c, hc, rfl⟩, he⟩
  exact h c hc e he

@[simp] theorem licensed_leaf_iff {a : α} : (leaf a).Licensed R ↔ R a [] := by
  simp [leaf, licensed_node_iff]

/-- In a licensed tree the root's local tree satisfies `R`. -/
theorem Licensed.rel_root {a : α} {cs : List (RoseTree α)} (h : (node a cs).Licensed R) :
    R a (cs.map value) :=
  (licensed_node_iff.mp h).1

theorem Licensed.of_mem {a : α} {cs : List (RoseTree α)} (h : (node a cs).Licensed R)
    {c : RoseTree α} (hc : c ∈ cs) : c.Licensed R :=
  (licensed_node_iff.mp h).2 c hc

theorem Licensed.of_subtreeAt {t s : RoseTree α} (ht : t.Licensed R) {p : List ℕ}
    (hs : subtreeAt t p = some s) : s.Licensed R := by
  induction p generalizing t with
  | nil => exact Option.some.inj hs ▸ ht
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp hs
    cases t with
    | node a cs => exact ih (ht.of_mem (List.mem_of_getElem? hc)) hcs

theorem licensed_iff_forall_isSubtree {t : RoseTree α} :
    t.Licensed R ↔ ∀ s, IsSubtree s t → R s.value (s.children.map value) := by
  refine ⟨fun h s hs ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨p, hp⟩ := isSubtree_iff_exists_subtreeAt.mp hs
    obtain ⟨a, cs⟩ := s
    exact (h.of_subtreeAt hp).rel_root
  · induction t with
    | node a cs ih =>
      refine licensed_node_iff.mpr ⟨h _ (.refl _), fun c hc ↦ ih c hc fun s hs ↦ ?_⟩
      exact h s (hs.trans (IsSubtree.of_isChild hc))

/-- Replacing a subtree by a licensed tree with the same root value keeps a tree licensed. -/
theorem Licensed.replaceAt {t s new : RoseTree α} (ht : t.Licensed R) {p : List ℕ}
    (hs : subtreeAt t p = some s) (hnew : new.Licensed R) (hv : new.value = s.value) :
    (t.replaceAt p new).Licensed R := by
  induction p generalizing t with
  | nil => rw [replaceAt_nil]; exact hnew
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp hs
    cases t with
    | node a cs =>
      rw [branching_children, children_node] at hc
      rw [replaceAt_cons_of_getElem? (by simpa using hc), value_node, children_node]
      have hval : (c.replaceAt p new).value = c.value := by
        cases p with
        | nil => rw [replaceAt_nil, hv, Option.some.inj hcs]
        | cons j p => exact value_replaceAt_cons c j p new
      refine licensed_node_iff.mpr ⟨?_, fun d hd ↦ ?_⟩
      · obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
        have h := List.set_getElem_self (as := cs.map value) (i := i) (by simpa using hi)
        rw [List.getElem_map] at h
        rw [List.map_set, hval, h]
        exact ht.rel_root
      · rcases List.mem_or_eq_of_mem_set hd with hd | rfl
        · exact ht.of_mem hd
        · exact ih (ht.of_mem (List.mem_of_getElem? hc)) hcs

end RoseTree
