/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.PreLie.InsertSum
public import Linglib.Core.Data.List.Zip
public import Linglib.Core.Data.Multiset.Antidiagonal
public import Linglib.Core.Data.UnorderedTree.DecEq
public import Linglib.Core.Data.UnorderedTree.Basic
public import Mathlib.Data.Multiset.Basic

/-!
# Multi-tree insertion on nonplanar forests

This file defines `UnorderedTree.insertionMultiset F G`, the insertion of a guest forest `G` into
a host forest `F` of nonplanar trees: the multiset, over all assignments of the trees of `G` to
vertices of `F`, of the forests obtained by grafting each guest at its vertex. It is
`RoseTree.insertionForest` read through `UnorderedTree.mk`, and Foissy's formula for the
Guin–Oudom extension of the grafting product. From it the file defines
`UnorderedTree.productMultiset F G`, the forests of the Grossman–Larson product `F ⋆ G`: over the
splits `G = G₁ + G₂`, the graftings of `G₂` into `F` with `G₁` placed alongside.

## Main results

* `insertionMultiset_singleton_singleton`: one host and one guest give the grafting product.
* `map_singleton_bind_insertSum`: two successive graftings, the degree-two case of Oudom and
  Guin's recursion for the extended product.
* `insertionMultiset_singleton_node`: grafting into a single node `node a A` puts the forests of
  `A ⋆ B` under the root.
* `insertionMultiset_add_host`: grafting into a disjoint union splits the guests between the two
  parts, the rule `AB ∘ C = (A ∘ C₍₁₎)(B ∘ C₍₂₎)` of Oudom and Guin's Proposition 3.7.
* `insertionMultiset_antidiagonal`: splits of an output forest are splits of the host and of the
  guests, each guest following its host.
* `productMultiset_zero_left`, `productMultiset_zero_right`: the empty forest is a unit.

## Implementation notes

The definition picks representatives with `Multiset.toList` and `Quotient.out`, so it is
noncomputable; `insertionForest_perm_host_msform` and `insertionForest_msform_invariance_guests`
show that the choice does not matter.

## References

* [foissy-2021]
* [oudom-guin-2008]
-/

@[expose] public section

open RoseTree

namespace UnorderedTree

variable {α : Type*}

/-- `insertionMultiset F G` is the multiset, over the assignments of the trees of `G` to vertices
of `F`, of the forests obtained by grafting each tree at its vertex. -/
noncomputable def insertionMultiset (F G : Multiset (UnorderedTree α)) :
    Multiset (Multiset (UnorderedTree α)) :=
  (insertionForest (F.toList.map Quotient.out) (G.toList.map Quotient.out)).map
    fun L => ↑(L.map mk)

private theorem map_out_map_mk (l : List (UnorderedTree α)) : (l.map Quotient.out).map mk = l := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg₂ _ (Quotient.out_eq x) ih

private theorem permList_map_out_toList (hs : List (RoseTree α)) :
    PermList ((↑(hs.map mk) : Multiset (UnorderedTree α)).toList.map Quotient.out) hs := by
  have h : ((↑(hs.map mk) : Multiset (UnorderedTree α)).toList).Perm (hs.map mk) :=
    Multiset.coe_eq_coe.mp (by rw [Multiset.coe_toList])
  refine (PermList.of_perm (h.map _)).trans (PermList.of_forall₂ ?_)
  clear h
  induction hs with
  | nil => exact .nil
  | cons h hs ih => exact .cons (mk_eq_mk_iff.mp (Quotient.out_eq (mk h))) ih

/-- `insertionMultiset` computes on any planar representatives of the two forests. -/
theorem insertionMultiset_mk (hs gs : List (RoseTree α)) :
    insertionMultiset ↑(hs.map mk) ↑(gs.map mk) =
      (insertionForest hs gs).map fun L => (↑(L.map mk) : Multiset (UnorderedTree α)) := by
  rw [insertionMultiset, insertionForest_permList_host_msform (permList_map_out_toList hs)]
  refine insertionForest_msform_invariance_guests hs (Multiset.coe_eq_coe.mp ?_)
  rw [map_out_map_mk, Multiset.coe_toList]

theorem insertionMultiset_zero_right (F : Multiset (UnorderedTree α)) :
    insertionMultiset F 0 = {F} := by
  induction F using forest_inductionOn with
  | h hs =>
    have h := insertionMultiset_mk hs []
    rwa [insertionForest_nil_guests, Multiset.map_singleton] at h

theorem insertionMultiset_zero_left_of_ne_zero (G : Multiset (UnorderedTree α)) (h : G ≠ 0) :
    insertionMultiset 0 G = 0 := by
  induction G using forest_inductionOn with
  | h gs =>
    cases gs with
    | nil => exact absurd rfl h
    | cons g gs =>
      have h := insertionMultiset_mk [] (g :: gs)
      rwa [insertionForest_empty_host_nonempty_guests, Multiset.map_zero] at h

/-- One host and one guest give the grafting product, each output a one-tree forest. -/
theorem insertionMultiset_singleton_singleton (T S : UnorderedTree α) :
    insertionMultiset {T} {S} = (T ◁ S).map ({·}) := by
  induction T using Quotient.inductionOn with | h t =>
  induction S using Quotient.inductionOn with | h s =>
  rw [quot_mk_eq_mk, quot_mk_eq_mk, ← Multiset.coe_singleton, ← Multiset.coe_singleton,
    ← List.map_singleton, ← List.map_singleton, insertionMultiset_mk, insertionForest_singleton,
    mk_insertSum, Multiset.map_map, Multiset.map_map]
  rfl

/-- Grafting `S₁` into `T` and then `S₂` into the result is grafting `S₁ ◁ S₂` into `T`, plus
grafting `S₁` and `S₂` into `T` at once: the degree-two case `T ∘ BX = (T ∘ B) ∘ X - T ∘ (B ∘ X)`
of Oudom and Guin's Proposition 3.7. -/
theorem map_singleton_bind_insertSum (T S₁ S₂ : UnorderedTree α) :
    ((T ◁ S₁).bind (· ◁ S₂)).map ({·}) =
      ((S₁ ◁ S₂).bind (T ◁ ·)).map ({·}) + insertionMultiset {T} {S₁, S₂} := by
  induction T using Quotient.inductionOn with | h t =>
  induction S₁ using Quotient.inductionOn with | h s₁ =>
  induction S₂ using Quotient.inductionOn with | h s₂ =>
  rw [quot_mk_eq_mk, quot_mk_eq_mk, quot_mk_eq_mk, ← Multiset.coe_singleton, ← List.map_singleton,
    show ({mk s₁, mk s₂} : Multiset (UnorderedTree α)) = ↑([s₁, s₂].map mk) from rfl,
    insertionMultiset_mk, insertionForest_singleton, Multiset.map_map]
  have h := congrArg (Multiset.map fun x : UnorderedTree α => ({x} : Multiset _))
    (map_mk_bind_insertSum t s₁ s₂)
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def] at h
  simp only [mk_insertSum, Multiset.bind_map, ← Multiset.map_bind, Multiset.map_map,
    Function.comp_def]
  rw [h]
  rfl

/-- Every output forest of `insertionMultiset A B` has as many trees as `A`. -/
theorem insertionMultiset_card_eq (A B : Multiset (UnorderedTree α))
    {F : Multiset (UnorderedTree α)} (h : F ∈ insertionMultiset A B) : F.card = A.card := by
  induction A using forest_inductionOn with | h hs =>
  induction B using forest_inductionOn with | h gs =>
  rw [insertionMultiset_mk, Multiset.mem_map] at h
  obtain ⟨L, hL, rfl⟩ := h
  simp [length_of_mem_insertionForest hL]

/-- Grafting into one tree gives one tree with the same root value. -/
theorem insertionMultiset_singleton_value (T : UnorderedTree α) (B : Multiset (UnorderedTree α))
    {F : Multiset (UnorderedTree α)} (h : F ∈ insertionMultiset {T} B) :
    ∃ T', F = {T'} ∧ T'.value = T.value := by
  induction T using Quotient.inductionOn with | h t =>
  induction B using forest_inductionOn with | h gs =>
  rw [quot_mk_eq_mk, ← Multiset.coe_singleton, ← List.map_singleton, insertionMultiset_mk,
    insertionForest_singleton, Multiset.map_map, Multiset.mem_map] at h
  obtain ⟨T', hT', rfl⟩ := h
  exact ⟨mk T', rfl, value_of_mem_insertion hT'⟩

private theorem antidiagonal_mk (l : List (RoseTree α)) :
    Multiset.antidiagonal (↑(l.map mk) : Multiset (UnorderedTree α)) =
      (↑l.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).map
        fun p => (↑(p.1.map mk), ↑(p.2.map mk)) := by
  rw [Multiset.antidiagonal_coe_sublists', List.sublists'_map, List.revzip_map, List.map_map,
    Multiset.map_coe]
  rfl

/-- Splits of an output forest are splits of the host and of the guests, each guest following
its host. -/
theorem insertionMultiset_antidiagonal (A G : Multiset (UnorderedTree α)) :
    (insertionMultiset A G).bind Multiset.antidiagonal =
      A.antidiagonal.bind fun pa => G.antidiagonal.bind fun pg =>
        insertionMultiset pa.1 pg.1 ×ˢ insertionMultiset pa.2 pg.2 := by
  induction A using forest_inductionOn with | h hs =>
  induction G using forest_inductionOn with | h gs =>
  have hL (L : List (RoseTree α)) : Multiset.antidiagonal (↑(L.map mk) : Multiset _) =
      (↑L.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun x =>
        {((↑(x.1.map mk) : Multiset (UnorderedTree α)), ↑(x.2.map mk))} := by
    rw [antidiagonal_mk, Multiset.bind_singleton]
  rw [antidiagonal_mk, antidiagonal_mk, Multiset.bind_map, insertionMultiset_mk, Multiset.bind_map]
  simp only [hL]
  rw [insertionForest_bind_revzip_sublists' hs gs fun L₁ L₂ =>
    {((↑(L₁.map mk) : Multiset (UnorderedTree α)), (↑(L₂.map mk) : Multiset (UnorderedTree α)))}]
  refine Multiset.bind_congr fun h _ => ?_
  rw [Multiset.bind_map]
  refine Multiset.bind_congr fun q _ => ?_
  rw [insertionMultiset_mk, insertionMultiset_mk, Multiset.bind_bind]
  simp only [SProd.sprod, Multiset.product, Multiset.bind_map, Multiset.map_map]
  exact Multiset.bind_congr fun L₁ _ => Multiset.bind_singleton _ _

/-- Grafting into a disjoint union splits the guests between the two parts. -/
theorem insertionMultiset_add_host (A B C : Multiset (UnorderedTree α)) :
    insertionMultiset (A + B) C =
      C.antidiagonal.bind fun p =>
        (insertionMultiset A p.1 ×ˢ insertionMultiset B p.2).map fun q => q.1 + q.2 := by
  induction A using forest_inductionOn with | h as =>
  induction B using forest_inductionOn with | h bs =>
  induction C using forest_inductionOn with | h cs =>
  rw [Multiset.coe_add, ← List.map_append, insertionMultiset_mk, insertionForest_append,
    Multiset.map_bind, antidiagonal_mk, Multiset.bind_map]
  refine Multiset.bind_congr fun p _ => ?_
  rw [insertionMultiset_mk, insertionMultiset_mk]
  simp only [SProd.sprod, Multiset.product, Multiset.map_bind, Multiset.bind_map, Multiset.map_map]
  exact Multiset.bind_congr fun L₁ _ => Multiset.map_congr rfl fun L₂ _ => by simp

/-! ### The Grossman–Larson product -/

/-- `productMultiset F G` is the multiset of forests in the Grossman–Larson product `F ⋆ G`: over
the splits `G = G₁ + G₂`, the forests `X + G₁` with `X` a grafting of the trees of `G₂` onto `F`. -/
noncomputable def productMultiset (F G : Multiset (UnorderedTree α)) :
    Multiset (Multiset (UnorderedTree α)) :=
  G.antidiagonal.bind fun p ↦ (insertionMultiset F p.2).map (· + p.1)

@[simp] theorem productMultiset_zero_right (F : Multiset (UnorderedTree α)) :
    productMultiset F 0 = {F} := by
  simp [productMultiset, insertionMultiset_zero_right]

@[simp] theorem productMultiset_zero_left (G : Multiset (UnorderedTree α)) :
    productMultiset 0 G = {G} := by
  induction G using Multiset.induction with
  | empty => simp [productMultiset, insertionMultiset_zero_right]
  | cons a G ih =>
    rw [productMultiset] at ih ⊢
    rw [Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map, Multiset.bind_map]
    have h (p : Multiset (UnorderedTree α) × Multiset (UnorderedTree α)) :
        (insertionMultiset 0 (a ::ₘ p.2)).map (· + p.1) = 0 := by
      rw [insertionMultiset_zero_left_of_ne_zero _ (Multiset.cons_ne_zero), Multiset.map_zero]
    simp only [Prod.map_fst, Prod.map_snd, id_eq, h, Multiset.bind_zero, zero_add]
    simpa [Multiset.map_bind, Multiset.map_map, Function.comp_def] using
      congrArg (Multiset.map (a ::ₘ ·)) ih

/-- Two one-tree forests multiply to their disjoint union and their graftings. -/
theorem productMultiset_singleton_singleton (T S : UnorderedTree α) :
    productMultiset {T} {S} = {T, S} ::ₘ (T ◁ S).map ({·}) := by
  rw [productMultiset, ← Multiset.cons_zero, Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
  simp [insertionMultiset_zero_right, insertionMultiset_singleton_singleton, add_comm]

/-- Every forest of `F ⋆ G` has at least as many trees as `F`. -/
theorem card_le_of_mem_productMultiset {F G W : Multiset (UnorderedTree α)}
    (h : W ∈ productMultiset F G) : F.card ≤ W.card := by
  obtain ⟨p, -, h⟩ := Multiset.mem_bind.mp h
  obtain ⟨X, hX, rfl⟩ := Multiset.mem_map.mp h
  simp [insertionMultiset_card_eq F p.2 hX]

/-- Grafting into a single node `node a A` puts the forests of `A ⋆ B` under the root: each guest
is a new child of the root or grafted into `A`. -/
theorem insertionMultiset_singleton_node (a : α) (A B : Multiset (UnorderedTree α)) :
    insertionMultiset {node a A} B = (productMultiset A B).map fun F => {node a F} := by
  rw [productMultiset, Multiset.map_bind]
  simp only [Multiset.map_map, Function.comp_def]
  induction A using forest_inductionOn with | h cs =>
  induction B using forest_inductionOn with | h gs =>
  rw [antidiagonal_mk, Multiset.bind_map, node_mk_tree_list, ← Multiset.coe_singleton,
    ← List.map_singleton, insertionMultiset_mk, insertionForest_singleton, Multiset.map_map,
    insertion_node, Multiset.map_bind]
  refine Multiset.bind_congr fun p _ => ?_
  rw [insertionMultiset_mk, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun L _ => ?_
  simp [← node_mk_tree_list, ← Multiset.coe_add, add_comm]

end UnorderedTree
