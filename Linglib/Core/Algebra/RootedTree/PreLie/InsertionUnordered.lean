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
* `productMultiset_bind_antidiagonal`: splits of the forests of `F ⋆ G` are products of splits of
  `F` and of `G`.

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

/-! ### Splits of a product

Splitting the forests of `F ⋆ G` is splitting `F` and `G` and multiplying the parts. This is the
multiset form of the compatibility between the Grossman–Larson product and the coproduct of the
symmetric algebra, Oudom and Guin's Lemma 3.11. -/

/-- `(s ×ˢ t).bind F = s.bind (a ↦ t.bind (b ↦ F (a, b)))`. -/
private theorem product_bind {β γ δ : Type*} (s : Multiset β) (t : Multiset γ)
    (F : β × γ → Multiset δ) :
    (s ×ˢ t).bind F = s.bind (fun a => t.bind (fun b => F (a, b))) := by
  show (s.bind (fun a => t.map (Prod.mk a))).bind F = _
  rw [Multiset.bind_assoc]
  exact Multiset.bind_congr fun a _ => Multiset.bind_map t F (Prod.mk a)

/-- `(s.bind f) ×ˢ t = s.bind (a ↦ f a ×ˢ t)`. -/
private theorem bind_product_left {β γ δ : Type*} (s : Multiset β)
    (f : β → Multiset γ) (t : Multiset δ) :
    (s.bind f) ×ˢ t = s.bind (fun a => f a ×ˢ t) := by
  show (s.bind f).bind (fun a => t.map (Prod.mk a)) = _
  rw [Multiset.bind_assoc]
  rfl

/-- `s ×ˢ (t.bind g) = t.bind (b ↦ s ×ˢ g b)`. -/
private theorem product_bind_right {β γ δ : Type*} (s : Multiset β)
    (t : Multiset γ) (g : γ → Multiset δ) :
    s ×ˢ (t.bind g) = t.bind (fun b => s ×ˢ g b) := by
  show s.bind (fun a => (t.bind g).map (Prod.mk a)) = _
  rw [show (fun a => (t.bind g).map (Prod.mk a)) =
      fun a => t.bind (fun b => (g b).map (Prod.mk a)) from
    funext fun a => Multiset.map_bind t g (Prod.mk a)]
  rw [Multiset.bind_bind]
  rfl

/-- `(s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g)`. -/
private theorem map_product_map {β γ β' γ' : Type*} (s : Multiset β) (t : Multiset γ)
    (f : β → β') (g : γ → γ') :
    (s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g) := by
  show (s.map f).bind (fun a => (t.map g).map (Prod.mk a)) = _
  rw [Multiset.bind_map]
  show (s.bind fun a => (t.map g).map (Prod.mk (f a))) = _
  rw [show (fun a => (t.map g).map (Prod.mk (f a))) =
      fun a => t.map (fun b => (f a, g b)) from
    funext fun a => by rw [Multiset.map_map]; rfl]
  show _ = ((s.bind fun a => t.map (Prod.mk a)).map (Prod.map f g))
  rw [Multiset.map_bind]
  refine Multiset.bind_congr fun a _ => ?_
  rw [Multiset.map_map]
  rfl

/-- The four-way splits of a multiset, as the splits of the two halves of a split. -/
private def quadBind {β γ : Type*} (B : Multiset β)
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    Multiset γ :=
  (Multiset.antidiagonal B).bind (fun p =>
    (Multiset.antidiagonal p.1).bind (fun u =>
      (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))

private theorem quadBind_zero {β γ : Type*}
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    quadBind 0 g = g 0 0 0 0 := by
  simp only [quadBind, Multiset.antidiagonal_zero, Multiset.singleton_bind]

private theorem quadBind_cons {β γ : Type*} (x : β) (B : Multiset β)
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    quadBind (x ::ₘ B) g =
      quadBind B (fun a b c d => g (x ::ₘ a) b c d) +
      quadBind B (fun a b c d => g a (x ::ₘ b) c d) +
      quadBind B (fun a b c d => g a b (x ::ₘ c) d) +
      quadBind B (fun a b c d => g a b c (x ::ₘ d)) := by
  have h2 : (((Multiset.antidiagonal B).map (Prod.map id (x ::ₘ ·))).bind
        (fun p => (Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))) =
      quadBind B (fun a b c d => g a b c (x ::ₘ d)) +
      quadBind B (fun a b c d => g a b (x ::ₘ c) d) := by
    rw [Multiset.bind_map]
    have step : ∀ p ∈ Multiset.antidiagonal B,
        ((Multiset.antidiagonal (Prod.map id (x ::ₘ ·) p).1).bind (fun u =>
          (Multiset.antidiagonal (Prod.map id (x ::ₘ ·) p).2).bind (fun v =>
            g u.1 u.2 v.1 v.2))) =
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 (x ::ₘ v.2)))) +
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 (x ::ₘ v.1) v.2))) := by
      intro p _
      have inner : ∀ u : Multiset β × Multiset β,
          ((Multiset.antidiagonal (x ::ₘ p.2)).bind (fun v => g u.1 u.2 v.1 v.2)) =
          ((Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 (x ::ₘ v.2))) +
          ((Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 (x ::ₘ v.1) v.2)) := by
        intro u
        rw [Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map,
            Multiset.bind_map]
        rfl
      show ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal (x ::ₘ p.2)).bind (fun v => g u.1 u.2 v.1 v.2))) = _
      rw [Multiset.bind_congr (fun u _ => inner u), Multiset.bind_add]
    rw [Multiset.bind_congr step, Multiset.bind_add]
    rfl
  have h1 : (((Multiset.antidiagonal B).map (Prod.map (x ::ₘ ·) id)).bind
        (fun p => (Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))) =
      quadBind B (fun a b c d => g a (x ::ₘ b) c d) +
      quadBind B (fun a b c d => g (x ::ₘ a) b c d) := by
    rw [Multiset.bind_map]
    have step : ∀ p ∈ Multiset.antidiagonal B,
        ((Multiset.antidiagonal (Prod.map (x ::ₘ ·) id p).1).bind (fun u =>
          (Multiset.antidiagonal (Prod.map (x ::ₘ ·) id p).2).bind (fun v =>
            g u.1 u.2 v.1 v.2))) =
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 (x ::ₘ u.2) v.1 v.2))) +
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g (x ::ₘ u.1) u.2 v.1 v.2))) := by
      intro p _
      show ((Multiset.antidiagonal (x ::ₘ p.1)).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2))) = _
      rw [Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map,
          Multiset.bind_map]
      rfl
    rw [Multiset.bind_congr step, Multiset.bind_add]
    rfl
  show ((Multiset.antidiagonal (x ::ₘ B)).bind (fun p =>
      (Multiset.antidiagonal p.1).bind (fun u =>
        (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))) = _
  rw [Multiset.antidiagonal_cons, Multiset.add_bind, h2, h1]
  abel

private theorem quadBind_middle_swap {β γ : Type*} (B : Multiset β)
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    quadBind B g = quadBind B (fun a b c d => g a c b d) := by
  induction B using Multiset.induction_on generalizing g with
  | empty => rw [quadBind_zero, quadBind_zero]
  | cons x B ih =>
    rw [quadBind_cons, quadBind_cons]
    rw [← ih (fun a b c d => g (x ::ₘ a) b c d),
        ← ih (fun a b c d => g a b (x ::ₘ c) d),
        ← ih (fun a b c d => g a (x ::ₘ b) c d),
        ← ih (fun a b c d => g a b c (x ::ₘ d))]
    abel

/-- Splitting the forests of `A ⋆ B` is splitting `A` and `B` and multiplying the parts. -/
theorem productMultiset_bind_antidiagonal (A B : Multiset (UnorderedTree α)) :
    (productMultiset A B).bind Multiset.antidiagonal =
      (Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).bind (fun pq =>
        productMultiset pq.1.1 pq.2.1 ×ˢ productMultiset pq.1.2 pq.2.2) := by
  -- Split each output forest `X + p.1` as a split of `X` plus a split of `p.1`.
  have stepACD : ∀ p ∈ Multiset.antidiagonal B,
      ((insertionMultiset A p.2).map (· + p.1)).bind Multiset.antidiagonal =
      (Multiset.antidiagonal A).bind (fun pa =>
        (Multiset.antidiagonal p.2).bind (fun pH =>
          (Multiset.antidiagonal p.1).bind (fun q =>
            (insertionMultiset pa.1 pH.1 ×ˢ
              insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2))))) := by
    intro p _
    have h1 : ((insertionMultiset A p.2).map (· + p.1)).bind
          Multiset.antidiagonal =
        ((insertionMultiset A p.2).bind Multiset.antidiagonal).bind
          (fun r => (Multiset.antidiagonal p.1).map
            (fun q => (r.1 + q.1, r.2 + q.2))) := by
      rw [Multiset.bind_map, Multiset.bind_assoc]
      exact Multiset.bind_congr fun X _ => Multiset.antidiagonal_add X p.1
    rw [h1, insertionMultiset_antidiagonal, Multiset.bind_assoc]
    refine Multiset.bind_congr fun pa _ => ?_
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun pH _ => ?_
    exact Multiset.bind_map_comm _ _
  rw [productMultiset, Multiset.bind_assoc, Multiset.bind_congr stepACD, Multiset.bind_bind,
    product_bind]
  refine Multiset.bind_congr fun pa _ => ?_
  -- Commute the two inner antidiagonal binds to reach `quadBind` shape.
  rw [Multiset.bind_congr fun pb _ => Multiset.bind_bind _ _]
  rw [show ((Multiset.antidiagonal B).bind (fun pb =>
      (Multiset.antidiagonal pb.1).bind (fun q =>
        (Multiset.antidiagonal pb.2).bind (fun pH =>
          (insertionMultiset pa.1 pH.1 ×ˢ
            insertionMultiset pa.2 pH.2).map
            (fun pX => (pX.1 + q.1, pX.2 + q.2)))))) =
    quadBind B (fun a b c d =>
      (insertionMultiset pa.1 c ×ˢ
        insertionMultiset pa.2 d).map
        (fun pX => (pX.1 + a, pX.2 + b))) from rfl]
  rw [quadBind_middle_swap]
  refine Multiset.bind_congr fun pb _ => ?_
  rw [productMultiset, productMultiset, bind_product_left]
  refine Multiset.bind_congr fun u _ => ?_
  rw [product_bind_right]
  refine Multiset.bind_congr fun v _ => ?_
  rw [map_product_map]
  rfl

end UnorderedTree
