/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
import Linglib.Core.Data.Tree.Basic
import Mathlib.Control.Applicative
import Mathlib.Control.Traversable.Basic

/-!
# Traversable rose tree

`Traversable` and `LawfulTraversable` instances for the n-ary `Tree`, mirroring
`Mathlib.Data.Tree.Traversable` for `BinaryTree`. The lawfulness lemmas recurse
through the child list via `traverseList`, so each is proved with a small
list-level helper fed the per-child induction hypothesis from `Tree.rec'`.
-/

namespace Tree

universe u v w

instance : Traversable Tree where
  map := map
  traverse := traverse

section Laws

variable {α : Type u}

/-! ### `traverse_eq_map_id` -/

private theorem traverseList_eq_map_id {β : Type u} (f : α → β) :
    ∀ (cs : List (Tree α)),
      (∀ c ∈ cs, traverse ((pure : β → Id β) ∘ f) c = pure (map f c)) →
      traverseList ((pure : β → Id β) ∘ f) cs = pure (cs.map (map f))
  | [], _ => rfl
  | c :: cs, h => by
    rw [show traverseList ((pure : β → Id β) ∘ f) (c :: cs)
          = (· :: ·) <$> traverse ((pure : β → Id β) ∘ f) c
              <*> traverseList ((pure : β → Id β) ∘ f) cs from rfl,
      h c (List.mem_cons_self ..),
      traverseList_eq_map_id f cs fun d hd => h d (List.mem_cons_of_mem _ hd)]
    simp

lemma traverse_eq_map_id {β : Type u} (f : α → β) (t : Tree α) :
    traverse ((pure : β → Id β) ∘ f) t = pure (map f t) := by
  induction t with
  | node a cs ih =>
    rw [traverse_node, Function.comp_apply, traverseList_eq_map_id f cs ih, map_node]
    simp

/-! ### `comp_traverse` -/

private theorem comp_traverseList {F G : Type u → Type u} [Applicative F] [Applicative G]
    [LawfulApplicative G] {β γ : Type u} (f : β → F γ) (g : α → G β) :
    ∀ (cs : List (Tree α)),
      (∀ c ∈ cs, traverse (Functor.Comp.mk ∘ (f <$> ·) ∘ g) c =
        Functor.Comp.mk ((·.traverse f) <$> traverse g c)) →
      traverseList (Functor.Comp.mk ∘ (f <$> ·) ∘ g) cs =
        Functor.Comp.mk ((traverseList f ·) <$> traverseList g cs)
  | [], _ => by
    show pure [] = Functor.Comp.mk ((traverseList f ·) <$> (pure [] : G _))
    rw [map_pure]; rfl
  | c :: cs, h => by
    rw [show traverseList (Functor.Comp.mk ∘ (f <$> ·) ∘ g) (c :: cs)
          = (· :: ·) <$> traverse (Functor.Comp.mk ∘ (f <$> ·) ∘ g) c
              <*> traverseList (Functor.Comp.mk ∘ (f <$> ·) ∘ g) cs from rfl,
      h c (List.mem_cons_self ..),
      comp_traverseList f g cs fun d hd => h d (List.mem_cons_of_mem _ hd),
      show traverseList g (c :: cs) = (· :: ·) <$> traverse g c <*> traverseList g cs from rfl]
    simp only [Function.comp_def, Functor.Comp.map_mk, Functor.map_map,
      Comp.seq_mk, seq_map_assoc, map_seq]
    rfl

lemma comp_traverse {F G : Type u → Type u} [Applicative F] [Applicative G]
    [LawfulApplicative G] {β γ : Type u} (f : β → F γ) (g : α → G β) (t : Tree α) :
    t.traverse (Functor.Comp.mk ∘ (f <$> ·) ∘ g) =
      Functor.Comp.mk ((·.traverse f) <$> (t.traverse g)) := by
  induction t with
  | node a cs ih =>
    rw [traverse_node, comp_traverseList f g cs ih, traverse_node]
    simp only [Function.comp_def, Functor.Comp.map_mk, Functor.map_map,
      Comp.seq_mk, seq_map_assoc, map_seq]
    rfl

/-! ### `naturality` -/

private theorem naturalityList {F G : Type u → Type u} [Applicative F] [Applicative G]
    [LawfulApplicative F] [LawfulApplicative G] (η : ApplicativeTransformation F G) {β : Type u}
    (f : α → F β) :
    ∀ (cs : List (Tree α)),
      (∀ c ∈ cs, η (traverse f c) = traverse (η.app β ∘ f) c) →
      η (traverseList f cs) = traverseList (η.app β ∘ f) cs
  | [], _ => by
    rw [show traverseList f [] = pure [] from rfl, η.preserves_pure]; rfl
  | c :: cs, h => by
    rw [show traverseList f (c :: cs) = (· :: ·) <$> traverse f c <*> traverseList f cs from rfl,
      η.preserves_seq, η.preserves_map, h c (List.mem_cons_self ..),
      naturalityList η f cs fun d hd => h d (List.mem_cons_of_mem _ hd)]
    rfl

lemma naturality {F G : Type u → Type u} [Applicative F] [Applicative G] [LawfulApplicative F]
    [LawfulApplicative G] (η : ApplicativeTransformation F G) {β : Type u} (f : α → F β)
    (t : Tree α) : η (t.traverse f) = t.traverse (η.app β ∘ f : α → G β) := by
  induction t with
  | node a cs ih =>
    rw [traverse_node, η.preserves_seq, η.preserves_map, naturalityList η f cs ih, traverse_node,
      Function.comp_apply]

instance : LawfulTraversable Tree where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map
  id_traverse t := traverse_pure t
  comp_traverse := comp_traverse
  traverse_eq_map_id := traverse_eq_map_id
  naturality η := naturality η

end Laws

end Tree
