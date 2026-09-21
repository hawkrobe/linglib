/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Basic

/-!
# Partial label maps on rose trees

`RoseTree.filterMap (f : α → Option β)` relabels a rose tree along `f`, recursively dropping
every subtree whose root label maps to `none`; the result is `none` iff the root itself is
dropped. It is the rose-tree analogue of `List.filterMap`.

## Main definitions

* `RoseTree.filterMap`, `RoseTree.filterMapList`: the mutual tree and children-list partial
  maps.

## Main results

* `RoseTree.filterMap_map`: `filterMap f (map g t) = filterMap (f ∘ g) t`.
* `RoseTree.filterMap_some`: a total map drops nothing,
  `filterMap (fun a => some (g a)) t = some (map g t)`.
-/

@[expose] public section

namespace RoseTree

variable {α β γ : Type*}

mutual

/-- Partially relabel a rose tree: subtrees whose root label maps to
    `none` are dropped, recursively; `none` iff the root itself is
    dropped. -/
def filterMap (f : α → Option β) : RoseTree α → Option (RoseTree β)
  | .node a cs => (f a).map fun b => .node b (RoseTree.filterMapList f cs)

/-- Children-list companion of `RoseTree.filterMap`: partial map over a
    list of trees, dropping the `none` results. -/
def filterMapList (f : α → Option β) :
    List (RoseTree α) → List (RoseTree β)
  | [] => []
  | c :: cs =>
    match RoseTree.filterMap f c with
    | none => RoseTree.filterMapList f cs
    | some t => t :: RoseTree.filterMapList f cs

end

@[simp] theorem filterMap_node (f : α → Option β) (a : α)
    (cs : List (RoseTree α)) :
    RoseTree.filterMap f (RoseTree.node a cs) =
      (f a).map fun b => .node b (RoseTree.filterMapList f cs) := rfl

@[simp] theorem filterMapList_nil (f : α → Option β) :
    RoseTree.filterMapList f ([] : List (RoseTree α)) = [] := rfl

/-- `filterMapList` on a singleton: the head's partial map as a list. -/
theorem filterMapList_singleton (f : α → Option β) (t : RoseTree α) :
    RoseTree.filterMapList f [t] = (RoseTree.filterMap f t).toList := by
  show (match RoseTree.filterMap f t with
          | none => RoseTree.filterMapList f []
          | some t' => t' :: RoseTree.filterMapList f []) = _
  cases RoseTree.filterMap f t <;> rfl

/-- `RoseTree.filterMapList` agrees with `List.filterMap` of the
    per-tree partial map. -/
theorem filterMapList_eq_filterMap (f : α → Option β)
    (cs : List (RoseTree α)) :
    RoseTree.filterMapList f cs = cs.filterMap (RoseTree.filterMap f) := by
  induction cs with
  | nil => rfl
  | cons head tail ih =>
    show (match RoseTree.filterMap f head with
            | none => RoseTree.filterMapList f tail
            | some t => t :: RoseTree.filterMapList f tail) =
         (head :: tail).filterMap (RoseTree.filterMap f)
    cases h : RoseTree.filterMap f head with
    | none => simp [List.filterMap_cons_none h, ih]
    | some t => simp [List.filterMap_cons_some h, ih]

/-- `RoseTree.filterMapList` distributes over list concatenation. -/
theorem filterMapList_append (f : α → Option β)
    (l₁ l₂ : List (RoseTree α)) :
    RoseTree.filterMapList f (l₁ ++ l₂) =
      RoseTree.filterMapList f l₁ ++ RoseTree.filterMapList f l₂ := by
  rw [RoseTree.filterMapList_eq_filterMap, RoseTree.filterMapList_eq_filterMap,
      RoseTree.filterMapList_eq_filterMap, List.filterMap_append]

/-! ## Composition with total maps -/

mutual

/-- Partial-after-total composition: `filterMap f` after `map g` is
    `filterMap (f ∘ g)`. -/
theorem filterMap_map (f : β → Option γ) (g : α → β) :
    ∀ (t : RoseTree α),
      RoseTree.filterMap f (RoseTree.map g t) = RoseTree.filterMap (f ∘ g) t
  | .node a cs => by
    rw [RoseTree.map_node, RoseTree.filterMap_node, RoseTree.filterMap_node,
        RoseTree.filterMapList_mapList f g cs]
    rfl

/-- Children-list companion of `RoseTree.filterMap_map`. -/
theorem filterMapList_mapList (f : β → Option γ) (g : α → β) :
    ∀ (cs : List (RoseTree α)),
      RoseTree.filterMapList f (List.map (RoseTree.map g) cs) =
        RoseTree.filterMapList (f ∘ g) cs
  | [] => rfl
  | c :: cs => by
    show (match RoseTree.filterMap f (RoseTree.map g c) with
            | none => RoseTree.filterMapList f (List.map (RoseTree.map g) cs)
            | some t => t :: RoseTree.filterMapList f (List.map (RoseTree.map g) cs)) = _
    rw [RoseTree.filterMap_map f g c, RoseTree.filterMapList_mapList f g cs]
    rfl

end

mutual

/-- A total map drops nothing: `filterMap (some ∘ g)` is `some ∘ map g`. -/
theorem filterMap_some (g : α → β) :
    ∀ (t : RoseTree α),
      RoseTree.filterMap (fun a => some (g a)) t = some (RoseTree.map g t)
  | .node a cs => by
    rw [RoseTree.filterMap_node, RoseTree.map_node,
        RoseTree.filterMapList_some g cs]
    rfl

/-- Children-list companion of `RoseTree.filterMap_some`. -/
theorem filterMapList_some (g : α → β) :
    ∀ (cs : List (RoseTree α)),
      RoseTree.filterMapList (fun a => some (g a)) cs =
        List.map (RoseTree.map g) cs
  | [] => rfl
  | c :: cs => by
    show (match RoseTree.filterMap (fun a => some (g a)) c with
            | none => RoseTree.filterMapList (fun a => some (g a)) cs
            | some t => t :: RoseTree.filterMapList (fun a => some (g a)) cs) = _
    rw [RoseTree.filterMap_some g c, RoseTree.filterMapList_some g cs]
    rfl

end

/-! ## The `Sum.getLeft?` roundtrip -/

/-- Left injection followed by `Sum.getLeft?`-filtering is the identity. -/
@[simp] theorem filterMap_getLeft?_map_inl (t : RoseTree α) :
    RoseTree.filterMap Sum.getLeft? (RoseTree.map (Sum.inl : α → α ⊕ β) t) =
      some t := by
  rw [RoseTree.filterMap_map,
      show (Sum.getLeft? ∘ (Sum.inl : α → α ⊕ β)) = (fun a => some (id a)) from rfl,
      RoseTree.filterMap_some, RoseTree.id_map]

end RoseTree
