/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Basic

/-!
# Partial label maps on rose trees

`RoseTree.filterMap f` relabels a rose tree along `f : α → Option β`, dropping every subtree whose
root `f` sends to `none`. The result is `none` exactly when the root itself is dropped. It is the
counterpart on rose trees of `List.filterMap`.

## Main definitions

* `RoseTree.filterMap`, `RoseTree.filterMapList`: the partial map on a tree and on a list of
  children.

## Main results

* `RoseTree.filterMapList_eq_filterMap`: on children the map is `List.filterMap`.
* `RoseTree.filterMap_map`: `filterMap f (map g t) = filterMap (f ∘ g) t`.
* `RoseTree.filterMap_some`: a total map drops nothing.
-/

@[expose] public section

namespace RoseTree

variable {α β γ : Type*}

mutual
/-- `filterMap f t` relabels `t` along `f`, dropping the subtrees whose root `f` sends to `none`.
It is `none` when the root itself is dropped. -/
def filterMap (f : α → Option β) : RoseTree α → Option (RoseTree β)
  | .node a cs => (f a).map fun b ↦ .node b (filterMapList f cs)
/-- `filterMapList f cs` applies `filterMap f` to a list of trees and keeps the results. -/
def filterMapList (f : α → Option β) : List (RoseTree α) → List (RoseTree β)
  | [] => []
  | c :: cs =>
    match filterMap f c with
    | none => filterMapList f cs
    | some t => t :: filterMapList f cs
end

@[simp] theorem filterMap_node (f : α → Option β) (a : α) (cs : List (RoseTree α)) :
    filterMap f (node a cs) = (f a).map fun b ↦ .node b (filterMapList f cs) := rfl

@[simp] theorem filterMapList_nil (f : α → Option β) :
    filterMapList f ([] : List (RoseTree α)) = [] := rfl

theorem filterMapList_eq_filterMap (f : α → Option β) (cs : List (RoseTree α)) :
    filterMapList f cs = cs.filterMap (filterMap f) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [filterMapList, ih]
    cases h : filterMap f c <;> simp [h]

theorem filterMapList_singleton (f : α → Option β) (t : RoseTree α) :
    filterMapList f [t] = (filterMap f t).toList := by
  rw [filterMapList_eq_filterMap]
  cases h : filterMap f t <;> simp [h]

theorem filterMapList_append (f : α → Option β) (l₁ l₂ : List (RoseTree α)) :
    filterMapList f (l₁ ++ l₂) = filterMapList f l₁ ++ filterMapList f l₂ := by
  simp only [filterMapList_eq_filterMap, List.filterMap_append]

/-! ### Composition with total maps -/

theorem filterMap_map (f : β → Option γ) (g : α → β) (t : RoseTree α) :
    filterMap f (map g t) = filterMap (f ∘ g) t := by
  induction t with
  | node a cs ih =>
    simp only [map_node, filterMap_node, filterMapList_eq_filterMap, List.filterMap_map,
      Function.comp_apply]
    rw [List.filterMap_congr fun c hc ↦ ih c hc]

/-- A total map drops nothing. -/
theorem filterMap_some (g : α → β) (t : RoseTree α) :
    filterMap (fun a ↦ some (g a)) t = some (map g t) := by
  induction t with
  | node a cs ih =>
    rw [filterMap_node, map_node, Option.map_some, filterMapList_eq_filterMap,
      List.filterMap_congr ih, ← List.filterMap_eq_map]
    rfl

/-- Injecting on the left and then keeping the left labels is the identity. -/
@[simp] theorem filterMap_getLeft?_map_inl (t : RoseTree α) :
    filterMap Sum.getLeft? (map (Sum.inl : α → α ⊕ β) t) = some t := by
  rw [filterMap_map,
    show (Sum.getLeft? ∘ (Sum.inl : α → α ⊕ β)) = (fun a ↦ some (id a)) from rfl,
    filterMap_some, id_map]

end RoseTree
