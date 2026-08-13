/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.Nonplanar

open RoseTree

/-!
# Partial label maps on rose trees

`RoseTree.filterMap (f : α → Option β)` relabels a rose tree along `f`,
recursively dropping every subtree whose root label maps to `none`; the
result is `none` iff the root itself is dropped. The rose-tree analogue
of `List.filterMap`, with `RoseTree.Nonplanar.filterMap` its descent
through the `Perm` quotient.

## Main definitions

* `RoseTree.filterMap`, `RoseTree.filterMapList` — the mutual tree /
  children-list partial maps.
* `RoseTree.Nonplanar.filterMap` — the descent through the `Perm`
  quotient.

## Main results

* `RoseTree.filterMap_map` — `filterMap f (map g t) = filterMap (f ∘ g) t`.
* `RoseTree.filterMap_some` — a total map drops nothing:
  `filterMap (fun a => some (g a)) t = some (map g t)`.
-/

variable {α β γ : Type*}

mutual

/-- Partially relabel a rose tree: subtrees whose root label maps to
    `none` are dropped, recursively; `none` iff the root itself is
    dropped. -/
def RoseTree.filterMap (f : α → Option β) : RoseTree α → Option (RoseTree β)
  | .node a cs => (f a).map fun b => .node b (RoseTree.filterMapList f cs)

/-- Children-list companion of `RoseTree.filterMap`: partial map over a
    list of trees, dropping the `none` results. -/
def RoseTree.filterMapList (f : α → Option β) :
    List (RoseTree α) → List (RoseTree β)
  | [] => []
  | c :: cs =>
    match RoseTree.filterMap f c with
    | none => RoseTree.filterMapList f cs
    | some t => t :: RoseTree.filterMapList f cs

end

@[simp] theorem RoseTree.filterMap_node (f : α → Option β) (a : α)
    (cs : List (RoseTree α)) :
    RoseTree.filterMap f (RoseTree.node a cs) =
      (f a).map fun b => .node b (RoseTree.filterMapList f cs) := rfl

@[simp] theorem RoseTree.filterMapList_nil (f : α → Option β) :
    RoseTree.filterMapList f ([] : List (RoseTree α)) = [] := rfl

/-- `filterMapList` on a singleton: the head's partial map as a list. -/
theorem RoseTree.filterMapList_singleton (f : α → Option β) (t : RoseTree α) :
    RoseTree.filterMapList f [t] = (RoseTree.filterMap f t).toList := by
  show (match RoseTree.filterMap f t with
          | none => RoseTree.filterMapList f []
          | some t' => t' :: RoseTree.filterMapList f []) = _
  cases RoseTree.filterMap f t <;> rfl

/-- `RoseTree.filterMapList` agrees with `List.filterMap` of the
    per-tree partial map. -/
theorem RoseTree.filterMapList_eq_filterMap (f : α → Option β)
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
theorem RoseTree.filterMapList_append (f : α → Option β)
    (l₁ l₂ : List (RoseTree α)) :
    RoseTree.filterMapList f (l₁ ++ l₂) =
      RoseTree.filterMapList f l₁ ++ RoseTree.filterMapList f l₂ := by
  rw [RoseTree.filterMapList_eq_filterMap, RoseTree.filterMapList_eq_filterMap,
      RoseTree.filterMapList_eq_filterMap, List.filterMap_append]

/-! ## Composition with total maps -/

mutual

/-- Partial-after-total composition: `filterMap f` after `map g` is
    `filterMap (f ∘ g)`. -/
theorem RoseTree.filterMap_map (f : β → Option γ) (g : α → β) :
    ∀ (t : RoseTree α),
      RoseTree.filterMap f (RoseTree.map g t) = RoseTree.filterMap (f ∘ g) t
  | .node a cs => by
    rw [RoseTree.map_node, RoseTree.filterMap_node, RoseTree.filterMap_node,
        RoseTree.filterMapList_mapList f g cs]
    rfl

/-- Children-list companion of `RoseTree.filterMap_map`. -/
theorem RoseTree.filterMapList_mapList (f : β → Option γ) (g : α → β) :
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
theorem RoseTree.filterMap_some (g : α → β) :
    ∀ (t : RoseTree α),
      RoseTree.filterMap (fun a => some (g a)) t = some (RoseTree.map g t)
  | .node a cs => by
    rw [RoseTree.filterMap_node, RoseTree.map_node,
        RoseTree.filterMapList_some g cs]
    rfl

/-- Children-list companion of `RoseTree.filterMap_some`. -/
theorem RoseTree.filterMapList_some (g : α → β) :
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

/-! ## Descent to `Nonplanar`

`RoseTree.filterMap f ∘ Nonplanar.mk` is well-defined modulo `Perm`:
`Perm` permutes children, `filterMapList` commutes with permutations up
to `List.Perm`, and child-list order collapses at the `Nonplanar.mk`
level. -/

/-- The Perm-invariant filterMap-then-mk composition, lifted through the
    quotient by `RoseTree.Nonplanar.filterMap`. -/
private def filterMapQuotient (f : α → Option β) (t : RoseTree α) :
    Option (Nonplanar β) :=
  (RoseTree.filterMap f t).map Nonplanar.mk

mutual

/-- **Perm invariance** of the filterMap-then-mk composition. -/
private theorem filterMapQuotient_perm (f : α → Option β) :
    ∀ {t t' : RoseTree α}, RoseTree.Perm t t' →
      filterMapQuotient f t = filterMapQuotient f t'
  | _, _, @RoseTree.Perm.node _ a cs ds h => by
    show ((RoseTree.filterMap f (.node a cs)).map Nonplanar.mk) =
         ((RoseTree.filterMap f (.node a ds)).map Nonplanar.mk)
    rw [RoseTree.filterMap_node, RoseTree.filterMap_node]
    cases f a with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      congr 1
      exact Nonplanar.mk_eq_mk_iff.mpr
        (RoseTree.Perm.node (filterMapList_permList f h))
  | _, _, .trans h₁ h₂ =>
    (filterMapQuotient_perm f h₁).trans (filterMapQuotient_perm f h₂)

/-- Companion: `filterMapList` sends `PermList`-related children to
    `PermList`-related partial-map images. -/
private theorem filterMapList_permList (f : α → Option β) :
    ∀ {cs ds : List (RoseTree α)}, RoseTree.PermList cs ds →
      RoseTree.PermList (RoseTree.filterMapList f cs)
        (RoseTree.filterMapList f ds)
  | _, _, .nil => .nil
  | _, _, @RoseTree.PermList.cons _ c d cs' ds' hcd hs => by
    have hq : (RoseTree.filterMap f c).map Nonplanar.mk =
              (RoseTree.filterMap f d).map Nonplanar.mk :=
      filterMapQuotient_perm f hcd
    rw [RoseTree.filterMapList_eq_filterMap, RoseTree.filterMapList_eq_filterMap]
    cases hc : RoseTree.filterMap f c with
    | none =>
      have hd : RoseTree.filterMap f d = none := by
        have h2 := hq.symm; rw [hc] at h2; simpa using h2
      rw [List.filterMap_cons_none hc, List.filterMap_cons_none hd,
          ← RoseTree.filterMapList_eq_filterMap,
          ← RoseTree.filterMapList_eq_filterMap]
      exact filterMapList_permList f hs
    | some t_c =>
      cases hd : RoseTree.filterMap f d with
      | none => rw [hc, hd] at hq; simp at hq
      | some t_d =>
        rw [hc, hd] at hq
        simp only [Option.map_some, Option.some.injEq] at hq
        rw [List.filterMap_cons_some hc, List.filterMap_cons_some hd,
            ← RoseTree.filterMapList_eq_filterMap,
            ← RoseTree.filterMapList_eq_filterMap]
        exact RoseTree.PermList.cons (Nonplanar.mk_eq_mk_iff.mp hq)
          (filterMapList_permList f hs)
  | _, _, .swap c d cs => by
    rw [RoseTree.filterMapList_eq_filterMap, RoseTree.filterMapList_eq_filterMap]
    exact RoseTree.PermList.of_perm
      (List.Perm.filterMap (RoseTree.filterMap f) (List.Perm.swap c d cs))
  | _, _, .trans h₁ h₂ =>
    (filterMapList_permList f h₁).trans (filterMapList_permList f h₂)

end

/-- Partially relabel a `Nonplanar` tree, dropping subtrees whose root
    label maps to `none`. -/
def RoseTree.Nonplanar.filterMap (f : α → Option β) :
    Nonplanar α → Option (Nonplanar β) :=
  Quotient.lift (filterMapQuotient f) (fun _ _ h => filterMapQuotient_perm f h)

@[simp] theorem RoseTree.Nonplanar.filterMap_mk (f : α → Option β)
    (t : RoseTree α) :
    Nonplanar.filterMap f (Nonplanar.mk t) =
      (RoseTree.filterMap f t).map Nonplanar.mk := rfl

/-! ## The `Sum.getLeft?` roundtrip -/

/-- Left injection followed by `Sum.getLeft?`-filtering is the identity. -/
@[simp] theorem RoseTree.filterMap_getLeft?_map_inl (t : RoseTree α) :
    RoseTree.filterMap Sum.getLeft? (RoseTree.map (Sum.inl : α → α ⊕ β) t) =
      some t := by
  rw [RoseTree.filterMap_map,
      show (Sum.getLeft? ∘ (Sum.inl : α → α ⊕ β)) = (fun a => some (id a)) from rfl,
      RoseTree.filterMap_some, RoseTree.id_map]

/-- `Nonplanar` version of `RoseTree.filterMap_getLeft?_map_inl`. -/
@[simp] theorem RoseTree.Nonplanar.filterMap_getLeft?_map_inl (T : Nonplanar α) :
    Nonplanar.filterMap Sum.getLeft?
        (Nonplanar.map (Sum.inl : α → α ⊕ β) T) = some T := by
  refine Quotient.inductionOn T fun t => ?_
  show Nonplanar.filterMap Sum.getLeft?
      (Nonplanar.map Sum.inl (Nonplanar.mk t)) = some (Nonplanar.mk t)
  rw [Nonplanar.map_mk, Nonplanar.filterMap_mk, RoseTree.filterMap_getLeft?_map_inl]
  rfl
