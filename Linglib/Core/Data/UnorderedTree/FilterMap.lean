/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.FilterMap
public import Linglib.Core.Data.UnorderedTree.Basic

/-!
# Partial label maps on unordered trees

`RoseTree.filterMap f ∘ UnorderedTree.mk` is well defined modulo `Perm`: `Perm` permutes
children, `filterMapList` commutes with permutations up to `List.Perm`, and child-list order
collapses under `UnorderedTree.mk`. So `RoseTree.filterMap` descends to the quotient.

## Main definitions

* `UnorderedTree.filterMap`: the descent through the `Perm` quotient.
-/

@[expose] public section

variable {α β : Type*}

/-- The Perm-invariant filterMap-then-mk composition, lifted through the
    quotient by `UnorderedTree.filterMap`. -/
def filterMapQuotient (f : α → Option β) (t : RoseTree α) :
    Option (UnorderedTree β) :=
  (RoseTree.filterMap f t).map UnorderedTree.mk

mutual

/-- **Perm invariance** of the filterMap-then-mk composition. -/
theorem filterMapQuotient_perm (f : α → Option β) :
    ∀ {t t' : RoseTree α}, RoseTree.Perm t t' →
      filterMapQuotient f t = filterMapQuotient f t'
  | _, _, @RoseTree.Perm.node _ a cs ds h => by
    show ((RoseTree.filterMap f (.node a cs)).map UnorderedTree.mk) =
         ((RoseTree.filterMap f (.node a ds)).map UnorderedTree.mk)
    rw [RoseTree.filterMap_node, RoseTree.filterMap_node]
    cases f a with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      congr 1
      exact UnorderedTree.mk_eq_mk_iff.mpr
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
    have hq : (RoseTree.filterMap f c).map UnorderedTree.mk =
              (RoseTree.filterMap f d).map UnorderedTree.mk :=
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
        exact RoseTree.PermList.cons (UnorderedTree.mk_eq_mk_iff.mp hq)
          (filterMapList_permList f hs)
  | _, _, .swap c d cs => by
    rw [RoseTree.filterMapList_eq_filterMap, RoseTree.filterMapList_eq_filterMap]
    exact RoseTree.PermList.of_perm
      (List.Perm.filterMap (RoseTree.filterMap f) (List.Perm.swap c d cs))
  | _, _, .trans h₁ h₂ =>
    (filterMapList_permList f h₁).trans (filterMapList_permList f h₂)

end

/-- Partially relabel a `UnorderedTree` tree, dropping subtrees whose root
    label maps to `none`. -/
def UnorderedTree.filterMap (f : α → Option β) :
    UnorderedTree α → Option (UnorderedTree β) :=
  Quotient.lift (filterMapQuotient f) (fun _ _ h => filterMapQuotient_perm f h)

@[simp] theorem UnorderedTree.filterMap_mk (f : α → Option β)
    (t : RoseTree α) :
    UnorderedTree.filterMap f (UnorderedTree.mk t) =
      (RoseTree.filterMap f t).map UnorderedTree.mk := rfl

/-- `UnorderedTree` version of `RoseTree.filterMap_getLeft?_map_inl`. -/
@[simp] theorem UnorderedTree.filterMap_getLeft?_map_inl (T : UnorderedTree α) :
    UnorderedTree.filterMap Sum.getLeft?
        (UnorderedTree.map (Sum.inl : α → α ⊕ β) T) = some T := by
  refine Quotient.inductionOn T fun t => ?_
  show UnorderedTree.filterMap Sum.getLeft?
      (UnorderedTree.map Sum.inl (UnorderedTree.mk t)) = some (UnorderedTree.mk t)
  rw [UnorderedTree.map_mk, UnorderedTree.filterMap_mk, RoseTree.filterMap_getLeft?_map_inl]
  rfl
