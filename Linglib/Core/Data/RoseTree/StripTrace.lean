/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.Nonplanar

open RoseTree

/-!
# Trace-stripping and `Sum.inl` embedding on rose trees

Removal of `Sum.inr`-rooted (trace-placeholder) subtrees from
`Sum`-labeled rose trees, and the `Sum.inl` embedding it inverts — the
tree-level substrate of the deletion coproduct Δ^d of
[marcolli-chomsky-berwick-2025], packaged as algebra homs in
`Core/Algebra/RootedTree/Coproduct/Deletion.lean`.

## Main definitions

* `RoseTree.stripTrace` — strip trace-placeholder subtrees from a planar
  tree, `none` iff the root itself is a placeholder.
* `RoseTree.Nonplanar.stripTrace` — the descent through the `Perm` quotient.
* `RoseTree.Nonplanar.embedInl` — the componentwise `Sum.inl` embedding.

## Main results

* `RoseTree.Nonplanar.stripTrace_embedInl` — stripping inverts the embedding.
-/

variable {α β : Type*}

/-! ## Tree-level trace-strip projection

Strip trace-placeholder subtrees (`Sum.inr`-rooted subtrees) from a
`RoseTree (α ⊕ β)` tree, yielding `Option (RoseTree α)` — the result is
`none` only if the root itself is a trace placeholder.

The strip recurses into children via `filterMap`: each child is
stripped, and `none` results are dropped. -/

/-- The children-list functor action `mapList f = List.map (RoseTree.map f)`,
    named so the node-expansion of `RoseTree.map` reads structurally below. -/
def RoseTree.mapList (f : α → β) (cs : List (RoseTree α)) : List (RoseTree β) :=
  cs.map (RoseTree.map f)

/-- `RoseTree.map` on a node, expressed through `RoseTree.mapList`. -/
theorem RoseTree.map_node_mapList (f : α → β) (a : α) (cs : List (RoseTree α)) :
    RoseTree.map f (RoseTree.node a cs) = RoseTree.node (f a) (RoseTree.mapList f cs) :=
  RoseTree.map_node f a cs

mutual

/-- Strip trace-placeholder subtrees from a tree-level tree. Returns `none`
    if the root is a trace placeholder (`Sum.inr`-labeled). -/
def RoseTree.stripTrace : RoseTree (α ⊕ β) → Option (RoseTree α)
  | .node (Sum.inr _) _ => none
  | .node (Sum.inl a) cs => some (.node a (RoseTree.stripTraceList cs))

/-- Auxiliary: strip each tree in a children list, dropping `none`s. -/
def RoseTree.stripTraceList : List (RoseTree (α ⊕ β)) → List (RoseTree α)
  | [] => []
  | c :: cs =>
    match RoseTree.stripTrace c with
    | none => RoseTree.stripTraceList cs
    | some t => t :: RoseTree.stripTraceList cs

end

@[simp] theorem RoseTree.stripTrace_inr (b : β) (cs : List (RoseTree (α ⊕ β))) :
    RoseTree.stripTrace (RoseTree.node (Sum.inr b) cs) = none := rfl

@[simp] theorem RoseTree.stripTrace_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    RoseTree.stripTrace (RoseTree.node (Sum.inl a) cs) =
      some (.node a (RoseTree.stripTraceList cs)) := rfl

@[simp] theorem RoseTree.stripTraceList_nil :
    RoseTree.stripTraceList ([] : List (RoseTree (α ⊕ β))) = [] := rfl

/-! ## Descent to `Nonplanar`

Lift `RoseTree.stripTrace` through the quotient. The lift requires that
`stripTrace ∘ Nonplanar.mk` be well-defined modulo `Perm`, which
holds because:
* `Perm` permutes children; `stripTraceList` commutes with
  permutations up to `List.Perm` on the resulting list.
* At the `Nonplanar.mk` level, child-list order collapses, so
  Perm-related stripped trees become equal.
-/

/-- The Perm-invariant strip-then-mk composition. Used to lift
    `RoseTree.stripTrace` through the Nonplanar quotient. -/
private def stripTraceQuotient (t : RoseTree (α ⊕ β)) : Option (Nonplanar α) :=
  (RoseTree.stripTrace t).map Nonplanar.mk

/-- `RoseTree.stripTraceList` agrees with `List.filterMap RoseTree.stripTrace`
    (by structural induction on the list — both pattern-match the same
    way on the optional strip result). -/
theorem RoseTree.stripTraceList_eq_filterMap (cs : List (RoseTree (α ⊕ β))) :
    RoseTree.stripTraceList cs = cs.filterMap RoseTree.stripTrace := by
  induction cs with
  | nil => rfl
  | cons head tail ih =>
    show (match RoseTree.stripTrace head with
            | none => RoseTree.stripTraceList tail
            | some t => t :: RoseTree.stripTraceList tail) =
         (head :: tail).filterMap RoseTree.stripTrace
    cases h : RoseTree.stripTrace head with
    | none => simp [List.filterMap_cons_none h, ih]
    | some t => simp [List.filterMap_cons_some h, ih]

mutual
/-- **Perm invariance** of the strip-then-mk composition. The `node` case is
    by root-label: an `inr` root strips to `none` on both sides, an `inl` root
    lifts the companion's `PermList` on the stripped children through `mk`. -/
private theorem stripTraceQuotient_perm :
    ∀ {t t' : RoseTree (α ⊕ β)}, RoseTree.Perm t t' →
      stripTraceQuotient t = stripTraceQuotient t'
  | _, _, @RoseTree.Perm.node _ a cs ds h => by
    cases a with
    | inl a' =>
      show ((RoseTree.stripTrace (RoseTree.node (Sum.inl a') cs)).map Nonplanar.mk) =
           ((RoseTree.stripTrace (RoseTree.node (Sum.inl a') ds)).map Nonplanar.mk)
      simp only [RoseTree.stripTrace_inl, Option.map_some]
      congr 1
      exact Nonplanar.mk_eq_mk_iff.mpr (RoseTree.Perm.node (stripTraceList_permList h))
    | inr b =>
      show ((RoseTree.stripTrace (RoseTree.node (Sum.inr b) cs)).map Nonplanar.mk) =
           ((RoseTree.stripTrace (RoseTree.node (Sum.inr b) ds)).map Nonplanar.mk)
      simp only [RoseTree.stripTrace_inr, Option.map_none]
  | _, _, .trans h₁ h₂ => (stripTraceQuotient_perm h₁).trans (stripTraceQuotient_perm h₂)

/-- Companion: `stripTraceList` sends `PermList`-related children to
    `PermList`-related stripped lists. `cons` case-splits on whether the
    `Perm`-related heads survive the strip (both drop, or both survive with
    `Perm`-related results via the sibling); `swap` filters through the plain
    `List.Perm`. -/
private theorem stripTraceList_permList :
    ∀ {cs ds : List (RoseTree (α ⊕ β))}, RoseTree.PermList cs ds →
      RoseTree.PermList (RoseTree.stripTraceList cs) (RoseTree.stripTraceList ds)
  | _, _, .nil => .nil
  | _, _, @RoseTree.PermList.cons _ c d cs' ds' hcd hs => by
    have hq : (RoseTree.stripTrace c).map Nonplanar.mk =
              (RoseTree.stripTrace d).map Nonplanar.mk :=
      stripTraceQuotient_perm hcd
    rw [stripTraceList_eq_filterMap, stripTraceList_eq_filterMap]
    cases hc : RoseTree.stripTrace c with
    | none =>
      have hd : RoseTree.stripTrace d = none := by
        have h2 := hq.symm; rw [hc] at h2; simpa using h2
      rw [List.filterMap_cons_none hc, List.filterMap_cons_none hd,
          ← stripTraceList_eq_filterMap, ← stripTraceList_eq_filterMap]
      exact stripTraceList_permList hs
    | some t_c =>
      cases hd : RoseTree.stripTrace d with
      | none => rw [hc, hd] at hq; simp at hq
      | some t_d =>
        rw [hc, hd] at hq
        simp only [Option.map_some, Option.some.injEq] at hq
        rw [List.filterMap_cons_some hc, List.filterMap_cons_some hd,
            ← stripTraceList_eq_filterMap, ← stripTraceList_eq_filterMap]
        exact RoseTree.PermList.cons (Nonplanar.mk_eq_mk_iff.mp hq)
          (stripTraceList_permList hs)
  | _, _, .swap c d cs => by
    rw [stripTraceList_eq_filterMap, stripTraceList_eq_filterMap]
    exact RoseTree.PermList.of_perm
      (List.Perm.filterMap RoseTree.stripTrace (List.Perm.swap c d cs))
  | _, _, .trans h₁ h₂ =>
    (stripTraceList_permList h₁).trans (stripTraceList_permList h₂)
end

/-- Strip trace-placeholder subtrees from a `Nonplanar` tree. -/
def RoseTree.Nonplanar.stripTrace : Nonplanar (α ⊕ β) → Option (Nonplanar α) :=
  Quotient.lift stripTraceQuotient (fun _ _ h => stripTraceQuotient_perm h)

@[simp] theorem RoseTree.Nonplanar.stripTrace_mk (t : RoseTree (α ⊕ β)) :
    Nonplanar.stripTrace (Nonplanar.mk t) =
      (RoseTree.stripTrace t).map Nonplanar.mk := rfl

/-- `RoseTree.stripTraceList` distributes over list concatenation.
    Follows from `stripTraceList_eq_filterMap` + `List.filterMap_append`. -/
theorem RoseTree.stripTraceList_append
    (l1 l2 : List (RoseTree (α ⊕ β))) :
    RoseTree.stripTraceList (l1 ++ l2) =
      RoseTree.stripTraceList l1 ++ RoseTree.stripTraceList l2 := by
  rw [stripTraceList_eq_filterMap, stripTraceList_eq_filterMap,
      stripTraceList_eq_filterMap, List.filterMap_append]

/-- Embed a `Nonplanar α` tree into `Nonplanar (α ⊕ β)` via `Sum.inl`. -/
def RoseTree.Nonplanar.embedInl : Nonplanar α → Nonplanar (α ⊕ β) :=
  Nonplanar.map (Sum.inl : α → α ⊕ β)

/-! ### Strip inverts embed

`RoseTree.stripTrace (RoseTree.map Sum.inl p) = some p` — embedding via
`Sum.inl` then stripping recovers the original. Proven by mutual
structural induction on the tree-level tree / its child list. Descends to
the Nonplanar level via `Quotient.inductionOn`, and lifts to the
algebra-hom level: `stripTraceAlgHom ∘ embedInlAlgHom = id`. -/

mutual

theorem RoseTree.stripTrace_map_inl :
    ∀ (p : RoseTree α), RoseTree.stripTrace (RoseTree.map (Sum.inl : α → α ⊕ β) p) = some p
  | .node a cs => by
    rw [RoseTree.map_node_mapList]
    show RoseTree.stripTrace (.node (Sum.inl a) (RoseTree.mapList Sum.inl cs)) = _
    rw [RoseTree.stripTrace_inl]
    congr 1
    show RoseTree.node a (RoseTree.stripTraceList (RoseTree.mapList Sum.inl cs)) =
         RoseTree.node a cs
    rw [RoseTree.stripTraceList_mapList_inl]

theorem RoseTree.stripTraceList_mapList_inl :
    ∀ (cs : List (RoseTree α)),
      RoseTree.stripTraceList (RoseTree.mapList (Sum.inl : α → α ⊕ β) cs) = cs
  | [] => rfl
  | c :: cs => by
    show (match RoseTree.stripTrace (RoseTree.map Sum.inl c) with
           | none => RoseTree.stripTraceList (RoseTree.mapList Sum.inl cs)
           | some t => t :: RoseTree.stripTraceList (RoseTree.mapList Sum.inl cs)) =
         c :: cs
    rw [RoseTree.stripTrace_map_inl c, RoseTree.stripTraceList_mapList_inl cs]

end

theorem RoseTree.Nonplanar.stripTrace_embedInl (T : Nonplanar α) :
    Nonplanar.stripTrace (Nonplanar.embedInl (β := β) T) = some T := by
  refine Quotient.inductionOn T ?_
  intro p
  show Nonplanar.stripTrace (Nonplanar.map Sum.inl (Nonplanar.mk p)) = some (Nonplanar.mk p)
  rw [Nonplanar.map_mk]
  show ((RoseTree.stripTrace (RoseTree.map Sum.inl p)).map Nonplanar.mk : Option (Nonplanar α)) =
       some (Nonplanar.mk p)
  rw [RoseTree.stripTrace_map_inl]
  rfl

/-- `stripTrace ∘ embedInl = some` (as forest-level filterMap = identity).
    This is the multiset-level version of `Nonplanar.stripTrace_embedInl`. -/
theorem RoseTree.Nonplanar.stripTrace_embedInl_filterMap (F : Multiset (Nonplanar α)) :
    (F.map (Nonplanar.embedInl (β := β))).filterMap Nonplanar.stripTrace = F := by
  rw [Multiset.filterMap_map]
  have h : (Nonplanar.stripTrace ∘ (Nonplanar.embedInl (α := α) (β := β))) = some := by
    funext T
    exact Nonplanar.stripTrace_embedInl T
  rw [h, Multiset.filterMap_some]
