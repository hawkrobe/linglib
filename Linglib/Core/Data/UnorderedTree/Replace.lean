/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.DecEq
public import Linglib.Core.Data.UnorderedTree.Basic

/-!
# Substitution of subtrees

`UnorderedTree.replace target replacement t` rebuilds `t` with every subtree equal to `target`
replaced by `replacement`. It is defined by `UnorderedTree.para`, testing each subtree before
rebuilding it from its substituted children. The planar counterpart
`RoseTree.unorderedReplace` serves proofs that recurse over planar children, and
`UnorderedTree.replace_mk` relates the two.

## Main definitions

* `UnorderedTree.replace`, `RoseTree.unorderedReplace`
-/

@[expose] public section

namespace RoseTree

variable {α : Type*} [DecidableEq α]

mutual
/-- Substitution on a planar tree: replace every subtree equal, in the quotient, to `target` by
    `replacement`. -/
def unorderedReplace (target replacement : UnorderedTree α) :
    RoseTree α → UnorderedTree α
  | .node a cs =>
      if UnorderedTree.mk (RoseTree.node a cs) = target then replacement
      else UnorderedTree.node a (unorderedReplaceList target replacement cs)
/-- Substitution in each child, collected as a multiset. -/
def unorderedReplaceList (target replacement : UnorderedTree α) :
    List (RoseTree α) → Multiset (UnorderedTree α)
  | []      => 0
  | c :: cs => unorderedReplace target replacement c ::ₘ unorderedReplaceList target replacement cs
end

end RoseTree

open RoseTree

namespace UnorderedTree

variable {α : Type*} [DecidableEq α]

/-- Replace every subtree equal to `target` by `replacement`. -/
def replace (target replacement : UnorderedTree α) : UnorderedTree α → UnorderedTree α :=
  para fun a ps ↦
    if node a (ps.map Prod.fst) = target then replacement else node a (ps.map Prod.snd)

theorem replace_node (target replacement : UnorderedTree α) (a : α)
    (F : Multiset (UnorderedTree α)) :
    replace target replacement (node a F) =
      if node a F = target then replacement else node a (F.map (replace target replacement)) := by
  simp [replace]

theorem replace_mk (target replacement : UnorderedTree α) (p : RoseTree α) :
    replace target replacement (mk p) = unorderedReplace target replacement p := by
  induction p with
  | node a cs ih =>
    rw [← node_mk_tree_list, replace_node, node_mk_tree_list, unorderedReplace]
    congr 2
    induction cs with
    | nil => rfl
    | cons c cs ihcs =>
      rw [List.map_cons, ← Multiset.cons_coe, Multiset.map_cons, unorderedReplaceList,
        ih c List.mem_cons_self, ihcs fun c hc ↦ ih c (List.mem_cons_of_mem _ hc)]

theorem replace_leaf (target replacement : UnorderedTree α) (x : α) :
    replace target replacement (leaf x) = if leaf x = target then replacement else leaf x := by
  simpa using replace_node target replacement x 0

theorem replace_node_pair (target replacement : UnorderedTree α) (a : α) (l r : UnorderedTree α) :
    replace target replacement (node a {l, r})
      = if node a {l, r} = target then replacement
        else node a {replace target replacement l, replace target replacement r} := by
  simp [replace_node]

/-- Replacing the whole tree yields the replacement. -/
theorem replace_self (t r : UnorderedTree α) : replace t r t = r := by
  simpa [node_eta] using replace_node t r t.value t.children

end UnorderedTree
