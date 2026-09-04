/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.DecEq
import Linglib.Core.Data.UnorderedTree.Basic

/-!
# Substitution of subtrees

`UnorderedTree.replace target replacement t` rebuilds `t` with every subtree equal to `target`
replaced by `replacement`. It is defined on planar representatives, where the equality test is
taken in the quotient, and descends because both the test and the rebuilt children multiset are
invariant under permutation of children. It is noncomputable since it rebuilds through the smart
constructor `UnorderedTree.node`; concrete cases reduce by `replace_leaf`, `replace_node_pair`, and
`replace_self`.

## Main definitions

* `UnorderedTree.replace`
-/

namespace RoseTree

variable {α : Type*} [DecidableEq α]

mutual
/-- Substitution on a planar tree: replace every subtree equal, in the quotient, to `target` by
    `replacement`. -/
noncomputable def unorderedReplace (target replacement : UnorderedTree α) :
    RoseTree α → UnorderedTree α
  | .node a cs =>
      if UnorderedTree.mk (RoseTree.node a cs) = target then replacement
      else UnorderedTree.node a (unorderedReplaceList target replacement cs)
/-- Substitution in each child, collected as a multiset. -/
noncomputable def unorderedReplaceList (target replacement : UnorderedTree α) :
    List (RoseTree α) → Multiset (UnorderedTree α)
  | []      => 0
  | c :: cs => unorderedReplace target replacement c ::ₘ unorderedReplaceList target replacement cs
end

mutual
theorem unorderedReplace_perm (target replacement : UnorderedTree α) :
    ∀ {t s : RoseTree α}, Perm t s →
      unorderedReplace target replacement t = unorderedReplace target replacement s
  | _, _, .node h => by
    simp only [unorderedReplace]
    rw [UnorderedTree.mk_eq_mk_iff.mpr (Perm.node h),
        unorderedReplaceList_permList target replacement h]
  | _, _, .trans h₁ h₂ =>
    (unorderedReplace_perm target replacement h₁).trans
      (unorderedReplace_perm target replacement h₂)

theorem unorderedReplaceList_permList (target replacement : UnorderedTree α) :
    ∀ {cs ds : List (RoseTree α)}, PermList cs ds →
      unorderedReplaceList target replacement cs = unorderedReplaceList target replacement ds
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [unorderedReplaceList, unorderedReplace_perm target replacement h,
      unorderedReplaceList_permList target replacement hs]
  | _, _, .swap _ _ _ => by simp only [unorderedReplaceList]; rw [Multiset.cons_swap]
  | _, _, .trans h₁ h₂ =>
    (unorderedReplaceList_permList target replacement h₁).trans
      (unorderedReplaceList_permList target replacement h₂)
end

end RoseTree

open RoseTree

namespace UnorderedTree

variable {α : Type*} [DecidableEq α]

/-- Replace every subtree equal to `target` by `replacement`. -/
noncomputable def replace (target replacement : UnorderedTree α) : UnorderedTree α
    → UnorderedTree α :=
  lift (unorderedReplace target replacement) fun _ _ h => unorderedReplace_perm target replacement h

@[simp] theorem replace_mk (target replacement : UnorderedTree α) (p : RoseTree α) :
    replace target replacement (mk p) = unorderedReplace target replacement p := rfl

theorem replace_leaf (target replacement : UnorderedTree α) (x : α) :
    replace target replacement (leaf x)
      = if leaf x = target then replacement else leaf x := by
  show unorderedReplace target replacement (RoseTree.leaf x) = _
  have hz : node x (0 : Multiset (UnorderedTree α)) = leaf x := by
    rw [show (0 : Multiset (UnorderedTree α)) = Multiset.ofList ([].map mk) from rfl,
        node_mk_tree_list]; rfl
  have hcond : mk (RoseTree.node x []) = leaf x := rfl
  simp only [RoseTree.leaf, unorderedReplace, unorderedReplaceList, hz, hcond]

theorem replace_node_pair (target replacement : UnorderedTree α) (a : α) (l r : UnorderedTree α) :
    replace target replacement (node a {l, r})
      = if node a {l, r} = target then replacement
        else node a {replace target replacement l, replace target replacement r} := by
  refine inductionOn₂ l r fun pl pr => ?_
  rw [node_pair_mk]
  simp only [replace_mk, unorderedReplace, unorderedReplaceList, Multiset.insert_eq_cons,
    ← Multiset.cons_zero]

/-- Replacing the whole tree yields the replacement. -/
theorem replace_self (t r : UnorderedTree α) : replace t r t = r := by
  refine Quotient.inductionOn t fun p => ?_
  obtain ⟨a, cs⟩ := p
  show unorderedReplace (mk (RoseTree.node a cs)) r (RoseTree.node a cs) = r
  simp only [unorderedReplace, if_pos]

end UnorderedTree
