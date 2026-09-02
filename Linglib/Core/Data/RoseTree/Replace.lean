/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.DecEq
import Linglib.Core.Data.RoseTree.Nonplanar

/-!
# Substitution of subtrees

`Nonplanar.replace target replacement t` rebuilds `t` with every subtree equal to `target`
replaced by `replacement`. It is defined on planar representatives, where the equality test is
taken in the quotient, and descends because both the test and the rebuilt children multiset are
invariant under permutation of children. It is noncomputable since it rebuilds through the smart
constructor `Nonplanar.node`; concrete cases reduce by `replace_leaf`, `replace_node_pair`, and
`replace_self`.

## Main definitions

* `RoseTree.Nonplanar.replace`
-/

namespace RoseTree

variable {α : Type*} [DecidableEq α]

mutual
/-- Substitution on a planar tree: replace every subtree equal, in the quotient, to `target` by
    `replacement`. -/
noncomputable def nonplanarReplace (target replacement : Nonplanar α) :
    RoseTree α → Nonplanar α
  | .node a cs =>
      if Nonplanar.mk (RoseTree.node a cs) = target then replacement
      else Nonplanar.node a (nonplanarReplaceList target replacement cs)
/-- Substitution in each child, collected as a multiset. -/
noncomputable def nonplanarReplaceList (target replacement : Nonplanar α) :
    List (RoseTree α) → Multiset (Nonplanar α)
  | []      => 0
  | c :: cs => nonplanarReplace target replacement c ::ₘ nonplanarReplaceList target replacement cs
end

mutual
theorem nonplanarReplace_perm (target replacement : Nonplanar α) :
    ∀ {t s : RoseTree α}, Perm t s →
      nonplanarReplace target replacement t = nonplanarReplace target replacement s
  | _, _, .node h => by
    simp only [nonplanarReplace]
    rw [Nonplanar.mk_eq_mk_iff.mpr (Perm.node h),
        nonplanarReplaceList_permList target replacement h]
  | _, _, .trans h₁ h₂ =>
    (nonplanarReplace_perm target replacement h₁).trans
      (nonplanarReplace_perm target replacement h₂)

theorem nonplanarReplaceList_permList (target replacement : Nonplanar α) :
    ∀ {cs ds : List (RoseTree α)}, PermList cs ds →
      nonplanarReplaceList target replacement cs = nonplanarReplaceList target replacement ds
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [nonplanarReplaceList, nonplanarReplace_perm target replacement h,
      nonplanarReplaceList_permList target replacement hs]
  | _, _, .swap _ _ _ => by simp only [nonplanarReplaceList]; rw [Multiset.cons_swap]
  | _, _, .trans h₁ h₂ =>
    (nonplanarReplaceList_permList target replacement h₁).trans
      (nonplanarReplaceList_permList target replacement h₂)
end

namespace Nonplanar

/-- Replace every subtree equal to `target` by `replacement`. -/
noncomputable def replace (target replacement : Nonplanar α) : Nonplanar α → Nonplanar α :=
  lift (nonplanarReplace target replacement) fun _ _ h => nonplanarReplace_perm target replacement h

@[simp] theorem replace_mk (target replacement : Nonplanar α) (p : RoseTree α) :
    replace target replacement (mk p) = nonplanarReplace target replacement p := rfl

theorem replace_leaf (target replacement : Nonplanar α) (x : α) :
    replace target replacement (leaf x)
      = if leaf x = target then replacement else leaf x := by
  show nonplanarReplace target replacement (RoseTree.leaf x) = _
  have hz : node x (0 : Multiset (Nonplanar α)) = leaf x := by
    rw [show (0 : Multiset (Nonplanar α)) = Multiset.ofList ([].map mk) from rfl,
        node_mk_tree_list]; rfl
  have hcond : mk (RoseTree.node x []) = leaf x := rfl
  simp only [RoseTree.leaf, nonplanarReplace, nonplanarReplaceList, hz, hcond]

theorem replace_node_pair (target replacement : Nonplanar α) (a : α) (l r : Nonplanar α) :
    replace target replacement (node a {l, r})
      = if node a {l, r} = target then replacement
        else node a {replace target replacement l, replace target replacement r} := by
  refine inductionOn₂ l r fun pl pr => ?_
  rw [node_pair_mk]
  simp only [replace_mk, nonplanarReplace, nonplanarReplaceList, Multiset.insert_eq_cons,
    ← Multiset.cons_zero]

/-- Replacing the whole tree yields the replacement. -/
theorem replace_self (t r : Nonplanar α) : replace t r t = r := by
  refine Quotient.inductionOn t fun p => ?_
  obtain ⟨a, cs⟩ := p
  show nonplanarReplace (mk (RoseTree.node a cs)) r (RoseTree.node a cs) = r
  simp only [nonplanarReplace, if_pos]

end Nonplanar

end RoseTree
