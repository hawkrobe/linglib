/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Structural substitution on the `SO` carrier

P4-pre-a of the single-carrier program. `SO.replace s target replacement` substitutes
every subterm of `s` equal (in the nonplanar quotient) to `target` by `replacement` —
the structural-substitution primitive on the `SO` carrier, replacing the legacy
`FreeCommMagma.lift`-based `SyntacticObject.replace`.

The intended copy-theory use is `s.replace mover SO.traceLeaf` (leave an index-free
trace where a mover was). **Framing:** this is a *structural* operation; the
**canonical** MCB Internal Merge is the workspace coproduct composition (Prop 1.4.2,
`SO.intMerge`/`Workspace`, #795), with traces as coproduct remainders and chains held
at the workspace level (Def 1.2.1). `replace` supports the derived, transformational
view that the paper-anchored study files are written in; it is not a claim that
movement *is* substitution.

Built the established way (`subtreesN`): a planar recursion with quotient-level `target`
matching, proved `Perm`-invariant and lifted, then closed under `IsSO` via
`SO.ind`. It is **noncomputable** (it rebuilds via `Nonplanar.node`); concrete results
are related by the reduction lemmas (`replace_lexLeaf`/`_traceLeaf`/`_node`), not by
`decide`.
-/

namespace Minimalist

open RootedTree

/-! ### Substitution on the planar carrier -/

mutual
/-- Structural substitution on a planar `SO`-tree: replace every subtree equal (in the
    nonplanar quotient) to `target` by `replacement`, rebuilding the surrounding tree. -/
noncomputable def replacePlanar (target replacement : Nonplanar SOLabel) :
    RoseTree SOLabel → Nonplanar SOLabel
  | .node a cs =>
      if Nonplanar.mk (RoseTree.node a cs) = target then replacement
      else Nonplanar.node a (replacePlanarList target replacement cs)
/-- Auxiliary: substitute in each child, collecting the results as a multiset. -/
noncomputable def replacePlanarList (target replacement : Nonplanar SOLabel) :
    List (RoseTree SOLabel) → Multiset (Nonplanar SOLabel)
  | []      => 0
  | c :: cs => replacePlanar target replacement c ::ₘ replacePlanarList target replacement cs
end

mutual
/-- `replacePlanar` is `Perm`-invariant, so it descends to the quotient. At a node the
    `if mk _ = target` guard is fixed because `mk` is `Perm`-invariant (`mk_eq_mk_iff`),
    and the rebuilt child multiset by the `PermList` companion. -/
theorem replacePlanar_perm (target replacement : Nonplanar SOLabel) :
    ∀ {t s : RoseTree SOLabel}, RoseTree.Perm t s →
      replacePlanar target replacement t = replacePlanar target replacement s
  | _, _, .node h => by
    simp only [replacePlanar]
    rw [Nonplanar.mk_eq_mk_iff.mpr (RoseTree.Perm.node h),
        replacePlanarList_permList target replacement h]
  | _, _, .trans h₁ h₂ =>
    (replacePlanar_perm target replacement h₁).trans (replacePlanar_perm target replacement h₂)

/-- The rebuilt child multiset is `PermList`-invariant: it is built child-by-child, the
    `List.Perm`-style case split matching heads by the mutual `replacePlanar_perm` and
    reordering by `Multiset.cons_swap`. -/
theorem replacePlanarList_permList (target replacement : Nonplanar SOLabel) :
    ∀ {cs ds : List (RoseTree SOLabel)}, RoseTree.PermList cs ds →
      replacePlanarList target replacement cs = replacePlanarList target replacement ds
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [replacePlanarList, replacePlanar_perm target replacement h,
      replacePlanarList_permList target replacement hs]
  | _, _, .swap _ _ _ => by simp only [replacePlanarList]; rw [Multiset.cons_swap]
  | _, _, .trans h₁ h₂ =>
    (replacePlanarList_permList target replacement h₁).trans
      (replacePlanarList_permList target replacement h₂)
end

/-- Substitution lifted to the nonplanar carrier. -/
noncomputable def replaceN (target replacement : Nonplanar SOLabel) :
    Nonplanar SOLabel → Nonplanar SOLabel :=
  Nonplanar.lift (replacePlanar target replacement)
    (fun _ _ h => replacePlanar_perm target replacement h)

@[simp] theorem replaceN_mk (target replacement : Nonplanar SOLabel) (p : RoseTree SOLabel) :
    replaceN target replacement (Nonplanar.mk p) = replacePlanar target replacement p := rfl

/-! ### Reduction lemmas on leaves and bare binary nodes -/

theorem replaceN_leaf (target replacement : Nonplanar SOLabel) (x : SOLabel) :
    replaceN target replacement (Nonplanar.leaf x)
      = if Nonplanar.leaf x = target then replacement else Nonplanar.leaf x := by
  show replacePlanar target replacement (RoseTree.leaf x) = _
  have hz : Nonplanar.node x (0 : Multiset (Nonplanar SOLabel)) = Nonplanar.leaf x := by
    rw [show (0 : Multiset (Nonplanar SOLabel)) = Multiset.ofList ([].map Nonplanar.mk) from rfl,
        Nonplanar.node_mk_tree_list]; rfl
  have hcond : Nonplanar.mk (RoseTree.node x []) = Nonplanar.leaf x := rfl
  simp only [RoseTree.leaf, replacePlanar, replacePlanarList, hz, hcond]

theorem replaceN_node (target replacement : Nonplanar SOLabel) (a b : Nonplanar SOLabel) :
    replaceN target replacement (Nonplanar.node (Sum.inr ()) {a, b})
      = if Nonplanar.node (Sum.inr ()) {a, b} = target then replacement
        else Nonplanar.node (Sum.inr ()) {replaceN target replacement a, replaceN target replacement b} := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  have key : Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
           = Nonplanar.mk (RoseTree.node (Sum.inr ()) [pa, pb]) := by
    rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
          = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl, Nonplanar.node_mk_tree_list]
  show replaceN target replacement (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = if Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb} = target then replacement
        else Nonplanar.node (Sum.inr ())
          {replaceN target replacement (Nonplanar.mk pa), replaceN target replacement (Nonplanar.mk pb)}
  rw [key]
  simp only [replaceN_mk, replacePlanar, replacePlanarList, Multiset.insert_eq_cons,
    ← Multiset.cons_zero]

/-- Replacing the whole tree (`t` itself) yields the replacement. -/
theorem replaceN_self (t r : Nonplanar SOLabel) : replaceN t r t = r := by
  refine Quotient.inductionOn t fun p => ?_
  obtain ⟨a, cs⟩ := p
  show replacePlanar (Nonplanar.mk (RoseTree.node a cs)) r (RoseTree.node a cs) = r
  simp only [replacePlanar, if_pos]

/-! ### `IsSO` closure and `SO.replace` -/

/-- Substitution preserves well-formedness: replacing subterms of an `SO` by another
    `SO` yields an `SO` (the arity of every node is preserved). -/
theorem replaceN_isSO (target replacement s : SO) :
    IsSO (replaceN target.val replacement.val s.val) := by
  induction s using SO.ind with
  | lex tok =>
    rw [show (SO.lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl, replaceN_leaf]
    split
    · exact replacement.2
    · exact (SO.lexLeaf tok).2
  | trace =>
    rw [show SO.traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl, replaceN_leaf]
    split
    · exact replacement.2
    · exact SO.traceLeaf.2
  | node l r ihl ihr =>
    rw [SO.node_val, replaceN_node]
    split
    · exact replacement.2
    · show isSO (Nonplanar.node (Sum.inr ())
        {replaceN target.val replacement.val l.val, replaceN target.val replacement.val r.val}) = true
      rw [isSO_node_pair, ihl, ihr]; rfl

/-- **Structural substitution** on the `SO` carrier ([marcolli-chomsky-berwick-2025]
    §1.2): replace every subterm of `s` equal to `target` by `replacement`. The
    copy-theory use is `s.replace mover SO.traceLeaf`. Noncomputable (rebuilds via
    `SO.node`); reduce concrete cases via `replace_self`/`replace_node_of_ne`/
    `replace_lexLeaf_of_ne`. -/
noncomputable def SO.replace (s target replacement : SO) : SO :=
  ⟨replaceN target.val replacement.val s.val, replaceN_isSO target replacement s⟩

@[simp] theorem SO.replace_val (s target replacement : SO) :
    (SO.replace s target replacement).val = replaceN target.val replacement.val s.val := rfl

/-- Replacing the whole object by `replacement`. -/
@[simp] theorem SO.replace_self (target replacement : SO) :
    SO.replace target target replacement = replacement :=
  Subtype.ext (by rw [SO.replace_val, replaceN_self])

/-- At a node that is not itself the `target`, substitution recurses into both
    daughters (the Head Feature Principle of substitution: structure is preserved). -/
theorem SO.replace_node_of_ne {l r target replacement : SO} (h : SO.node l r ≠ target) :
    SO.replace (SO.node l r) target replacement
      = SO.node (SO.replace l target replacement) (SO.replace r target replacement) := by
  apply Subtype.ext
  rw [SO.replace_val, SO.node_val, replaceN_node, if_neg, SO.node_val, SO.replace_val,
      SO.replace_val]
  rw [← SO.node_val]
  exact fun heq => h (Subtype.ext heq)

/-- A lexical leaf that is not the `target` is left unchanged. -/
theorem SO.replace_lexLeaf_of_ne {tok : LIToken} {target replacement : SO}
    (h : SO.lexLeaf tok ≠ target) :
    SO.replace (SO.lexLeaf tok) target replacement = SO.lexLeaf tok := by
  apply Subtype.ext
  rw [SO.replace_val, show (SO.lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl,
      replaceN_leaf, if_neg]
  exact fun heq => h (Subtype.ext heq)

/-- The bare trace leaf, not being the `target`, is left unchanged. -/
theorem SO.replace_traceLeaf_of_ne {target replacement : SO} (h : SO.traceLeaf ≠ target) :
    SO.replace SO.traceLeaf target replacement = SO.traceLeaf := by
  apply Subtype.ext
  rw [SO.replace_val, show SO.traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl,
      replaceN_leaf, if_neg]
  exact fun heq => h (Subtype.ext heq)

/-! ### Worked example

The copy-theory case: moving a daughter `r` out of `[l r]` and leaving a trace in its
place yields `[l′ t]` (with `l′` the recursively-substituted left daughter). The
side-condition `[l r] ≠ r` always holds (a tree is never its own daughter; provable
from weight via `Subterm`'s `immediatelyContains_lt_weight`), taken as a hypothesis
here to keep this module's dependencies minimal. Substitution is noncomputable, so this
is a structural proof, not a `decide`. -/

example (l r : SO) (h : SO.node l r ≠ r) :
    SO.replace (SO.node l r) r SO.traceLeaf
      = SO.node (SO.replace l r SO.traceLeaf) SO.traceLeaf := by
  rw [SO.replace_node_of_ne h, SO.replace_self]

end Minimalist
