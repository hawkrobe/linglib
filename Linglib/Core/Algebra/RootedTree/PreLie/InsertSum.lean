/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insert
import Linglib.Core.Combinatorics.RootedTree.Nonplanar
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# Single-tree pre-Lie product `insertSum` on `Tree α` and `Nonplanar α`
[foissy-typed-decorated-rooted-trees-2018]
[chapoton-livernet-2001]
[marcolli-chomsky-berwick-2025]

The **vertex-grafting pre-Lie product** on n-ary rooted trees: for
trees `T₁, T₂`, `T₁ ◁ T₂` is the multiset of all trees obtained by
grafting `T₂` as a new child of some vertex of `T₁`:

  T₁ ◁ T₂ = Σ_{v ∈ V(T₁)} graft(v, T₁, T₂)

This file contains both the ordered definition (Foissy 2018 Prop 2.2,
Chapoton-Livernet) on `Tree α` and its descent through `Nonplanar.mk`
to the nonplanar carrier.

## Reference

[foissy-typed-decorated-rooted-trees-2018] Proposition 2.2 defines
the multiple pre-Lie product on D-decorated T-typed rooted trees (D =
decoration set, T = edge type set). Specialized to T = {*} (single
edge type) and decoration set α, this is exactly `insertSum`.

[chapoton-livernet-2001] introduced the original CL pre-Lie
product on undecorated rooted trees, of which the present construction
is the decorated extension.

## Relation to MCB §1.7

[marcolli-chomsky-berwick-2025] Definition 1.7.1 (book p. 77)
defines a DIFFERENT pre-Lie product on **nonplanar BINARY** rooted
trees with leaf labels in `SO_0` (internal vertices unlabeled), via
**edge subdivision**. The two are distinct algebras on distinct
carriers — neither is a specialization of the other. Both satisfy the
abstract pre-Lie identity (mathlib's `RightPreLieAlgebra`); a future
binary substrate file would add a separate `RightPreLieAlgebra`
instance for MCB §1.7.

## File scope

- §1: `insertSum` definition + simp lemmas + leaf case.
- §2: Decomposition (`insertSum_eq_coe_map_insertAt`).
- §3: Cardinality (`card_insertSum_eq_numNodes`), derived from §2.
- §4: Cons-decomposition projection helpers (descent).
- §5: Right invariance (`PermEquiv` on T₂).
- §6: List-side perm + componentwise `PermEquiv` invariance.
- §7: Left invariance (`PermStep` / `PermEquiv` on T₁).
- §8: Native `Nonplanar.insertSum` via `Quotient.lift₂`.
- §9: Quotient-unfolding lemma + Nonplanar cardinality.
- §10: Sanity tests.

Sibling files:
- `Path.lean` / `Insert.lean` — path-based vertex enumeration + grafting
  (`Pathed.vertices`, `Pathed.insertAt`).
- `Insertion.lean` — multi-tree multi-vertex grafting (Foissy 2021).
- `Algebra.lean` — `RightPreLieAlgebra ℤ` instance.

-/

namespace RootedTree.Tree

variable {α : Type*}

/-! ### `insertSum` — the vertex-grafting product

Mutually recursive on `(Tree, List Tree)`. Each summand of
`insertSum T₁ T₂` corresponds to a choice of vertex `v` in `T₁`; the
corresponding tree replaces `v`'s children list `cs` with `T₂ :: cs`.
This is a paramorphic recursion — the original children list is reused
to rebuild the grafted node — so it is written by hand rather than as a
`fold`. -/

mutual
/-- The pre-Lie product `T₁ ◁ T₂` on `Tree α` (vertex grafting): the
    multiset of all trees obtained by grafting `T₂` as a new child of
    some vertex of `T₁`. -/
def insertSum : Tree α → Tree α → Multiset (Tree α)
  | .node a cs, T₂ =>
      ((Tree.node a (T₂ :: cs)) : Tree α) ::ₘ
        (insertSumList cs T₂).map (fun cs' => .node a cs')
/-- Auxiliary: graft `T₂` inside one of the entries of a children list,
    returning the multiset of resulting children-lists (one per vertex
    inside the list). -/
def insertSumList : List (Tree α) → Tree α →
    Multiset (List (Tree α))
  | [], _ => 0
  | c :: cs, T₂ =>
      (insertSum c T₂).map (fun c' => c' :: cs)
        + (insertSumList cs T₂).map (fun cs' => c :: cs')
end

/-- Notation `T₁ ◁ T₂` for `insertSum T₁ T₂`. The right-triangular
    Unicode glyph matches Foissy's typesetting. Scoped to avoid
    clashing with mathlib's `LeftPreLieRing` notation. -/
scoped infixl:65 " ◁ " => insertSum

@[simp] theorem insertSum_node (a : α) (cs : List (Tree α))
    (T₂ : Tree α) :
    (Tree.node a cs) ◁ T₂ =
      ((Tree.node a (T₂ :: cs)) : Tree α) ::ₘ
        (insertSumList cs T₂).map (fun cs' => .node a cs') := by
  unfold insertSum; rfl

@[simp] theorem insertSumList_nil (T₂ : Tree α) :
    insertSumList ([] : List (Tree α)) T₂ = 0 := by
  conv_lhs => unfold insertSumList

@[simp] theorem insertSumList_cons (c : Tree α) (cs : List (Tree α))
    (T₂ : Tree α) :
    insertSumList (c :: cs) T₂ =
      (insertSum c T₂).map (fun c' => c' :: cs)
        + (insertSumList cs T₂).map (fun cs' => c :: cs') := by
  conv_lhs => unfold insertSumList

/-- A leaf has exactly one summand: graft `T₂` at the root. -/
@[simp] theorem insertSum_leaf (a : α) (T₂ : Tree α) :
    Tree.leaf a ◁ T₂ =
      ({Tree.node a [T₂]} : Multiset (Tree α)) := by
  show insertSum (Tree.node a []) T₂ =
       ({Tree.node a [T₂]} : Multiset (Tree α))
  rw [insertSum_node, insertSumList_nil, Multiset.map_zero]
  rfl

/-! ### Decomposition — `insertSum` via `Pathed.vertices` + `Pathed.insertAt`

Bridge lemma between the recursive (Multiset) formulation of `insertSum`
in §1 and the per-path (List) formulation in `Path.lean` / `Insert.lean`.
The lemma is the basis for the pre-Lie identity proof in `Algebra.lean`:
each summand of `insertSum T₁ T₂` is uniquely identified by a path
into `T₁`. -/

/-- Path-offset helper: at offset `pre.length`, the path-based
    insertion descends into the head of `c :: cs'` (sitting after the
    `pre` prefix). Witnesses the decisive identification of "the path
    `pre.length :: q` in `pre ++ (c :: cs')`" with "the path `q` in
    `c`, lifted through the `pre`-prefixed children-list set". -/
private theorem pathInsertAt_at_pre_length (a : α)
    (pre cs' : List (Tree α)) (c : Tree α) (q : Pathed.Path)
    (T₂ : Tree α) :
    Pathed.insertAt (pre.length :: q) T₂ (Tree.node a (pre ++ (c :: cs')))
      = Tree.node a (pre ++ (Pathed.insertAt q T₂ c :: cs')) := by
  have hpre_lt : pre.length < (pre ++ (c :: cs')).length := by
    rw [List.length_append, List.length_cons]; omega
  rw [Pathed.insertAt_cons_of_lt _ _ _ _ _ hpre_lt]
  congr 1
  rw [List.getElem_append_right (le_refl _),
      List.set_append_right _ _ (le_refl _)]
  simp only [Nat.sub_self, List.getElem_cons_zero, List.set_cons_zero]

mutual
/-- **Decomposition lemma**: `T₁ ◁ T₂` equals the multiset of
    `Pathed.insertAt p T₂ T₁` for `p` ranging over `Pathed.vertices T₁`. -/
theorem insertSum_eq_coe_map_insertAt : ∀ (T₁ T₂ : Tree α),
    T₁ ◁ T₂ =
      ((Pathed.vertices T₁).map (fun p => Pathed.insertAt p T₂ T₁)
        : Multiset (Tree α))
  | .node a cs, T₂ => by
    rw [insertSum_node, Pathed.vertices_node]
    have aux := insertSumList_eq_coe_map_pathInsertAt_aux a [] cs T₂
    simp only [List.nil_append, List.length_nil] at aux
    rw [aux, List.map_cons, ← Multiset.cons_coe, Pathed.insertAt_nil]
/-- Auxiliary: with `pre` siblings before the cs-tail being grafted in,
    children-list grafting through `pre`-prefixed `Tree.node a`
    equals the path-based insertions at offset `pre.length` into the
    original host `Tree.node a (pre ++ cs)`. -/
theorem insertSumList_eq_coe_map_pathInsertAt_aux :
    ∀ (a : α) (pre cs : List (Tree α)) (T₂ : Tree α),
    (insertSumList cs T₂).map (fun cs' => Tree.node a (pre ++ cs'))
      = ((Pathed.verticesAux pre.length cs).map
          (fun p => Pathed.insertAt p T₂ (Tree.node a (pre ++ cs)))
          : Multiset _)
  | _, _, [], _ => by
    rw [insertSumList_nil, Pathed.verticesAux_nil]
    rfl
  | a, pre, c :: cs', T₂ => by
    rw [insertSumList_cons, Pathed.verticesAux_cons,
        Multiset.map_add, Multiset.map_map, Multiset.map_map,
        List.map_append, ← Multiset.coe_add]
    simp only [Function.comp_def]
    congr 1
    · rw [insertSum_eq_coe_map_insertAt c T₂, Multiset.map_coe,
          List.map_map, List.map_map]
      simp only [Function.comp_def]
      apply congrArg Multiset.ofList
      apply List.map_congr_left
      intro q _
      exact (pathInsertAt_at_pre_length a pre cs' c q T₂).symm
    · have ih_aux :=
        insertSumList_eq_coe_map_pathInsertAt_aux a (pre ++ [c]) cs' T₂
      simp only [List.length_append, List.length_singleton,
                 List.append_assoc, List.singleton_append] at ih_aux
      exact ih_aux
end

/-! ### Cardinality — `card (T₁ ◁ T₂) = T₁.numNodes`

Each vertex of `T₁` contributes one summand. Both counts fall out of the
§2 decomposition: `card (T₁ ◁ T₂) = (vertices T₁).length = T₁.numNodes`,
so no `numNodes`-mirroring induction is needed. -/

/-- The number of summands in `T₁ ◁ T₂` equals `(vertices T₁).length`. -/
theorem card_insertSum_eq_length_vertices (T₁ T₂ : Tree α) :
    Multiset.card (T₁ ◁ T₂) = (Pathed.vertices T₁).length := by
  rw [insertSum_eq_coe_map_insertAt, Multiset.coe_card, List.length_map]

/-- The number of summands in `T₁ ◁ T₂` equals `T₁.numNodes`
    (total vertex count). -/
theorem card_insertSum_eq_numNodes (T₁ T₂ : Tree α) :
    Multiset.card (T₁ ◁ T₂) = T₁.numNodes := by
  rw [card_insertSum_eq_length_vertices, Pathed.length_vertices_eq_numNodes]

/-! ### Sanity tests at compile time -/

section Tests

example : (Tree.leaf 1 : Tree Nat) ◁ Tree.leaf 2
    = ({Tree.node 1 [Tree.leaf 2]} : Multiset (Tree Nat)) := by
  rw [insertSum_leaf]

/-- A binary tree has 3 vertices, hence 3 grafting summands. -/
example : Multiset.card
    ((Tree.binary 1 (Tree.leaf 2) (Tree.leaf 3) : Tree Nat) ◁
      Tree.leaf 4) = 3 := by
  rw [card_insertSum_eq_numNodes]
  decide

/-- The grafting decomposition: each summand corresponds to a path. -/
example (T₁ T₂ : Tree Nat) :
    Multiset.card (T₁ ◁ T₂) = (Pathed.vertices T₁).length :=
  card_insertSum_eq_length_vertices T₁ T₂

end Tests

end RootedTree.Tree

/-! # Descent of `insertSum` through `Nonplanar.mk`

The descent layer: lift `Tree.insertSum` to `Nonplanar α` via
`Quotient.lift₂`, requiring invariance under `PermEquiv` on both
arguments. -/

namespace RootedTree

namespace Nonplanar

variable {α : Type*}

/-! ### Cons-decomposition of `insertSumList`-projection

Helper lemma used by both §5 right-invariance and §6 list permutation
proofs. The cons case of `insertSumList cs T₂` splits into a per-head
grafting (in `insertSum c T₂`) plus a per-tail grafting (in
`insertSumList tail T₂`); after projection through `mk ∘ node a`, the
two halves are clean two-summand decompositions with simpler wrappers
than the raw `Multiset.map_map` form. -/

private theorem insertSumList_cons_proj (a : α) (c : Tree α)
    (cs : List (Tree α)) (T₂ : Tree α) :
    (Tree.insertSumList (c :: cs) T₂).map
        (fun cs' => (Nonplanar.mk (Tree.node a cs') : Nonplanar α)) =
      (Tree.insertSum c T₂).map
          (fun c' => Nonplanar.mk (Tree.node a (c' :: cs))) +
        (Tree.insertSumList cs T₂).map
          (fun cs' => Nonplanar.mk (Tree.node a (c :: cs'))) := by
  rw [Tree.insertSumList_cons, Multiset.map_add, Multiset.map_map,
      Multiset.map_map]
  rfl

/-- Companion: `(insertSum (node a cs) T₂).map mk` decomposes as the head
    `mk (node a (T₂ :: cs))` plus the projected tail
    `(insertSumList cs T₂).map (fun cs' => mk (node a cs'))`. -/
private theorem insertSum_node_proj (a : α) (cs : List (Tree α)) (T₂ : Tree α) :
    (Tree.insertSum (Tree.node a cs) T₂).map Nonplanar.mk =
      Nonplanar.mk (Tree.node a (T₂ :: cs)) ::ₘ
        (Tree.insertSumList cs T₂).map
          (fun cs' => Nonplanar.mk (Tree.node a cs')) := by
  rw [Tree.insertSum_node, Multiset.map_cons, Multiset.map_map]
  rfl

/-- Wrapper-shift helper: `(M.map (fun c' => mk (node a (c' :: cs)))) =
    ((M.map mk).map (fun n => mk (node a (n.out :: cs))))`. Used when we
    want to factor the `c' :: cs` wrapper through `mk` so that the inner
    multiset becomes `M.map mk` (a form we can substitute via the IH). -/
private theorem map_node_cons_via_mk (a : α) (cs : List (Tree α))
    {M : Multiset (Tree α)} :
    M.map (fun c' => Nonplanar.mk (Tree.node a (c' :: cs))) =
      (M.map Nonplanar.mk).map
        (fun n : Nonplanar α =>
          Nonplanar.mk (Tree.node a (n.out :: cs))) := by
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro c' _
  apply Nonplanar.mk_eq_mk_iff.mpr
  apply Tree.permEquiv_recurse_lift [] cs
  exact (Quotient.exact (Quotient.out_eq (Nonplanar.mk c'))).symm

/-- Wrapper-shift helper for sibling-cons: factor a sibling-cons wrapper
    through `mk ∘ node a` so the IH on `(M.map (mk ∘ node a))`
    substitutes cleanly. -/
private theorem map_node_sibling_cons_via_mk (a : α) (p : Tree α)
    {M : Multiset (List (Tree α))} :
    M.map (fun cs' => Nonplanar.mk (Tree.node a (p :: cs'))) =
      (M.map (fun cs' => Nonplanar.mk (Tree.node a cs'))).map
        (fun n : Nonplanar α =>
          Nonplanar.mk (Tree.node a (p :: n.out.children))) := by
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro cs' _
  apply Nonplanar.mk_eq_mk_iff.mpr
  have hbase : Tree.PermEquiv (Tree.node a cs')
               (Nonplanar.mk (Tree.node a cs')).out :=
    (Quotient.exact (Quotient.out_eq (Nonplanar.mk (Tree.node a cs')))).symm
  have hvalue : (Nonplanar.mk (Tree.node a cs')).out.value = a := by
    have := Tree.value_permEquiv hbase
    simp only [Tree.value_node] at this
    exact this.symm
  have hform : (Nonplanar.mk (Tree.node a cs')).out =
      Tree.node a (Nonplanar.mk (Tree.node a cs')).out.children := by
    generalize (Nonplanar.mk (Tree.node a cs')).out = q at hvalue
    cases q with
    | node b qs =>
      simp only [Tree.value_node] at hvalue
      rw [hvalue]
      rfl
  have hbase' : Tree.PermEquiv (Tree.node a cs')
      (Tree.node a (Nonplanar.mk (Tree.node a cs')).out.children) := by
    rw [← hform]; exact hbase
  exact Tree.permEquiv_cons_lift p hbase'

/-! ### Right invariance — `T₂ → T₂'`

If `T₂ ≡ T₂'` (`PermEquiv`), then `(T₁ ◁ T₂).map mk = (T₁ ◁ T₂').map mk`
for any T₁. Mutually inducted with the children-list version
`insertSumList`. -/

mutual
private theorem insertSum_permEquiv_right_aux : ∀ (T₁ T₂ T₂' : Tree α)
    (_ : Tree.PermEquiv T₂ T₂'),
    (Tree.insertSum T₁ T₂).map Nonplanar.mk =
      (Tree.insertSum T₁ T₂').map Nonplanar.mk
  | .node a cs, T₂, T₂', h => by
    rw [insertSum_node_proj, insertSum_node_proj]
    congr 1
    · apply Nonplanar.mk_eq_mk_iff.mpr
      exact Tree.permEquiv_recurse_lift [] cs h
    · exact insertSumList_permEquiv_right_aux a cs T₂ T₂' h
private theorem insertSumList_permEquiv_right_aux : ∀ (a : α) (cs : List (Tree α))
    (T₂ T₂' : Tree α) (_ : Tree.PermEquiv T₂ T₂'),
    (Tree.insertSumList cs T₂).map
        (fun cs' => (Nonplanar.mk (Tree.node a cs') : Nonplanar α)) =
    (Tree.insertSumList cs T₂').map
        (fun cs' => Nonplanar.mk (Tree.node a cs'))
  | _, [], _, _, _ => by
    rw [Tree.insertSumList_nil, Tree.insertSumList_nil]
  | a, c :: cs, T₂, T₂', h => by
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · have ih := insertSum_permEquiv_right_aux c T₂ T₂' h
      rw [map_node_cons_via_mk a cs (M := Tree.insertSum c T₂),
          map_node_cons_via_mk a cs (M := Tree.insertSum c T₂'),
          ih]
    · have ih_list := insertSumList_permEquiv_right_aux a cs T₂ T₂' h
      rw [map_node_sibling_cons_via_mk a c (M := Tree.insertSumList cs T₂),
          map_node_sibling_cons_via_mk a c (M := Tree.insertSumList cs T₂'),
          ih_list]
end

/-- Right invariance for `insertSum`. -/
theorem insertSum_permEquiv_right (T₁ : Tree α) {T₂ T₂' : Tree α}
    (h : Tree.PermEquiv T₂ T₂') :
    (Tree.insertSum T₁ T₂).map Nonplanar.mk =
      (Tree.insertSum T₁ T₂').map Nonplanar.mk :=
  insertSum_permEquiv_right_aux T₁ T₂ T₂' h

/-! ### List-side `mk`-projection of `insertSumList`

Two key properties of `(insertSumList cs T₂).map (mk ∘ .node a)`:
Perm-invariance in `cs` and componentwise `PermEquiv`-invariance. -/

private theorem insertSumList_proj_perm_aux (a : α) (T₂ : Tree α) :
    ∀ {cs cs' : List (Tree α)},
      cs.Perm cs' →
      (Tree.insertSumList cs T₂).map
          (fun cs' => (Nonplanar.mk (Tree.node a cs') : Nonplanar α)) =
      (Tree.insertSumList cs' T₂).map
          (fun cs' => Nonplanar.mk (Tree.node a cs')) := by
  intro cs cs' h
  induction h with
  | nil => rfl
  | @cons x cs cs' hperm ih =>
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    have head_eq :
        (Tree.insertSum x T₂).map
          (fun c' => Nonplanar.mk (Tree.node a (c' :: cs))) =
        (Tree.insertSum x T₂).map
          (fun c' => Nonplanar.mk (Tree.node a (c' :: cs'))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Tree.permEquiv_root_perm
      exact List.Perm.cons c' hperm
    rw [head_eq,
        map_node_sibling_cons_via_mk a x (M := Tree.insertSumList cs T₂),
        map_node_sibling_cons_via_mk a x (M := Tree.insertSumList cs' T₂),
        ih]
  | @swap x y cs =>
    have lhs_eq :
        (Tree.insertSumList (x :: y :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Tree.node a cs')) =
          (Tree.insertSum x T₂).map
              (fun c' => Nonplanar.mk (Tree.node a (c' :: y :: cs))) +
            (Tree.insertSumList (y :: cs) T₂).map
              (fun cs' => Nonplanar.mk (Tree.node a (x :: cs'))) := by
      exact insertSumList_cons_proj a x (y :: cs) T₂
    have rhs_eq :
        (Tree.insertSumList (y :: x :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Tree.node a cs')) =
          (Tree.insertSum y T₂).map
              (fun c' => Nonplanar.mk (Tree.node a (c' :: x :: cs))) +
            (Tree.insertSumList (x :: cs) T₂).map
              (fun cs' => Nonplanar.mk (Tree.node a (y :: cs'))) := by
      exact insertSumList_cons_proj a y (x :: cs) T₂
    have lhs_inner :
        (Tree.insertSumList (y :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Tree.node a (x :: cs'))) =
          (Tree.insertSum y T₂).map
              (fun c' => Nonplanar.mk (Tree.node a (x :: c' :: cs))) +
            (Tree.insertSumList cs T₂).map
              (fun cs' => Nonplanar.mk (Tree.node a (x :: y :: cs'))) := by
      rw [Tree.insertSumList_cons, Multiset.map_add, Multiset.map_map,
          Multiset.map_map]
      rfl
    have rhs_inner :
        (Tree.insertSumList (x :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Tree.node a (y :: cs'))) =
          (Tree.insertSum x T₂).map
              (fun c' => Nonplanar.mk (Tree.node a (y :: c' :: cs))) +
            (Tree.insertSumList cs T₂).map
              (fun cs' => Nonplanar.mk (Tree.node a (y :: x :: cs'))) := by
      rw [Tree.insertSumList_cons, Multiset.map_add, Multiset.map_map,
          Multiset.map_map]
      rfl
    rw [lhs_eq, rhs_eq, lhs_inner, rhs_inner]
    have hAB' : (Tree.insertSum x T₂).map
                  (fun c' => Nonplanar.mk (Tree.node a (c' :: y :: cs))) =
                (Tree.insertSum x T₂).map
                  (fun c' => Nonplanar.mk (Tree.node a (y :: c' :: cs))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Tree.permEquiv_root_perm
      exact List.Perm.swap _ _ _
    have hBA' : (Tree.insertSum y T₂).map
                  (fun c' => Nonplanar.mk (Tree.node a (x :: c' :: cs))) =
                (Tree.insertSum y T₂).map
                  (fun c' => Nonplanar.mk (Tree.node a (c' :: x :: cs))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Tree.permEquiv_root_perm
      exact List.Perm.swap _ _ _
    have hCC' : (Tree.insertSumList cs T₂).map
                  (fun cs' => Nonplanar.mk (Tree.node a (x :: y :: cs'))) =
                (Tree.insertSumList cs T₂).map
                  (fun cs' => Nonplanar.mk (Tree.node a (y :: x :: cs'))) := by
      apply Multiset.map_congr rfl
      intro cs' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Tree.permEquiv_root_perm
      exact List.Perm.swap _ _ _
    rw [hAB', hBA', hCC']
    abel
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Left invariance — `T₁ → T₁'` via PermStep induction -/

private theorem insertSumList_permStep_at_aux : ∀ (a : α) (T₂ : Tree α)
    (pre : List (Tree α)) (post : List (Tree α)) (old new : Tree α),
    (Tree.insertSum old T₂).map Nonplanar.mk =
      (Tree.insertSum new T₂).map Nonplanar.mk →
    Nonplanar.mk old = Nonplanar.mk new →
    (Tree.insertSumList (pre ++ old :: post) T₂).map
        (fun cs' => (Nonplanar.mk (Tree.node a cs') : Nonplanar α)) =
    (Tree.insertSumList (pre ++ new :: post) T₂).map
        (fun cs' => Nonplanar.mk (Tree.node a cs'))
  | a, T₂, [], post, old, new, ih_sub, h_mk => by
    simp only [List.nil_append]
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · rw [map_node_cons_via_mk a post (M := Tree.insertSum old T₂),
          map_node_cons_via_mk a post (M := Tree.insertSum new T₂),
          ih_sub]
    · apply Multiset.map_congr rfl
      intro cs' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Tree.permEquiv_recurse_lift [] cs'
      exact Nonplanar.mk_eq_mk_iff.mp h_mk
  | a, T₂, p :: pre', post, old, new, ih_sub, h_mk => by
    show (Tree.insertSumList (p :: (pre' ++ old :: post)) T₂).map
            (fun cs' => Nonplanar.mk (Tree.node a cs')) =
         (Tree.insertSumList (p :: (pre' ++ new :: post)) T₂).map
            (fun cs' => Nonplanar.mk (Tree.node a cs'))
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Tree.permEquiv_recurse_lift (c' :: pre') post
      exact Nonplanar.mk_eq_mk_iff.mp h_mk
    · have ih_tail := insertSumList_permStep_at_aux a T₂ pre' post old new ih_sub h_mk
      rw [map_node_sibling_cons_via_mk a p
            (M := Tree.insertSumList (pre' ++ old :: post) T₂),
          map_node_sibling_cons_via_mk a p
            (M := Tree.insertSumList (pre' ++ new :: post) T₂),
          ih_tail]

/-- Left invariance for `insertSum` under a single `PermStep` on T₁. -/
theorem insertSum_permStep_left {T₁ T₁' : Tree α}
    (h : Tree.PermStep T₁ T₁') (T₂ : Tree α) :
    (Tree.insertSum T₁ T₂).map Nonplanar.mk =
      (Tree.insertSum T₁' T₂).map Nonplanar.mk := by
  induction h with
  | @swapAtRoot a l r pre post =>
    rw [insertSum_node_proj, insertSum_node_proj]
    congr 1
    · apply Nonplanar.mk_eq_mk_iff.mpr
      apply Tree.permEquiv_root_perm
      apply List.Perm.cons
      exact List.Perm.append_left pre (List.Perm.swap r l post)
    · have hperm : (pre ++ l :: r :: post).Perm (pre ++ r :: l :: post) :=
        List.Perm.append_left pre (List.Perm.swap r l post)
      exact insertSumList_proj_perm_aux a T₂ hperm
  | @recurse a pre old new post hsub ih =>
    have h_mk : Nonplanar.mk old = Nonplanar.mk new :=
      Nonplanar.mk_eq_mk_iff.mpr (Tree.PermEquiv.of_step hsub)
    rw [insertSum_node_proj, insertSum_node_proj]
    congr 1
    · apply Nonplanar.mk_eq_mk_iff.mpr
      apply Tree.permEquiv_recurse_lift (T₂ :: pre) post
      exact Tree.PermEquiv.of_step hsub
    · exact insertSumList_permStep_at_aux a T₂ pre post old new ih h_mk

/-! ### EqvGen lift to `PermEquiv` -/

/-- Left invariance under `PermEquiv` on T₁. Standard `EqvGen` recipe. -/
theorem insertSum_permEquiv_left {T₁ T₁' : Tree α}
    (h : Tree.PermEquiv T₁ T₁') (T₂ : Tree α) :
    (Tree.insertSum T₁ T₂).map Nonplanar.mk =
      (Tree.insertSum T₁' T₂).map Nonplanar.mk := by
  induction h with
  | rel _ _ hstep => exact insertSum_permStep_left hstep T₂
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Native `Nonplanar.insertSum` via `Quotient.lift₂` -/

/-- The **vertex-grafting pre-Lie product on `Nonplanar α`**: lifted from
    the ordered `Tree.insertSum` via `Quotient.lift₂`, using the
    invariance lemmas from §5 and §7. -/
def insertSum : Nonplanar α → Nonplanar α → Multiset (Nonplanar α) :=
  Quotient.lift₂
    (fun (t₁ t₂ : Tree α) => (Tree.insertSum t₁ t₂).map Nonplanar.mk)
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => by
      have step1 : (Tree.insertSum a₁ a₂).map Nonplanar.mk =
                   (Tree.insertSum b₁ a₂).map Nonplanar.mk :=
        insertSum_permEquiv_left h₁ a₂
      have step2 : (Tree.insertSum b₁ a₂).map Nonplanar.mk =
                   (Tree.insertSum b₁ b₂).map Nonplanar.mk :=
        insertSum_permEquiv_right b₁ h₂
      exact step1.trans step2)

/-- Notation `T₁ ◁ T₂` for `Nonplanar.insertSum T₁ T₂`. Scoped to the
    `Nonplanar` namespace to coexist with the tree-level `◁`. -/
scoped infixl:65 " ◁ " => Nonplanar.insertSum

/-! ### Quotient-unfolding lemma + Nonplanar cardinality -/

/-- Quotient unfolding: `Nonplanar.insertSum (mk t₁) (mk t₂)` is the
    multiset of nonplanar grafting summands obtained by projecting the
    ordered grafting summands. -/
@[simp] theorem mk_insertSum (t₁ t₂ : Tree α) :
    Nonplanar.insertSum (Nonplanar.mk t₁) (Nonplanar.mk t₂) =
      (Tree.insertSum t₁ t₂).map Nonplanar.mk := rfl

/-- The number of summands of `T₁ ◁ T₂` equals `T₁.numNodes`, i.e., the
    nonplanar tree-vertex count of T₁. -/
theorem card_insertSum_eq_numNodes (T₁ T₂ : Nonplanar α) :
    Multiset.card (Nonplanar.insertSum T₁ T₂) = T₁.numNodes := by
  refine Quotient.inductionOn₂ T₁ T₂ ?_
  intro t₁ t₂
  show Multiset.card ((Tree.insertSum t₁ t₂).map Nonplanar.mk) =
    (Nonplanar.mk t₁).numNodes
  rw [Multiset.card_map, Tree.card_insertSum_eq_numNodes, numNodes_mk]

/-! ### Sanity tests -/

section Tests

/-- A leaf grafted onto a leaf gives the canonical 1-vertex grafting summand. -/
example : Nonplanar.insertSum (Nonplanar.leaf 1 : Nonplanar Nat) (Nonplanar.leaf 2)
    = ({Nonplanar.mk (Tree.node 1 [Tree.leaf 2])} : Multiset (Nonplanar Nat)) := by
  show (Tree.insertSum (Tree.leaf 1) (Tree.leaf 2)).map Nonplanar.mk = _
  rw [Tree.insertSum_leaf, Multiset.map_singleton]

/-- A nonplanar binary tree has 3 vertices, hence 3 grafting summands. -/
example : Multiset.card
    (Nonplanar.insertSum
      (Nonplanar.mk (Tree.binary 1 (Tree.leaf 2) (Tree.leaf 3)))
      (Nonplanar.leaf 4 : Nonplanar Nat)) = 3 := by
  rw [card_insertSum_eq_numNodes, numNodes_mk]
  decide

end Tests

end Nonplanar

end RootedTree
