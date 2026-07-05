/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insert
import Linglib.Core.Data.RoseTree.Nonplanar
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# Single-tree pre-Lie product `insertSum` on `RoseTree α` and `Nonplanar α`
[foissy-typed-decorated-rooted-trees-2018]
[chapoton-livernet-2001]
[marcolli-chomsky-berwick-2025]

The **vertex-grafting pre-Lie product** on n-ary rooted trees: for
trees `T₁, T₂`, `T₁ ◁ T₂` is the multiset of all trees obtained by
grafting `T₂` as a new child of some vertex of `T₁`:

  T₁ ◁ T₂ = Σ_{v ∈ V(T₁)} graft(v, T₁, T₂)

This file contains both the ordered definition (Foissy 2018 Prop 2.2,
Chapoton-Livernet) on `RoseTree α` and its descent through `Nonplanar.mk`
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
- §5: Right invariance (`Perm` on T₂).
- §6: List-side perm + componentwise `Perm` invariance.
- §7: Left invariance (`Perm` / `PermList` on T₁).
- §8: Native `Nonplanar.insertSum` via `Quotient.lift₂`.
- §9: Quotient-unfolding lemma + Nonplanar cardinality.
- §10: Sanity tests.

Sibling files:
- `Path.lean` / `Insert.lean` — path-based vertex enumeration + grafting
  (`Pathed.vertices`, `Pathed.insertAt`).
- `Insertion.lean` — multi-tree multi-vertex grafting (Foissy 2021).
- `Algebra.lean` — `RightPreLieAlgebra ℤ` instance.

-/

namespace RoseTree

variable {α : Type*}

/-! ### `insertSum` — the vertex-grafting product

Mutually recursive on `(RoseTree, List RoseTree)`. Each summand of
`insertSum T₁ T₂` corresponds to a choice of vertex `v` in `T₁`; the
corresponding tree replaces `v`'s children list `cs` with `T₂ :: cs`.
This is a paramorphic recursion — the original children list is reused
to rebuild the grafted node — so it is written by hand rather than as a
`fold`. -/

mutual
/-- The pre-Lie product `T₁ ◁ T₂` on `RoseTree α` (vertex grafting): the
    multiset of all trees obtained by grafting `T₂` as a new child of
    some vertex of `T₁`. -/
def insertSum : RoseTree α → RoseTree α → Multiset (RoseTree α)
  | .node a cs, T₂ =>
      ((RoseTree.node a (T₂ :: cs)) : RoseTree α) ::ₘ
        (insertSumList cs T₂).map (fun cs' => .node a cs')
/-- Auxiliary: graft `T₂` inside one of the entries of a children list,
    returning the multiset of resulting children-lists (one per vertex
    inside the list). -/
def insertSumList : List (RoseTree α) → RoseTree α →
    Multiset (List (RoseTree α))
  | [], _ => 0
  | c :: cs, T₂ =>
      (insertSum c T₂).map (fun c' => c' :: cs)
        + (insertSumList cs T₂).map (fun cs' => c :: cs')
end

/-- Notation `T₁ ◁ T₂` for `insertSum T₁ T₂`. The right-triangular
    Unicode glyph matches Foissy's typesetting. Scoped to avoid
    clashing with mathlib's `LeftPreLieRing` notation. -/
scoped infixl:65 " ◁ " => insertSum

@[simp] theorem insertSum_node (a : α) (cs : List (RoseTree α))
    (T₂ : RoseTree α) :
    (RoseTree.node a cs) ◁ T₂ =
      ((RoseTree.node a (T₂ :: cs)) : RoseTree α) ::ₘ
        (insertSumList cs T₂).map (fun cs' => .node a cs') := by
  unfold insertSum; rfl

@[simp] theorem insertSumList_nil (T₂ : RoseTree α) :
    insertSumList ([] : List (RoseTree α)) T₂ = 0 := by
  conv_lhs => unfold insertSumList

@[simp] theorem insertSumList_cons (c : RoseTree α) (cs : List (RoseTree α))
    (T₂ : RoseTree α) :
    insertSumList (c :: cs) T₂ =
      (insertSum c T₂).map (fun c' => c' :: cs)
        + (insertSumList cs T₂).map (fun cs' => c :: cs') := by
  conv_lhs => unfold insertSumList

/-- A leaf has exactly one summand: graft `T₂` at the root. -/
@[simp] theorem insertSum_leaf (a : α) (T₂ : RoseTree α) :
    RoseTree.leaf a ◁ T₂ =
      ({RoseTree.node a [T₂]} : Multiset (RoseTree α)) := by
  show insertSum (RoseTree.node a []) T₂ =
       ({RoseTree.node a [T₂]} : Multiset (RoseTree α))
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
    (pre cs' : List (RoseTree α)) (c : RoseTree α) (q : Pathed.Path)
    (T₂ : RoseTree α) :
    Pathed.insertAt (pre.length :: q) T₂ (RoseTree.node a (pre ++ (c :: cs')))
      = RoseTree.node a (pre ++ (Pathed.insertAt q T₂ c :: cs')) := by
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
theorem insertSum_eq_coe_map_insertAt : ∀ (T₁ T₂ : RoseTree α),
    T₁ ◁ T₂ =
      ((Pathed.vertices T₁).map (fun p => Pathed.insertAt p T₂ T₁)
        : Multiset (RoseTree α))
  | .node a cs, T₂ => by
    rw [insertSum_node, Pathed.vertices_node]
    have aux := insertSumList_eq_coe_map_pathInsertAt_aux a [] cs T₂
    simp only [List.nil_append, List.length_nil] at aux
    rw [aux, List.map_cons, ← Multiset.cons_coe, Pathed.insertAt_nil]
/-- Auxiliary: with `pre` siblings before the cs-tail being grafted in,
    children-list grafting through `pre`-prefixed `RoseTree.node a`
    equals the path-based insertions at offset `pre.length` into the
    original host `RoseTree.node a (pre ++ cs)`. -/
theorem insertSumList_eq_coe_map_pathInsertAt_aux :
    ∀ (a : α) (pre cs : List (RoseTree α)) (T₂ : RoseTree α),
    (insertSumList cs T₂).map (fun cs' => RoseTree.node a (pre ++ cs'))
      = ((Pathed.verticesAux pre.length cs).map
          (fun p => Pathed.insertAt p T₂ (RoseTree.node a (pre ++ cs)))
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
theorem card_insertSum_eq_length_vertices (T₁ T₂ : RoseTree α) :
    Multiset.card (T₁ ◁ T₂) = (Pathed.vertices T₁).length := by
  rw [insertSum_eq_coe_map_insertAt, Multiset.coe_card, List.length_map]

/-- The number of summands in `T₁ ◁ T₂` equals `T₁.numNodes`
    (total vertex count). -/
theorem card_insertSum_eq_numNodes (T₁ T₂ : RoseTree α) :
    Multiset.card (T₁ ◁ T₂) = T₁.numNodes := by
  rw [card_insertSum_eq_length_vertices, Pathed.length_vertices_eq_numNodes]

/-! ### Sanity tests at compile time -/

section Tests

example : (RoseTree.leaf 1 : RoseTree Nat) ◁ RoseTree.leaf 2
    = ({RoseTree.node 1 [RoseTree.leaf 2]} : Multiset (RoseTree Nat)) := by
  rw [insertSum_leaf]

/-- A binary tree has 3 vertices, hence 3 grafting summands. -/
example : Multiset.card
    ((RoseTree.binary 1 (RoseTree.leaf 2) (RoseTree.leaf 3) : RoseTree Nat) ◁
      RoseTree.leaf 4) = 3 := by
  rw [card_insertSum_eq_numNodes]
  decide

/-- The grafting decomposition: each summand corresponds to a path. -/
example (T₁ T₂ : RoseTree Nat) :
    Multiset.card (T₁ ◁ T₂) = (Pathed.vertices T₁).length :=
  card_insertSum_eq_length_vertices T₁ T₂

end Tests

end RoseTree

/-! # Descent of `insertSum` through `Nonplanar.mk`

The descent layer: lift `RoseTree.insertSum` to `Nonplanar α` via
`Quotient.lift₂`, requiring invariance under `Perm` on both
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

private theorem insertSumList_cons_proj (a : α) (c : RoseTree α)
    (cs : List (RoseTree α)) (T₂ : RoseTree α) :
    (RoseTree.insertSumList (c :: cs) T₂).map
        (fun cs' => (Nonplanar.mk (RoseTree.node a cs') : Nonplanar α)) =
      (RoseTree.insertSum c T₂).map
          (fun c' => Nonplanar.mk (RoseTree.node a (c' :: cs))) +
        (RoseTree.insertSumList cs T₂).map
          (fun cs' => Nonplanar.mk (RoseTree.node a (c :: cs'))) := by
  rw [RoseTree.insertSumList_cons, Multiset.map_add, Multiset.map_map,
      Multiset.map_map]
  rfl

/-- Companion: `(insertSum (node a cs) T₂).map mk` decomposes as the head
    `mk (node a (T₂ :: cs))` plus the projected tail
    `(insertSumList cs T₂).map (fun cs' => mk (node a cs'))`. -/
private theorem insertSum_node_proj (a : α) (cs : List (RoseTree α)) (T₂ : RoseTree α) :
    (RoseTree.insertSum (RoseTree.node a cs) T₂).map Nonplanar.mk =
      Nonplanar.mk (RoseTree.node a (T₂ :: cs)) ::ₘ
        (RoseTree.insertSumList cs T₂).map
          (fun cs' => Nonplanar.mk (RoseTree.node a cs')) := by
  rw [RoseTree.insertSum_node, Multiset.map_cons, Multiset.map_map]
  rfl

/-- Wrapper-shift helper: `(M.map (fun c' => mk (node a (c' :: cs)))) =
    ((M.map mk).map (fun n => mk (node a (n.out :: cs))))`. Used when we
    want to factor the `c' :: cs` wrapper through `mk` so that the inner
    multiset becomes `M.map mk` (a form we can substitute via the IH). -/
private theorem map_node_cons_via_mk (a : α) (cs : List (RoseTree α))
    {M : Multiset (RoseTree α)} :
    M.map (fun c' => Nonplanar.mk (RoseTree.node a (c' :: cs))) =
      (M.map Nonplanar.mk).map
        (fun n : Nonplanar α =>
          Nonplanar.mk (RoseTree.node a (n.out :: cs))) := by
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro c' _
  apply Nonplanar.mk_eq_mk_iff.mpr
  apply RoseTree.Perm.congr_child [] cs
  exact (Quotient.exact (Quotient.out_eq (Nonplanar.mk c'))).symm

/-- Wrapper-shift helper for sibling-cons: factor a sibling-cons wrapper
    through `mk ∘ node a` so the IH on `(M.map (mk ∘ node a))`
    substitutes cleanly. -/
private theorem map_node_sibling_cons_via_mk (a : α) (p : RoseTree α)
    {M : Multiset (List (RoseTree α))} :
    M.map (fun cs' => Nonplanar.mk (RoseTree.node a (p :: cs'))) =
      (M.map (fun cs' => Nonplanar.mk (RoseTree.node a cs'))).map
        (fun n : Nonplanar α =>
          Nonplanar.mk (RoseTree.node a (p :: n.out.children))) := by
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro cs' _
  apply Nonplanar.mk_eq_mk_iff.mpr
  have hbase : RoseTree.Perm (RoseTree.node a cs')
               (Nonplanar.mk (RoseTree.node a cs')).out :=
    (Quotient.exact (Quotient.out_eq (Nonplanar.mk (RoseTree.node a cs')))).symm
  have hvalue : (Nonplanar.mk (RoseTree.node a cs')).out.value = a := by
    have := RoseTree.Perm.value_eq hbase
    simp only [RoseTree.value_node] at this
    exact this.symm
  have hform : (Nonplanar.mk (RoseTree.node a cs')).out =
      RoseTree.node a (Nonplanar.mk (RoseTree.node a cs')).out.children := by
    generalize (Nonplanar.mk (RoseTree.node a cs')).out = q at hvalue
    cases q with
    | node b qs =>
      simp only [RoseTree.value_node] at hvalue
      rw [hvalue]
      rfl
  have hbase' : RoseTree.Perm (RoseTree.node a cs')
      (RoseTree.node a (Nonplanar.mk (RoseTree.node a cs')).out.children) := by
    rw [← hform]; exact hbase
  exact RoseTree.Perm.cons_child p hbase'

/-! ### Right invariance — `T₂ → T₂'`

If `T₂ ≡ T₂'` (`Perm`), then `(T₁ ◁ T₂).map mk = (T₁ ◁ T₂').map mk`
for any T₁. Mutually inducted with the children-list version
`insertSumList`. -/

mutual
private theorem insertSum_perm_right_aux : ∀ (T₁ T₂ T₂' : RoseTree α)
    (_ : RoseTree.Perm T₂ T₂'),
    (RoseTree.insertSum T₁ T₂).map Nonplanar.mk =
      (RoseTree.insertSum T₁ T₂').map Nonplanar.mk
  | .node a cs, T₂, T₂', h => by
    rw [insertSum_node_proj, insertSum_node_proj]
    congr 1
    · apply Nonplanar.mk_eq_mk_iff.mpr
      exact RoseTree.Perm.congr_child [] cs h
    · exact insertSumList_perm_right_aux a cs T₂ T₂' h
private theorem insertSumList_perm_right_aux : ∀ (a : α) (cs : List (RoseTree α))
    (T₂ T₂' : RoseTree α) (_ : RoseTree.Perm T₂ T₂'),
    (RoseTree.insertSumList cs T₂).map
        (fun cs' => (Nonplanar.mk (RoseTree.node a cs') : Nonplanar α)) =
    (RoseTree.insertSumList cs T₂').map
        (fun cs' => Nonplanar.mk (RoseTree.node a cs'))
  | _, [], _, _, _ => by
    rw [RoseTree.insertSumList_nil, RoseTree.insertSumList_nil]
  | a, c :: cs, T₂, T₂', h => by
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · have ih := insertSum_perm_right_aux c T₂ T₂' h
      rw [map_node_cons_via_mk a cs (M := RoseTree.insertSum c T₂),
          map_node_cons_via_mk a cs (M := RoseTree.insertSum c T₂'),
          ih]
    · have ih_list := insertSumList_perm_right_aux a cs T₂ T₂' h
      rw [map_node_sibling_cons_via_mk a c (M := RoseTree.insertSumList cs T₂),
          map_node_sibling_cons_via_mk a c (M := RoseTree.insertSumList cs T₂'),
          ih_list]
end

/-- Right invariance for `insertSum`. -/
theorem insertSum_perm_right (T₁ : RoseTree α) {T₂ T₂' : RoseTree α}
    (h : RoseTree.Perm T₂ T₂') :
    (RoseTree.insertSum T₁ T₂).map Nonplanar.mk =
      (RoseTree.insertSum T₁ T₂').map Nonplanar.mk :=
  insertSum_perm_right_aux T₁ T₂ T₂' h

/-! ### List-side `mk`-projection of `insertSumList`

Two key properties of `(insertSumList cs T₂).map (mk ∘ .node a)`:
Perm-invariance in `cs` and componentwise `Perm`-invariance. -/

private theorem insertSumList_proj_perm_aux (a : α) (T₂ : RoseTree α) :
    ∀ {cs cs' : List (RoseTree α)},
      cs.Perm cs' →
      (RoseTree.insertSumList cs T₂).map
          (fun cs' => (Nonplanar.mk (RoseTree.node a cs') : Nonplanar α)) =
      (RoseTree.insertSumList cs' T₂).map
          (fun cs' => Nonplanar.mk (RoseTree.node a cs')) := by
  intro cs cs' h
  induction h with
  | nil => rfl
  | @cons x cs cs' hperm ih =>
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    have head_eq :
        (RoseTree.insertSum x T₂).map
          (fun c' => Nonplanar.mk (RoseTree.node a (c' :: cs))) =
        (RoseTree.insertSum x T₂).map
          (fun c' => Nonplanar.mk (RoseTree.node a (c' :: cs'))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply RoseTree.Perm.node_of_perm
      exact List.Perm.cons c' hperm
    rw [head_eq,
        map_node_sibling_cons_via_mk a x (M := RoseTree.insertSumList cs T₂),
        map_node_sibling_cons_via_mk a x (M := RoseTree.insertSumList cs' T₂),
        ih]
  | @swap x y cs =>
    have lhs_eq :
        (RoseTree.insertSumList (x :: y :: cs) T₂).map
            (fun cs' => Nonplanar.mk (RoseTree.node a cs')) =
          (RoseTree.insertSum x T₂).map
              (fun c' => Nonplanar.mk (RoseTree.node a (c' :: y :: cs))) +
            (RoseTree.insertSumList (y :: cs) T₂).map
              (fun cs' => Nonplanar.mk (RoseTree.node a (x :: cs'))) := by
      exact insertSumList_cons_proj a x (y :: cs) T₂
    have rhs_eq :
        (RoseTree.insertSumList (y :: x :: cs) T₂).map
            (fun cs' => Nonplanar.mk (RoseTree.node a cs')) =
          (RoseTree.insertSum y T₂).map
              (fun c' => Nonplanar.mk (RoseTree.node a (c' :: x :: cs))) +
            (RoseTree.insertSumList (x :: cs) T₂).map
              (fun cs' => Nonplanar.mk (RoseTree.node a (y :: cs'))) := by
      exact insertSumList_cons_proj a y (x :: cs) T₂
    have lhs_inner :
        (RoseTree.insertSumList (y :: cs) T₂).map
            (fun cs' => Nonplanar.mk (RoseTree.node a (x :: cs'))) =
          (RoseTree.insertSum y T₂).map
              (fun c' => Nonplanar.mk (RoseTree.node a (x :: c' :: cs))) +
            (RoseTree.insertSumList cs T₂).map
              (fun cs' => Nonplanar.mk (RoseTree.node a (x :: y :: cs'))) := by
      rw [RoseTree.insertSumList_cons, Multiset.map_add, Multiset.map_map,
          Multiset.map_map]
      rfl
    have rhs_inner :
        (RoseTree.insertSumList (x :: cs) T₂).map
            (fun cs' => Nonplanar.mk (RoseTree.node a (y :: cs'))) =
          (RoseTree.insertSum x T₂).map
              (fun c' => Nonplanar.mk (RoseTree.node a (y :: c' :: cs))) +
            (RoseTree.insertSumList cs T₂).map
              (fun cs' => Nonplanar.mk (RoseTree.node a (y :: x :: cs'))) := by
      rw [RoseTree.insertSumList_cons, Multiset.map_add, Multiset.map_map,
          Multiset.map_map]
      rfl
    rw [lhs_eq, rhs_eq, lhs_inner, rhs_inner]
    have hAB' : (RoseTree.insertSum x T₂).map
                  (fun c' => Nonplanar.mk (RoseTree.node a (c' :: y :: cs))) =
                (RoseTree.insertSum x T₂).map
                  (fun c' => Nonplanar.mk (RoseTree.node a (y :: c' :: cs))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply RoseTree.Perm.node_of_perm
      exact List.Perm.swap _ _ _
    have hBA' : (RoseTree.insertSum y T₂).map
                  (fun c' => Nonplanar.mk (RoseTree.node a (x :: c' :: cs))) =
                (RoseTree.insertSum y T₂).map
                  (fun c' => Nonplanar.mk (RoseTree.node a (c' :: x :: cs))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply RoseTree.Perm.node_of_perm
      exact List.Perm.swap _ _ _
    have hCC' : (RoseTree.insertSumList cs T₂).map
                  (fun cs' => Nonplanar.mk (RoseTree.node a (x :: y :: cs'))) =
                (RoseTree.insertSumList cs T₂).map
                  (fun cs' => Nonplanar.mk (RoseTree.node a (y :: x :: cs'))) := by
      apply Multiset.map_congr rfl
      intro cs' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply RoseTree.Perm.node_of_perm
      exact List.Perm.swap _ _ _
    rw [hAB', hBA', hCC']
    abel
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Left invariance — `T₁ → T₁'`

Single-position substitution (`insertSumList_subst_at_aux`) is the building
block; the headline `insertSum_perm_left` and its `PermList` companion recurse
over the `Perm` structure. -/

private theorem insertSumList_subst_at_aux : ∀ (a : α) (T₂ : RoseTree α)
    (pre : List (RoseTree α)) (post : List (RoseTree α)) (old new : RoseTree α),
    (RoseTree.insertSum old T₂).map Nonplanar.mk =
      (RoseTree.insertSum new T₂).map Nonplanar.mk →
    Nonplanar.mk old = Nonplanar.mk new →
    (RoseTree.insertSumList (pre ++ old :: post) T₂).map
        (fun cs' => (Nonplanar.mk (RoseTree.node a cs') : Nonplanar α)) =
    (RoseTree.insertSumList (pre ++ new :: post) T₂).map
        (fun cs' => Nonplanar.mk (RoseTree.node a cs'))
  | a, T₂, [], post, old, new, ih_sub, h_mk => by
    simp only [List.nil_append]
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · rw [map_node_cons_via_mk a post (M := RoseTree.insertSum old T₂),
          map_node_cons_via_mk a post (M := RoseTree.insertSum new T₂),
          ih_sub]
    · apply Multiset.map_congr rfl
      intro cs' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply RoseTree.Perm.congr_child [] cs'
      exact Nonplanar.mk_eq_mk_iff.mp h_mk
  | a, T₂, p :: pre', post, old, new, ih_sub, h_mk => by
    show (RoseTree.insertSumList (p :: (pre' ++ old :: post)) T₂).map
            (fun cs' => Nonplanar.mk (RoseTree.node a cs')) =
         (RoseTree.insertSumList (p :: (pre' ++ new :: post)) T₂).map
            (fun cs' => Nonplanar.mk (RoseTree.node a cs'))
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply RoseTree.Perm.congr_child (c' :: pre') post
      exact Nonplanar.mk_eq_mk_iff.mp h_mk
    · have ih_tail := insertSumList_subst_at_aux a T₂ pre' post old new ih_sub h_mk
      rw [map_node_sibling_cons_via_mk a p
            (M := RoseTree.insertSumList (pre' ++ old :: post) T₂),
          map_node_sibling_cons_via_mk a p
            (M := RoseTree.insertSumList (pre' ++ new :: post) T₂),
          ih_tail]

mutual
/-- Left invariance for `insertSum` under `Perm` of the host `T₁`. The
    `node` case splits `insertSum` via `insertSum_node_proj` into the root
    graft (a `Perm.cons_child`) and the sibling recursion (the `PermList`
    companion). -/
theorem insertSum_perm_left :
    ∀ {T₁ T₁' : RoseTree α}, RoseTree.Perm T₁ T₁' → ∀ (T₂ : RoseTree α),
      (RoseTree.insertSum T₁ T₂).map Nonplanar.mk =
        (RoseTree.insertSum T₁' T₂).map Nonplanar.mk
  | _, _, @RoseTree.Perm.node _ a cs ds h, T₂ => by
    rw [insertSum_node_proj a cs T₂, insertSum_node_proj a ds T₂]
    congr 1
    · exact Nonplanar.mk_eq_mk_iff.mpr
        (RoseTree.Perm.cons_child T₂ (RoseTree.Perm.node h))
    · exact insertSumList_permList_proj h a T₂
  | _, _, .trans h₁ h₂, T₂ =>
    (insertSum_perm_left h₁ T₂).trans (insertSum_perm_left h₂ T₂)

/-- Companion: sibling-level invariance of the projected `insertSumList`
    under `PermList` of the children. The `cons` case changes the head child
    (via `insertSum_perm_left`) then the tail (recursion); `swap` reorders
    identical siblings (`insertSumList_proj_perm_aux`). -/
private theorem insertSumList_permList_proj :
    ∀ {cs ds : List (RoseTree α)}, RoseTree.PermList cs ds →
      ∀ (a : α) (T₂ : RoseTree α),
        (RoseTree.insertSumList cs T₂).map
            (fun cs' => (Nonplanar.mk (RoseTree.node a cs') : Nonplanar α)) =
        (RoseTree.insertSumList ds T₂).map
            (fun cs' => Nonplanar.mk (RoseTree.node a cs'))
  | _, _, .nil, _, _ => rfl
  | _, _, @RoseTree.PermList.cons _ c d cs' ds' hcd hs, a, T₂ => by
    have step1 :
        (RoseTree.insertSumList (c :: cs') T₂).map
            (fun cs' => (Nonplanar.mk (RoseTree.node a cs') : Nonplanar α)) =
        (RoseTree.insertSumList (d :: cs') T₂).map
            (fun cs' => Nonplanar.mk (RoseTree.node a cs')) :=
      insertSumList_subst_at_aux a T₂ [] cs' c d
        (insertSum_perm_left hcd T₂) (Nonplanar.mk_eq_mk_iff.mpr hcd)
    have step2 :
        (RoseTree.insertSumList (d :: cs') T₂).map
            (fun cs' => (Nonplanar.mk (RoseTree.node a cs') : Nonplanar α)) =
        (RoseTree.insertSumList (d :: ds') T₂).map
            (fun cs' => Nonplanar.mk (RoseTree.node a cs')) := by
      rw [insertSumList_cons_proj a d cs' T₂, insertSumList_cons_proj a d ds' T₂]
      congr 1
      · apply Multiset.map_congr rfl
        intro c' _
        exact Nonplanar.mk_eq_mk_iff.mpr
          (RoseTree.Perm.cons_child c' (RoseTree.Perm.node hs))
      · rw [map_node_sibling_cons_via_mk a d (M := RoseTree.insertSumList cs' T₂),
            map_node_sibling_cons_via_mk a d (M := RoseTree.insertSumList ds' T₂),
            insertSumList_permList_proj hs a T₂]
    exact step1.trans step2
  | _, _, .swap c d cs, a, T₂ =>
    insertSumList_proj_perm_aux a T₂ (List.Perm.swap c d cs)
  | _, _, .trans h₁ h₂, a, T₂ =>
    (insertSumList_permList_proj h₁ a T₂).trans (insertSumList_permList_proj h₂ a T₂)
end

/-! ### Native `Nonplanar.insertSum` via `Quotient.lift₂` -/

/-- The **vertex-grafting pre-Lie product on `Nonplanar α`**: lifted from
    the ordered `RoseTree.insertSum` via `Quotient.lift₂`, using the
    invariance lemmas from §5 and §7. -/
def insertSum : Nonplanar α → Nonplanar α → Multiset (Nonplanar α) :=
  Quotient.lift₂
    (fun (t₁ t₂ : RoseTree α) => (RoseTree.insertSum t₁ t₂).map Nonplanar.mk)
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => by
      have step1 : (RoseTree.insertSum a₁ a₂).map Nonplanar.mk =
                   (RoseTree.insertSum b₁ a₂).map Nonplanar.mk :=
        insertSum_perm_left h₁ a₂
      have step2 : (RoseTree.insertSum b₁ a₂).map Nonplanar.mk =
                   (RoseTree.insertSum b₁ b₂).map Nonplanar.mk :=
        insertSum_perm_right b₁ h₂
      exact step1.trans step2)

/-- Notation `T₁ ◁ T₂` for `Nonplanar.insertSum T₁ T₂`. Scoped to the
    `Nonplanar` namespace to coexist with the tree-level `◁`. -/
scoped infixl:65 " ◁ " => Nonplanar.insertSum

/-! ### Quotient-unfolding lemma + Nonplanar cardinality -/

/-- Quotient unfolding: `Nonplanar.insertSum (mk t₁) (mk t₂)` is the
    multiset of nonplanar grafting summands obtained by projecting the
    ordered grafting summands. -/
@[simp] theorem mk_insertSum (t₁ t₂ : RoseTree α) :
    Nonplanar.insertSum (Nonplanar.mk t₁) (Nonplanar.mk t₂) =
      (RoseTree.insertSum t₁ t₂).map Nonplanar.mk := rfl

/-- The number of summands of `T₁ ◁ T₂` equals `T₁.numNodes`, i.e., the
    nonplanar tree-vertex count of T₁. -/
theorem card_insertSum_eq_numNodes (T₁ T₂ : Nonplanar α) :
    Multiset.card (Nonplanar.insertSum T₁ T₂) = T₁.numNodes := by
  refine Quotient.inductionOn₂ T₁ T₂ ?_
  intro t₁ t₂
  show Multiset.card ((RoseTree.insertSum t₁ t₂).map Nonplanar.mk) =
    (Nonplanar.mk t₁).numNodes
  rw [Multiset.card_map, RoseTree.card_insertSum_eq_numNodes, numNodes_mk]

/-! ### Sanity tests -/

section Tests

/-- A leaf grafted onto a leaf gives the canonical 1-vertex grafting summand. -/
example : Nonplanar.insertSum (Nonplanar.leaf 1 : Nonplanar Nat) (Nonplanar.leaf 2)
    = ({Nonplanar.mk (RoseTree.node 1 [RoseTree.leaf 2])} : Multiset (Nonplanar Nat)) := by
  show (RoseTree.insertSum (RoseTree.leaf 1) (RoseTree.leaf 2)).map Nonplanar.mk = _
  rw [RoseTree.insertSum_leaf, Multiset.map_singleton]

/-- A nonplanar binary tree has 3 vertices, hence 3 grafting summands. -/
example : Multiset.card
    (Nonplanar.insertSum
      (Nonplanar.mk (RoseTree.binary 1 (RoseTree.leaf 2) (RoseTree.leaf 3)))
      (Nonplanar.leaf 4 : Nonplanar Nat)) = 3 := by
  rw [card_insertSum_eq_numNodes, numNodes_mk]
  decide

end Tests

end Nonplanar

end RootedTree
