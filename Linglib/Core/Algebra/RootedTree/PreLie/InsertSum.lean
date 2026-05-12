/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Vertex
import Linglib.Core.Combinatorics.RootedTree.Nonplanar
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# Single-tree pre-Lie product `insertSum` on `Planar α` and `Nonplanar α`
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{chapoton-livernet-2001}
@cite{marcolli-chomsky-berwick-2025}

The **vertex-grafting pre-Lie product** on planar / nonplanar n-ary
rooted trees: for trees `T₁, T₂`, `T₁ ◁ T₂` is the multiset of all
trees obtained by grafting `T₂` as a new child of some vertex of `T₁`:

  T₁ ◁ T₂ = Σ_{v ∈ V(T₁)} graft(v, T₁, T₂)

This file contains both the planar definition (Foissy 2018 Prop 2.2,
Chapoton-Livernet) and its descent through `Nonplanar.mk` to the
nonplanar carrier.

## Reference

@cite{foissy-typed-decorated-rooted-trees-2018} Proposition 2.2 defines
the multiple pre-Lie product on D-decorated T-typed rooted trees (D =
decoration set, T = edge type set). Specialized to T = {*} (single
edge type) and decoration set α, this is exactly `insertSum`.

@cite{chapoton-livernet-2001} introduced the original CL pre-Lie
product on undecorated rooted trees, of which the present construction
is the decorated extension.

## Relation to MCB §1.7

@cite{marcolli-chomsky-berwick-2025} Definition 1.7.1 (book p. 77)
defines a DIFFERENT pre-Lie product on **nonplanar BINARY** rooted
trees with leaf labels in `SO_0` (internal vertices unlabeled), via
**edge subdivision**. The two are distinct algebras on distinct
carriers — neither is a specialization of the other. Both satisfy the
abstract pre-Lie identity (mathlib's `RightPreLieAlgebra`); a future
binary substrate file would add a separate `RightPreLieAlgebra`
instance for MCB §1.7.

## File scope

- §1: `insertSum` planar definition + simp lemmas + leaf case.
- §2: Cardinality (`card_insertSum_eq_weight`).
- §3: Decomposition (`insertSum_eq_coe_map_insertAt`).
- §4: Cardinality consistency.
- §5: Cons-decomposition projection helpers (descent §1).
- §6: Right invariance (PlanarEquiv on T₂).
- §7: List-side perm + componentwise PlanarEquiv invariance.
- §8: Left invariance (PlanarEquiv on T₁).
- §9: EqvGen lift to PlanarEquiv on either argument.
- §10: Native `Nonplanar.insertSum` via `Quotient.lift₂`.
- §11: Quotient-unfolding lemma + Nonplanar cardinality.
- §12: Sanity tests.

Sibling files:
- `Vertex.lean` — vertex machinery (`Vertex`, `insertAt`, `vertices`).
- `Insertion.lean` — multi-tree multi-vertex grafting (Foissy 2021).
- `VertexBijection.lean` — vertex classification + commutativity.
- `Algebra.lean` — `RightPreLieAlgebra ℤ` instance.

## Status

`[UPSTREAM]` candidate. Sorry-free.
-/

namespace RootedTree

namespace Planar

variable {α : Type*}

/-! ## §1: `insertSum` — the vertex-grafting product

Mutually recursive on `(Planar, List Planar)` mirroring `weight` /
`weightList` etc. Each summand of `insertSum T₁ T₂` corresponds to a
choice of vertex `v` in `T₁`; the corresponding tree replaces `v`'s
children list `cs` with `T₂ :: cs`. -/

mutual
/-- The pre-Lie product `T₁ ◁ T₂` on `Planar α` (vertex grafting): the
    multiset of all trees obtained by grafting `T₂` as a new child of
    some vertex of `T₁`. -/
def insertSum : Planar α → Planar α → Multiset (Planar α)
  | .node a cs, T₂ =>
      ((Planar.node a (T₂ :: cs)) : Planar α) ::ₘ
        (insertSumList cs T₂).map (fun cs' => .node a cs')
/-- Auxiliary: graft `T₂` inside one of the entries of a children list,
    returning the multiset of resulting children-lists (one per vertex
    inside the list). -/
def insertSumList : List (Planar α) → Planar α →
    Multiset (List (Planar α))
  | [], _ => 0
  | c :: cs, T₂ =>
      (insertSum c T₂).map (fun c' => c' :: cs)
        + (insertSumList cs T₂).map (fun cs' => c :: cs')
end

/-- Notation `T₁ ◁ T₂` for `insertSum T₁ T₂`. The right-triangular
    Unicode glyph matches Foissy's typesetting. Scoped to avoid
    clashing with mathlib's `LeftPreLieRing` notation. -/
scoped infixl:65 " ◁ " => insertSum

@[simp] theorem insertSum_node (a : α) (cs : List (Planar α))
    (T₂ : Planar α) :
    (Planar.node a cs) ◁ T₂ =
      ((Planar.node a (T₂ :: cs)) : Planar α) ::ₘ
        (insertSumList cs T₂).map (fun cs' => .node a cs') := by
  unfold insertSum; rfl

@[simp] theorem insertSumList_nil (T₂ : Planar α) :
    insertSumList ([] : List (Planar α)) T₂ = 0 := by
  conv_lhs => unfold insertSumList

@[simp] theorem insertSumList_cons (c : Planar α) (cs : List (Planar α))
    (T₂ : Planar α) :
    insertSumList (c :: cs) T₂ =
      (insertSum c T₂).map (fun c' => c' :: cs)
        + (insertSumList cs T₂).map (fun cs' => c :: cs') := by
  conv_lhs => unfold insertSumList

/-- A leaf has exactly one summand: graft `T₂` at the root. -/
@[simp] theorem insertSum_leaf (a : α) (T₂ : Planar α) :
    Planar.leaf a ◁ T₂ =
      ({Planar.node a [T₂]} : Multiset (Planar α)) := by
  show insertSum (Planar.node a []) T₂ = _
  rw [insertSum_node, insertSumList_nil]
  simp

/-! ## §2: Cardinality — `card (T₁ ◁ T₂) = T₁.weight`

Each vertex of `T₁` contributes one summand. Proved by mutual
structural induction mirroring the definition. -/

mutual
/-- The number of summands in `T₁ ◁ T₂` equals `T₁.weight`
    (total vertex count). -/
theorem card_insertSum_eq_weight : ∀ (T₁ T₂ : Planar α),
    Multiset.card (T₁ ◁ T₂) = T₁.weight
  | .node a cs, T₂ => by
    rw [insertSum_node]
    simp only [Multiset.card_cons, Multiset.card_map]
    rw [card_insertSumList_eq_weightList cs T₂]
    show weightList cs + 1 = (Planar.node a cs).weight
    show weightList cs + 1 = 1 + weightList cs
    omega
/-- The number of children-lists in `insertSumList cs T₂` equals
    `weightList cs` (sum of weights of entries). -/
theorem card_insertSumList_eq_weightList : ∀ (cs : List (Planar α))
    (T₂ : Planar α),
    Multiset.card (insertSumList cs T₂) = weightList cs
  | [], _ => by rw [insertSumList_nil]; rfl
  | c :: cs', T₂ => by
    rw [insertSumList_cons]
    simp only [Multiset.card_add, Multiset.card_map]
    rw [card_insertSum_eq_weight c T₂,
        card_insertSumList_eq_weightList cs' T₂]
    show c.weight + weightList cs' = weightList (c :: cs')
    rfl
end

/-! ## §3: Decomposition — `insertSum` via `vertices` + `insertAt`

Bridge lemma between the recursive (Multiset) formulation of `insertSum`
in §1 and the per-vertex (List) formulation in `Vertex.lean`. The
lemma is the basis for the pre-Lie identity proof in `Algebra.lean`:
each summand of `insertSum T₁ T₂` is uniquely identified by a vertex
of `T₁`. -/

mutual
/-- **Decomposition lemma**: `T₁ ◁ T₂` equals the multiset of
    `insertAt v T₂` for `v` ranging over `vertices T₁`. -/
theorem insertSum_eq_coe_map_insertAt : ∀ (T₁ T₂ : Planar α),
    T₁ ◁ T₂ =
      ((vertices T₁).map (fun v => insertAt v T₂) : Multiset (Planar α))
  | .node a cs, T₂ => by
    rw [insertSum_node, vertices_node,
        insertSumList_eq_coe_map_insertAtList cs T₂]
    simp only [Multiset.map_coe, List.map_cons, List.map_map,
               Function.comp_def, insertAt_root, insertAt_inChild,
               ← Multiset.cons_coe]
/-- `insertSumList cs T₂` equals the multiset of `insertAtList vl T₂`
    for `vl` ranging over `verticesList cs`. -/
theorem insertSumList_eq_coe_map_insertAtList :
    ∀ (cs : List (Planar α)) (T₂ : Planar α),
    insertSumList cs T₂ =
      ((verticesList cs).map (fun vl => insertAtList vl T₂)
          : Multiset (List (Planar α)))
  | [], _ => by
    rw [insertSumList_nil, verticesList_nil]
    rfl
  | c :: cs, T₂ => by
    rw [insertSumList_cons, verticesList_cons,
        insertSum_eq_coe_map_insertAt c T₂,
        insertSumList_eq_coe_map_insertAtList cs T₂]
    simp only [Multiset.map_coe, List.map_append, List.map_map,
               Function.comp_def, insertAtList_head, insertAtList_tail,
               ← Multiset.coe_add]
end

/-! ## §4: Cardinality consistency

The two cardinality computations agree: `(T₁ ◁ T₂).card = (vertices T₁).length`. -/

theorem card_insertSum_eq_length_vertices (T₁ T₂ : Planar α) :
    Multiset.card (T₁ ◁ T₂) = (vertices T₁).length := by
  rw [card_insertSum_eq_weight, length_vertices_eq_weight]

end Planar

/-! # Descent of `insertSum` through `Nonplanar.mk`

The descent layer: lift `Planar.insertSum` to `Nonplanar α` via
`Quotient.lift₂`, requiring invariance under `PlanarEquiv` on both
arguments. Mirrors the original `PreLie/Nonplanar.lean` pre-restructure. -/

namespace Nonplanar

variable {α : Type*}

open scoped RootedTree.Planar

/-! ## §5: Cons-decomposition of `insertSumList`-projection

Helper lemma used by both §6 right-invariance and §7 list permutation
proofs. The cons case of `insertSumList cs T₂` splits into a per-head
grafting (in `insertSum c T₂`) plus a per-tail grafting (in
`insertSumList tail T₂`); after projection through `mk ∘ node a`, the
two halves are clean two-summand decompositions with simpler wrappers
than the raw `Multiset.map_map` form. -/

private theorem insertSumList_cons_proj (a : α) (c : Planar α)
    (cs : List (Planar α)) (T₂ : Planar α) :
    (Planar.insertSumList (c :: cs) T₂).map
        (fun cs' => (Nonplanar.mk (Planar.node a cs') : Nonplanar α)) =
      (Planar.insertSum c T₂).map
          (fun c' => Nonplanar.mk (Planar.node a (c' :: cs))) +
        (Planar.insertSumList cs T₂).map
          (fun cs' => Nonplanar.mk (Planar.node a (c :: cs'))) := by
  rw [Planar.insertSumList_cons, Multiset.map_add, Multiset.map_map,
      Multiset.map_map]
  rfl

/-- Companion: `(insertSum (node a cs) T₂).map mk` decomposes as the head
    `mk (node a (T₂ :: cs))` plus the projected tail
    `(insertSumList cs T₂).map (fun cs' => mk (node a cs'))`. -/
private theorem insertSum_node_proj (a : α) (cs : List (Planar α)) (T₂ : Planar α) :
    (Planar.insertSum (Planar.node a cs) T₂).map Nonplanar.mk =
      Nonplanar.mk (Planar.node a (T₂ :: cs)) ::ₘ
        (Planar.insertSumList cs T₂).map
          (fun cs' => Nonplanar.mk (Planar.node a cs')) := by
  rw [Planar.insertSum_node, Multiset.map_cons, Multiset.map_map]
  rfl

/-- Wrapper-shift helper: `(M.map (fun c' => mk (node a (c' :: cs)))) =
    ((M.map mk).map (fun n => mk (node a (n.out :: cs))))`. Used when we
    want to factor the `c' :: cs` wrapper through `mk` so that the inner
    multiset becomes `M.map mk` (a form we can substitute via the IH). -/
private theorem map_node_cons_via_mk (a : α) (cs : List (Planar α))
    {M : Multiset (Planar α)} :
    M.map (fun c' => Nonplanar.mk (Planar.node a (c' :: cs))) =
      (M.map Nonplanar.mk).map
        (fun n : Nonplanar α =>
          Nonplanar.mk (Planar.node a (n.out :: cs))) := by
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro c' _
  apply Nonplanar.mk_eq_mk_iff.mpr
  apply Planar.planarEquiv_recurse_lift [] cs
  exact (Quotient.exact (Quotient.out_eq (Nonplanar.mk c'))).symm

/-- Wrapper-shift helper for sibling-cons: factor a sibling-cons wrapper
    through `mk ∘ node a` so the IH on `(M.map (mk ∘ node a))`
    substitutes cleanly. -/
private theorem map_node_sibling_cons_via_mk (a : α) (p : Planar α)
    {M : Multiset (List (Planar α))} :
    M.map (fun cs' => Nonplanar.mk (Planar.node a (p :: cs'))) =
      (M.map (fun cs' => Nonplanar.mk (Planar.node a cs'))).map
        (fun n : Nonplanar α =>
          Nonplanar.mk (Planar.node a (p :: n.out.children))) := by
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro cs' _
  apply Nonplanar.mk_eq_mk_iff.mpr
  have hbase : Planar.PlanarEquiv (Planar.node a cs')
               (Nonplanar.mk (Planar.node a cs')).out :=
    (Quotient.exact (Quotient.out_eq (Nonplanar.mk (Planar.node a cs')))).symm
  have hlabel : (Nonplanar.mk (Planar.node a cs')).out.label = a := by
    have := Planar.planarEquiv_label_eq hbase
    simp only [Planar.label_node] at this
    exact this.symm
  have hform : (Nonplanar.mk (Planar.node a cs')).out =
      Planar.node a (Nonplanar.mk (Planar.node a cs')).out.children := by
    generalize (Nonplanar.mk (Planar.node a cs')).out = q at hlabel
    cases q with
    | node b qs =>
      simp only [Planar.label_node] at hlabel
      rw [hlabel]
      rfl
  have hbase' : Planar.PlanarEquiv (Planar.node a cs')
      (Planar.node a (Nonplanar.mk (Planar.node a cs')).out.children) := by
    rw [← hform]; exact hbase
  exact Planar.planarEquiv_cons_lift p hbase'

/-! ## §6: Right invariance — `T₂ → T₂'`

If `T₂ ≡ T₂'` (PlanarEquiv), then `(T₁ ◁ T₂).map mk = (T₁ ◁ T₂').map mk`
for any T₁. Mutually inducted with the children-list version
`insertSumList`. -/

mutual
private theorem insertSum_planarEquiv_right_aux : ∀ (T₁ T₂ T₂' : Planar α)
    (_ : Planar.PlanarEquiv T₂ T₂'),
    (Planar.insertSum T₁ T₂).map Nonplanar.mk =
      (Planar.insertSum T₁ T₂').map Nonplanar.mk
  | .node a cs, T₂, T₂', h => by
    rw [insertSum_node_proj, insertSum_node_proj]
    congr 1
    · apply Nonplanar.mk_eq_mk_iff.mpr
      exact Planar.planarEquiv_recurse_lift [] cs h
    · exact insertSumList_planarEquiv_right_aux a cs T₂ T₂' h
private theorem insertSumList_planarEquiv_right_aux : ∀ (a : α) (cs : List (Planar α))
    (T₂ T₂' : Planar α) (_ : Planar.PlanarEquiv T₂ T₂'),
    (Planar.insertSumList cs T₂).map
        (fun cs' => (Nonplanar.mk (Planar.node a cs') : Nonplanar α)) =
    (Planar.insertSumList cs T₂').map
        (fun cs' => Nonplanar.mk (Planar.node a cs'))
  | _, [], _, _, _ => by
    rw [Planar.insertSumList_nil, Planar.insertSumList_nil]
  | a, c :: cs, T₂, T₂', h => by
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · have ih := insertSum_planarEquiv_right_aux c T₂ T₂' h
      rw [map_node_cons_via_mk a cs (M := Planar.insertSum c T₂),
          map_node_cons_via_mk a cs (M := Planar.insertSum c T₂'),
          ih]
    · have ih_list := insertSumList_planarEquiv_right_aux a cs T₂ T₂' h
      rw [map_node_sibling_cons_via_mk a c (M := Planar.insertSumList cs T₂),
          map_node_sibling_cons_via_mk a c (M := Planar.insertSumList cs T₂'),
          ih_list]
end

/-- Right invariance for `insertSum`. -/
theorem insertSum_planarEquiv_right (T₁ : Planar α) {T₂ T₂' : Planar α}
    (h : Planar.PlanarEquiv T₂ T₂') :
    (Planar.insertSum T₁ T₂).map Nonplanar.mk =
      (Planar.insertSum T₁ T₂').map Nonplanar.mk :=
  insertSum_planarEquiv_right_aux T₁ T₂ T₂' h

/-! ## §7: List-side `mk`-projection of `insertSumList`

Two key properties of `(insertSumList cs T₂).map (mk ∘ .node a)`:
Perm-invariance in `cs` and componentwise PlanarEquiv-invariance. -/

private theorem insertSumList_proj_perm_aux (a : α) (T₂ : Planar α) :
    ∀ {cs cs' : List (Planar α)},
      cs.Perm cs' →
      (Planar.insertSumList cs T₂).map
          (fun cs' => (Nonplanar.mk (Planar.node a cs') : Nonplanar α)) =
      (Planar.insertSumList cs' T₂).map
          (fun cs' => Nonplanar.mk (Planar.node a cs')) := by
  intro cs cs' h
  induction h with
  | nil => rfl
  | @cons x cs cs' hperm ih =>
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    have head_eq :
        (Planar.insertSum x T₂).map
          (fun c' => Nonplanar.mk (Planar.node a (c' :: cs))) =
        (Planar.insertSum x T₂).map
          (fun c' => Nonplanar.mk (Planar.node a (c' :: cs'))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_root_perm
      exact List.Perm.cons c' hperm
    rw [head_eq,
        map_node_sibling_cons_via_mk a x (M := Planar.insertSumList cs T₂),
        map_node_sibling_cons_via_mk a x (M := Planar.insertSumList cs' T₂),
        ih]
  | @swap x y cs =>
    have lhs_eq :
        (Planar.insertSumList (x :: y :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a cs')) =
          (Planar.insertSum x T₂).map
              (fun c' => Nonplanar.mk (Planar.node a (c' :: y :: cs))) +
            (Planar.insertSumList (y :: cs) T₂).map
              (fun cs' => Nonplanar.mk (Planar.node a (x :: cs'))) := by
      exact insertSumList_cons_proj a x (y :: cs) T₂
    have rhs_eq :
        (Planar.insertSumList (y :: x :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a cs')) =
          (Planar.insertSum y T₂).map
              (fun c' => Nonplanar.mk (Planar.node a (c' :: x :: cs))) +
            (Planar.insertSumList (x :: cs) T₂).map
              (fun cs' => Nonplanar.mk (Planar.node a (y :: cs'))) := by
      exact insertSumList_cons_proj a y (x :: cs) T₂
    have lhs_inner :
        (Planar.insertSumList (y :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a (x :: cs'))) =
          (Planar.insertSum y T₂).map
              (fun c' => Nonplanar.mk (Planar.node a (x :: c' :: cs))) +
            (Planar.insertSumList cs T₂).map
              (fun cs' => Nonplanar.mk (Planar.node a (x :: y :: cs'))) := by
      rw [Planar.insertSumList_cons, Multiset.map_add, Multiset.map_map,
          Multiset.map_map]
      rfl
    have rhs_inner :
        (Planar.insertSumList (x :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a (y :: cs'))) =
          (Planar.insertSum x T₂).map
              (fun c' => Nonplanar.mk (Planar.node a (y :: c' :: cs))) +
            (Planar.insertSumList cs T₂).map
              (fun cs' => Nonplanar.mk (Planar.node a (y :: x :: cs'))) := by
      rw [Planar.insertSumList_cons, Multiset.map_add, Multiset.map_map,
          Multiset.map_map]
      rfl
    rw [lhs_eq, rhs_eq, lhs_inner, rhs_inner]
    have hAB' : (Planar.insertSum x T₂).map
                  (fun c' => Nonplanar.mk (Planar.node a (c' :: y :: cs))) =
                (Planar.insertSum x T₂).map
                  (fun c' => Nonplanar.mk (Planar.node a (y :: c' :: cs))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_root_perm
      exact List.Perm.swap _ _ _
    have hBA' : (Planar.insertSum y T₂).map
                  (fun c' => Nonplanar.mk (Planar.node a (x :: c' :: cs))) =
                (Planar.insertSum y T₂).map
                  (fun c' => Nonplanar.mk (Planar.node a (c' :: x :: cs))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_root_perm
      exact List.Perm.swap _ _ _
    have hCC' : (Planar.insertSumList cs T₂).map
                  (fun cs' => Nonplanar.mk (Planar.node a (x :: y :: cs'))) =
                (Planar.insertSumList cs T₂).map
                  (fun cs' => Nonplanar.mk (Planar.node a (y :: x :: cs'))) := by
      apply Multiset.map_congr rfl
      intro cs' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_root_perm
      exact List.Perm.swap _ _ _
    rw [hAB', hBA', hCC']
    abel
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## §8: Left invariance — `T₁ → T₁'` via PlanarStep induction -/

private theorem insertSumList_planarStep_at_aux : ∀ (a : α) (T₂ : Planar α)
    (pre : List (Planar α)) (post : List (Planar α)) (old new : Planar α),
    (Planar.insertSum old T₂).map Nonplanar.mk =
      (Planar.insertSum new T₂).map Nonplanar.mk →
    Nonplanar.mk old = Nonplanar.mk new →
    (Planar.insertSumList (pre ++ old :: post) T₂).map
        (fun cs' => (Nonplanar.mk (Planar.node a cs') : Nonplanar α)) =
    (Planar.insertSumList (pre ++ new :: post) T₂).map
        (fun cs' => Nonplanar.mk (Planar.node a cs'))
  | a, T₂, [], post, old, new, ih_sub, h_mk => by
    simp only [List.nil_append]
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · rw [map_node_cons_via_mk a post (M := Planar.insertSum old T₂),
          map_node_cons_via_mk a post (M := Planar.insertSum new T₂),
          ih_sub]
    · apply Multiset.map_congr rfl
      intro cs' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_recurse_lift [] cs'
      exact Nonplanar.mk_eq_mk_iff.mp h_mk
  | a, T₂, p :: pre', post, old, new, ih_sub, h_mk => by
    show (Planar.insertSumList (p :: (pre' ++ old :: post)) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a cs')) =
         (Planar.insertSumList (p :: (pre' ++ new :: post)) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a cs'))
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_recurse_lift (c' :: pre') post
      exact Nonplanar.mk_eq_mk_iff.mp h_mk
    · have ih_tail := insertSumList_planarStep_at_aux a T₂ pre' post old new ih_sub h_mk
      rw [map_node_sibling_cons_via_mk a p
            (M := Planar.insertSumList (pre' ++ old :: post) T₂),
          map_node_sibling_cons_via_mk a p
            (M := Planar.insertSumList (pre' ++ new :: post) T₂),
          ih_tail]

/-- Left invariance for `insertSum` under a single PlanarStep on T₁. -/
theorem insertSum_planarStep_left {T₁ T₁' : Planar α}
    (h : Planar.PlanarStep T₁ T₁') (T₂ : Planar α) :
    (Planar.insertSum T₁ T₂).map Nonplanar.mk =
      (Planar.insertSum T₁' T₂).map Nonplanar.mk := by
  induction h with
  | @swapAtRoot a l r pre post =>
    rw [insertSum_node_proj, insertSum_node_proj]
    congr 1
    · apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_root_perm
      apply List.Perm.cons
      exact List.Perm.append_left pre (List.Perm.swap r l post)
    · have hperm : (pre ++ l :: r :: post).Perm (pre ++ r :: l :: post) :=
        List.Perm.append_left pre (List.Perm.swap r l post)
      exact insertSumList_proj_perm_aux a T₂ hperm
  | @recurse a pre old new post hsub ih =>
    have h_mk : Nonplanar.mk old = Nonplanar.mk new :=
      Nonplanar.mk_eq_mk_iff.mpr (Planar.PlanarEquiv.of_step hsub)
    rw [insertSum_node_proj, insertSum_node_proj]
    congr 1
    · apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_recurse_lift (T₂ :: pre) post
      exact Planar.PlanarEquiv.of_step hsub
    · exact insertSumList_planarStep_at_aux a T₂ pre post old new ih h_mk

/-! ## §9: EqvGen lift to `PlanarEquiv` -/

/-- Left invariance under `PlanarEquiv` on T₁. Standard `EqvGen` recipe. -/
theorem insertSum_planarEquiv_left {T₁ T₁' : Planar α}
    (h : Planar.PlanarEquiv T₁ T₁') (T₂ : Planar α) :
    (Planar.insertSum T₁ T₂).map Nonplanar.mk =
      (Planar.insertSum T₁' T₂).map Nonplanar.mk := by
  induction h with
  | rel _ _ hstep => exact insertSum_planarStep_left hstep T₂
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## §10: Native `Nonplanar.insertSum` via `Quotient.lift₂` -/

/-- The **vertex-grafting pre-Lie product on `Nonplanar α`**: lifted from
    the planar `Planar.insertSum` via `Quotient.lift₂`, using the
    invariance lemmas from §6 and §9. -/
def insertSum : Nonplanar α → Nonplanar α → Multiset (Nonplanar α) :=
  Quotient.lift₂
    (fun (t₁ t₂ : Planar α) => (Planar.insertSum t₁ t₂).map Nonplanar.mk)
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => by
      have step1 : (Planar.insertSum a₁ a₂).map Nonplanar.mk =
                   (Planar.insertSum b₁ a₂).map Nonplanar.mk :=
        insertSum_planarEquiv_left h₁ a₂
      have step2 : (Planar.insertSum b₁ a₂).map Nonplanar.mk =
                   (Planar.insertSum b₁ b₂).map Nonplanar.mk :=
        insertSum_planarEquiv_right b₁ h₂
      exact step1.trans step2)

/-- Notation `T₁ ◁ T₂` for `Nonplanar.insertSum T₁ T₂`. Scoped to the
    `Nonplanar` namespace to coexist with the planar `◁`. -/
scoped infixl:65 " ◁ " => Nonplanar.insertSum

/-! ## §11: Quotient-unfolding lemma + Nonplanar cardinality -/

/-- Quotient unfolding: `Nonplanar.insertSum (mk t₁) (mk t₂)` is the
    multiset of nonplanar grafting summands obtained by projecting the
    planar grafting summands. -/
@[simp] theorem mk_insertSum (t₁ t₂ : Planar α) :
    Nonplanar.insertSum (Nonplanar.mk t₁) (Nonplanar.mk t₂) =
      (Planar.insertSum t₁ t₂).map Nonplanar.mk := rfl

/-- The number of summands of `T₁ ◁ T₂` equals `T₁.weight`, i.e., the
    nonplanar tree-vertex count of T₁. -/
theorem card_insertSum_eq_weight (T₁ T₂ : Nonplanar α) :
    Multiset.card (Nonplanar.insertSum T₁ T₂) = T₁.weight := by
  refine Quotient.inductionOn₂ T₁ T₂ ?_
  intro t₁ t₂
  show Multiset.card ((Planar.insertSum t₁ t₂).map Nonplanar.mk) = (Nonplanar.mk t₁).weight
  rw [Multiset.card_map, Planar.card_insertSum_eq_weight]
  rfl

end Nonplanar

/-! ## §12: Sanity tests at compile time -/

namespace Planar

section Tests

example : (Planar.leaf 1 : Planar Nat) ◁ Planar.leaf 2
    = ({Planar.node 1 [Planar.leaf 2]} : Multiset (Planar Nat)) := by
  rw [insertSum_leaf]

/-- A binary tree has 3 vertices, hence 3 grafting summands. -/
example : Multiset.card
    ((Planar.binary 1 (Planar.leaf 2) (Planar.leaf 3) : Planar Nat) ◁
      Planar.leaf 4) = 3 := by
  rw [card_insertSum_eq_weight]
  show (Planar.binary 1 (Planar.leaf 2) (Planar.leaf 3) : Planar Nat).weight = 3
  unfold Planar.binary Planar.leaf weight weightList; rfl

/-- The grafting decomposition: each summand corresponds to a vertex. -/
example (T₁ T₂ : Planar Nat) :
    Multiset.card (T₁ ◁ T₂) = (vertices T₁).length :=
  card_insertSum_eq_length_vertices T₁ T₂

end Tests

end Planar

namespace Nonplanar

section Tests

variable {α : Type*}

/-- A leaf grafted onto a leaf gives the canonical 1-vertex grafting summand. -/
example : Nonplanar.insertSum (Nonplanar.leaf 1 : Nonplanar Nat) (Nonplanar.leaf 2)
    = ({Nonplanar.mk (Planar.node 1 [Planar.leaf 2])} : Multiset (Nonplanar Nat)) := by
  show (Planar.insertSum (Planar.leaf 1) (Planar.leaf 2)).map Nonplanar.mk = _
  rw [Planar.insertSum_leaf, Multiset.map_singleton]

/-- A nonplanar binary tree has 3 vertices, hence 3 grafting summands. -/
example : Multiset.card
    (Nonplanar.insertSum
      (Nonplanar.mk (Planar.binary 1 (Planar.leaf 2) (Planar.leaf 3)))
      (Nonplanar.leaf 4 : Nonplanar Nat)) = 3 := by
  rw [card_insertSum_eq_weight]
  show (Nonplanar.mk (Planar.binary 1 (Planar.leaf 2) (Planar.leaf 3))).weight = 3
  show (Planar.binary 1 (Planar.leaf 2) (Planar.leaf 3) : Planar Nat).weight = 3
  unfold Planar.binary Planar.leaf Planar.weight Planar.weightList; rfl

end Tests

end Nonplanar

end RootedTree
