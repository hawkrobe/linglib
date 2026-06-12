/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
import Linglib.Core.Combinatorics.RootedTree.Nonplanar
import Mathlib.Data.Multiset.Basic

set_option autoImplicit false

/-!
# Nonplanar multi-tree insertion

Lift of `Planar.Pathed.insertionForest` through `Nonplanar.mk`.

Given two multisets of nonplanar trees `F` (host forest) and `G` (guest
forest), `Nonplanar.insertionMultiset F G` produces the multiset of all
forests obtained by inserting `G`'s trees at vertices of `F`'s trees,
summing over all assignments (Foissy 2021 Theorem 5.1).

## Implementation note

The implementation uses `Multiset.toList` + `Quotient.out` to pick
representatives, making it `noncomputable`. The function value is
nonetheless well-defined (classical choice yields a definite element).
Stronger invariance theorems (host-Perm invariance lifted to the
multiset-output level) would enable a `Quotient.liftOn₂`-based definition
but are deferred — the current API suffices for the GrossmanLarson
product's zero-case lemmas.

## Import-direction anomaly

This file lives under `Combinatorics/` but imports
`Linglib.Core.Algebra.RootedTree.PreLie.Insertion`. The anomaly is
temporary: the path-based `Insertion.lean` is planned to migrate to
`Combinatorics/RootedTree/Planar/Insertion.lean`, after which the
imports become hierarchical.
-/

namespace RootedTree

namespace Nonplanar

variable {α : Type*}

/-- Multi-tree insertion at the nonplanar level. Given a host forest
    `F` and guest forest `G` (both `Multiset (Nonplanar α)`), produces
    the multiset of all forests obtained by inserting `G`'s trees at
    vertices of `F`'s trees. Defined via list representatives
    (`Multiset.toList`) + planar representatives (`Quotient.out`) +
    `Planar.Pathed.insertionForest`. -/
noncomputable def insertionMultiset (F G : Multiset (Nonplanar α)) :
    Multiset (Multiset (Nonplanar α)) :=
  let host_planar : List (Planar α) := F.toList.map Quotient.out
  let guest_planar : List (Planar α) := G.toList.map Quotient.out
  (Planar.Pathed.insertionForest host_planar guest_planar).map
    fun L => Multiset.ofList (L.map Nonplanar.mk)

/-- With no guests, the multi-graft leaves `F` unchanged:
    `insertionMultiset F 0 = {F}`. -/
theorem insertionMultiset_zero_right (F : Multiset (Nonplanar α)) :
    insertionMultiset F 0 = ({F} : Multiset (Multiset (Nonplanar α))) := by
  unfold insertionMultiset
  rw [Multiset.toList_zero]
  show (Planar.Pathed.insertionForest (F.toList.map Quotient.out) []).map
        (fun L => (Multiset.ofList (L.map Nonplanar.mk) :
                    Multiset (Nonplanar α))) = ({F} : Multiset _)
  rw [Planar.Pathed.insertionForest_nil_guests, Multiset.map_singleton]
  congr 1
  have h_map_id : (F.toList.map Quotient.out).map Nonplanar.mk = F.toList := by
    induction F.toList with
    | nil => rfl
    | cons hd tl ih =>
      show Nonplanar.mk (Quotient.out hd) :: ((tl.map Quotient.out).map Nonplanar.mk) =
           hd :: tl
      rw [ih]
      congr 1
      exact hd.out_eq
  rw [h_map_id]
  exact F.coe_toList

/-- With no host but non-empty guests, no vertices to graft into:
    `insertionMultiset 0 G = 0`. -/
theorem insertionMultiset_zero_left_of_ne_zero (G : Multiset (Nonplanar α))
    (h : G ≠ 0) :
    insertionMultiset 0 G = 0 := by
  unfold insertionMultiset
  rw [Multiset.toList_zero]
  have h_toList : G.toList ≠ [] := fun h_eq => h (Multiset.toList_eq_nil.mp h_eq)
  rcases hg : G.toList with _ | ⟨g, gs⟩
  · exact absurd hg h_toList
  · show (Planar.Pathed.insertionForest [] (Quotient.out g :: gs.map Quotient.out)).map _ = 0
    rw [Planar.Pathed.insertionForest_empty_host_nonempty_guests, Multiset.map_zero]

/-! ## §2: toList helpers

Multiset's `toList` returns a non-canonical list representative. Two
different choices of representative produce `Perm`-equivalent lists.
Below: a Perm bridge between `(M + N).toList` and `M.toList ++ N.toList`,
and its `Q.out`-mapped lift to the planar level. Used by
`insertionMultiset_add_host` to bridge `(A + B).toList.map Q.out` with the
disjoint-host concatenation `A.toList.map Q.out ++ B.toList.map Q.out`. -/

/-- `(M + N).toList` is `Perm`-equivalent to `M.toList ++ N.toList`. Both
    have multiset `M + N`; `Perm` follows from `Multiset.coe_eq_coe`.

    `[UPSTREAM]` candidate: pure `Multiset` substrate, no rooted-tree
    dependencies. Belongs in mathlib's `Mathlib.Data.Multiset.Basic`
    alongside `Multiset.coe_toList` and `Multiset.coe_add`. -/
theorem _root_.Multiset.toList_add_perm {β : Type*} (M N : Multiset β) :
    (M + N).toList.Perm (M.toList ++ N.toList) := by
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.coe_toList, ← Multiset.coe_add, Multiset.coe_toList,
      Multiset.coe_toList]

/-- `Quotient.out`-mapped lift of `Multiset.toList_add_perm`: at the Planar
    level, `(M + N).toList.map Quotient.out` is Perm to
    `M.toList.map Quotient.out ++ N.toList.map Quotient.out`. -/
theorem toList_map_quotientOut_add_perm (M N : Multiset (Nonplanar α)) :
    ((M + N).toList.map Quotient.out).Perm
      (M.toList.map Quotient.out ++ N.toList.map Quotient.out) := by
  rw [← List.map_append]
  exact (Multiset.toList_add_perm M N).map _

/-- Planar substrate for `insertionMultiset_card_eq`: every output list in
    `insertionForest host guests` has length equal to the host length.
    `insertionForest` produces `T' :: F'` lists by recursion on the host;
    each step prepends one tree and recurses on the tail. -/
private theorem _root_.RootedTree.Planar.Pathed.insertionForest_length
    {α : Type*} :
    ∀ (host guests : List (Planar α)) {L : List (Planar α)},
      L ∈ Planar.Pathed.insertionForest host guests → L.length = host.length
  | [],     [],         L, hL => by
    rw [Planar.Pathed.insertionForest_nil_nil] at hL
    rw [Multiset.mem_singleton.mp hL]
  | [],     _ :: _,     L, hL => by
    rw [Planar.Pathed.insertionForest_empty_host_nonempty_guests] at hL
    exact absurd hL (Multiset.notMem_zero L)
  | T :: F, [],         L, hL => by
    rw [Planar.Pathed.insertionForest_cons_host_nil_guests] at hL
    rw [Multiset.mem_singleton.mp hL]
  | T :: F, T_g :: Ts,  L, hL => by
    rw [Planar.Pathed.insertionForest_cons_cons] at hL
    -- L ∈ bind of bind of map; unfold mem step by step.
    rw [Multiset.mem_bind] at hL
    obtain ⟨assignment, _hass, hL⟩ := hL
    rw [Multiset.mem_bind] at hL
    obtain ⟨T', _hT', hL⟩ := hL
    rw [Multiset.mem_map] at hL
    obtain ⟨F', hF'mem, hL_eq⟩ := hL
    -- L = T' :: F', with F' from the inner insertionForest F (sub-guests).
    have hF'len : F'.length = F.length :=
      Planar.Pathed.insertionForest_length F _ hF'mem
    rw [← hL_eq, List.length_cons, hF'len, List.length_cons]
  termination_by host _ => host.length

/-- The insertion multiset preserves cardinality: every forest in
    `insertionMultiset A B` has the same cardinality as `A`.

    Proof: `insertionMultiset A B` is built from
    `insertionForest (A.toList.map Q.out) (B.toList.map Q.out)`; every
    output list `L` has `L.length = (A.toList.map Q.out).length = A.card`
    (via `Planar.Pathed.insertionForest_length`); and the cardinality of
    the lifted `Multiset.ofList (L.map mk)` equals `L.length`. -/
theorem insertionMultiset_card_eq {α : Type*} (A B : Multiset (Nonplanar α))
    {F' : Multiset (Nonplanar α)} (hF' : F' ∈ insertionMultiset A B) :
    F'.card = A.card := by
  unfold insertionMultiset at hF'
  rw [Multiset.mem_map] at hF'
  obtain ⟨L, hL_mem, hL_eq⟩ := hF'
  have hLlen : L.length = (A.toList.map Quotient.out).length :=
    Planar.Pathed.insertionForest_length _ _ hL_mem
  rw [← hL_eq]
  -- F'.card = (Multiset.ofList (L.map mk)).card = (L.map mk).length = L.length.
  show (Multiset.ofList (L.map Nonplanar.mk)).card = A.card
  rw [Multiset.coe_card, List.length_map, hLlen, List.length_map]
  exact Multiset.length_toList A

/-! ## §3: Root-label preservation for singleton hosts

When the host forest is a single tree `{T}`, every output forest of
`insertionMultiset {T} B` is a singleton `{T'}` and `T'.rootLabel =
T.rootLabel`: grafting guests into a tree only modifies its subtrees,
never its root label.

The proof descends through the planar substrate using
`Planar.Pathed.insertionForest_singleton` and `multiGraft_node` (which
preserves the head label by structure). -/

/-- **Planar root preservation**: `Planar.label (multiGraft T pairs) =
    Planar.label T`. Follows directly from `multiGraft_node`, which
    rebuilds the root with the same label `a`. -/
private theorem _root_.RootedTree.Planar.label_multiGraft
    (T : Planar α) (pairs : List (Planar.Pathed.Path × Planar α)) :
    (Planar.Pathed.multiGraft T pairs).label = T.label := by
  cases T with
  | node a cs => rw [Planar.Pathed.multiGraft_node, Planar.label_node, Planar.label_node]

/-- **Singleton-host root preservation**: every forest in
    `insertionMultiset {T} B` is a singleton `{T'}` and `T'.rootLabel =
    T.rootLabel`. Descends through `insertionForest_singleton` +
    `Planar.label_multiGraft`. -/
theorem insertionMultiset_singleton_rootLabel
    (T : Nonplanar α) (B : Multiset (Nonplanar α))
    {F' : Multiset (Nonplanar α)} (hF' : F' ∈ insertionMultiset {T} B) :
    ∃ T' : Nonplanar α, F' = ({T'} : Multiset (Nonplanar α)) ∧
      T'.rootLabel = T.rootLabel := by
  unfold insertionMultiset at hF'
  rw [Multiset.mem_map] at hF'
  obtain ⟨L, hL_mem, hL_eq⟩ := hF'
  -- ({T} : Multiset _).toList = [T] via `Multiset.toList_singleton`.
  have h_toList : ({T} : Multiset (Nonplanar α)).toList.map Quotient.out =
      [Quotient.out T] := by
    rw [Multiset.toList_singleton]; rfl
  rw [h_toList] at hL_mem
  -- Use `insertionForest_singleton`.
  rw [Planar.Pathed.insertionForest_singleton] at hL_mem
  rw [Multiset.mem_map] at hL_mem
  obtain ⟨T'_pl, hT'_pl_mem, hT'_pl_eq⟩ := hL_mem
  -- T'_pl ∈ insertion (Q.out T) gs, so T'_pl = multiGraft (Q.out T) (choice.zip gs)
  -- for some choice. Hence label T'_pl = label (Q.out T) = T.rootLabel.
  refine ⟨Nonplanar.mk T'_pl, ?_, ?_⟩
  · -- F' = {Nonplanar.mk T'_pl}: L = [T'_pl], so F' = ofList [mk T'_pl] = {mk T'_pl}.
    rw [← hL_eq, ← hT'_pl_eq]
    show (Multiset.ofList (([T'_pl] : List (Planar α)).map Nonplanar.mk) :
            Multiset (Nonplanar α)) = {Nonplanar.mk T'_pl}
    rfl
  · -- Root label preservation through the planar substrate.
    -- T'_pl ∈ insertion T.out (...): T'_pl = multiGraft T.out pairs for some pairs.
    rw [Nonplanar.rootLabel_mk]
    -- Unfold `insertion` to extract the choice and reduce label-equality.
    rw [Planar.Pathed.insertion_def, Multiset.mem_coe, List.mem_map] at hT'_pl_mem
    obtain ⟨choice, _hchoice_mem, hchoice_eq⟩ := hT'_pl_mem
    rw [← hchoice_eq]
    -- Now: label (multiGraft T.out (choice.zip ...)) = T.rootLabel
    rw [Planar.label_multiGraft]
    -- label T.out = rootLabel T via `rootLabel_mk T.out_eq`.
    -- (Quotient.out T).label = (mk (Quotient.out T)).rootLabel by `rootLabel_mk`;
    -- mk (Quotient.out T) = T by `T.out_eq`.
    show (Quotient.out T).label = T.rootLabel
    have h_eq : Nonplanar.mk (Quotient.out T) = T := T.out_eq
    calc (Quotient.out T).label
        = (Nonplanar.mk (Quotient.out T)).rootLabel := (Nonplanar.rootLabel_mk _).symm
      _ = T.rootLabel := by rw [h_eq]

end Nonplanar

end RootedTree
