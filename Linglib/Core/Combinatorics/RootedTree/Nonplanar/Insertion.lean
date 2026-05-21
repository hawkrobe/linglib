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

/-! ## §1.5: Cardinality preservation

NIM grafts guest-trees into host-vertices; no host trees are created or
destroyed. Hence every output forest has the same cardinality as the host. -/

/-- **Planar**: every list `L ∈ insertionForest hosts guests` has
    `L.length = hosts.length`. Structural induction on hosts/guests. -/
theorem _root_.RootedTree.Planar.Pathed.insertionForest_length
    {α : Type*} (hosts guests : List (Planar α))
    {L : List (Planar α)}
    (h : L ∈ Planar.Pathed.insertionForest hosts guests) :
    L.length = hosts.length := by
  induction hosts generalizing guests L with
  | nil =>
    cases guests with
    | nil =>
      rw [Planar.Pathed.insertionForest_nil_nil] at h
      have : L = [] := Multiset.mem_singleton.mp h
      simp [this]
    | cons _ _ =>
      rw [Planar.Pathed.insertionForest_empty_host_nonempty_guests] at h
      exact absurd h (by simp)
  | cons T F ih =>
    cases guests with
    | nil =>
      rw [Planar.Pathed.insertionForest_cons_host_nil_guests] at h
      have : L = T :: F := Multiset.mem_singleton.mp h
      simp [this]
    | cons Tg Ts =>
      rw [Planar.Pathed.insertionForest_cons_cons] at h
      rw [Multiset.mem_bind] at h
      obtain ⟨_assn, _hassn, h2⟩ := h
      rw [Multiset.mem_bind] at h2
      obtain ⟨T', _hT', h3⟩ := h2
      rw [Multiset.mem_map] at h3
      obtain ⟨F', hF', hLeq⟩ := h3
      have hF'len : F'.length = F.length := ih _ hF'
      rw [← hLeq]
      show (T' :: F').length = (T :: F).length
      simp [hF'len]

/-- **Cardinality preservation**: every `F' ∈ NIM(A, B)` has `|F'| = |A|`.
    Lifts `Planar.Pathed.insertionForest_length` through `Nonplanar.mk`. -/
theorem insertionMultiset_card_eq (A B : Multiset (Nonplanar α))
    {F' : Multiset (Nonplanar α)} (h : F' ∈ insertionMultiset A B) :
    F'.card = A.card := by
  unfold insertionMultiset at h
  rw [Multiset.mem_map] at h
  obtain ⟨L, hL, hF'_eq⟩ := h
  have hLlen : L.length = A.toList.length := by
    have h_hosts_len : (A.toList.map Quotient.out).length = A.toList.length :=
      List.length_map _
    rw [← h_hosts_len]
    exact Planar.Pathed.insertionForest_length _ _ hL
  rw [← hF'_eq]
  show ((Multiset.ofList (L.map Nonplanar.mk)) : Multiset (Nonplanar α)).card =
      A.card
  rw [Multiset.coe_card, List.length_map, hLlen, Multiset.length_toList]

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

end Nonplanar

end RootedTree
