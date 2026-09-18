/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
import Linglib.Core.Data.List.Zip
import Linglib.Core.Data.Multiset.Antidiagonal
import Linglib.Core.Data.UnorderedTree.DecEq
import Linglib.Core.Data.UnorderedTree.Basic
import Mathlib.Data.Multiset.Basic

open RoseTree UnorderedTree

/-!
# UnorderedTree multi-tree insertion

Lift of `RoseTree.Pathed.insertionForest` through `UnorderedTree.mk`.

Given two multisets of nonplanar trees `F` (host forest) and `G` (guest
forest), `UnorderedTree.insertionMultiset F G` produces the multiset of all
forests obtained by inserting `G`'s trees at vertices of `F`'s trees,
summing over all assignments (Foissy 2021 Theorem 5.1).

## Main results

* `UnorderedTree.insertionMultiset_add_host`: multi-graft into a
  disjoint-union host decomposes over guest partitions
  ([oudom-guin-2008] Prop 2.7.iii substrate).
* `UnorderedTree.insertionMultiset_antidiagonal`: splits of a multi-graft
  output factor through splits of host and guests.

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
`Linglib.Core.Algebra.RootedTree.PreLie.Insertion` (the path-based
single/forest insertion operators). The path apparatus currently lives in
the Algebra leg; were it to graduate to `Combinatorics/`, the imports
would become strictly hierarchical.
-/


namespace UnorderedTree
variable {α : Type*}

/-- Multi-tree insertion at the nonplanar level. Given a host forest
    `F` and guest forest `G` (both `Multiset (UnorderedTree α)`), produces
    the multiset of all forests obtained by inserting `G`'s trees at
    vertices of `F`'s trees. Defined via list representatives
    (`Multiset.toList`) + tree representatives (`Quotient.out`) +
    `RoseTree.Pathed.insertionForest`. -/
noncomputable def insertionMultiset (F G : Multiset (UnorderedTree α)) :
    Multiset (Multiset (UnorderedTree α)) :=
  let hostTrees : List (RoseTree α) := F.toList.map Quotient.out
  let guestTrees : List (RoseTree α) := G.toList.map Quotient.out
  (RoseTree.Pathed.insertionForest hostTrees guestTrees).map
    fun L => Multiset.ofList (L.map UnorderedTree.mk)

/-- With no guests, the multi-graft leaves `F` unchanged:
    `insertionMultiset F 0 = {F}`. -/
theorem insertionMultiset_zero_right (F : Multiset (UnorderedTree α)) :
    insertionMultiset F 0 = ({F} : Multiset (Multiset (UnorderedTree α))) := by
  unfold insertionMultiset
  rw [Multiset.toList_zero]
  show (RoseTree.Pathed.insertionForest (F.toList.map Quotient.out) []).map
        (fun L => (Multiset.ofList (L.map UnorderedTree.mk) :
                    Multiset (UnorderedTree α))) = ({F} : Multiset _)
  rw [RoseTree.Pathed.insertionForest_nil_guests, Multiset.map_singleton]
  congr 1
  have h_map_id : (F.toList.map Quotient.out).map UnorderedTree.mk = F.toList := by
    induction F.toList with
    | nil => rfl
    | cons hd tl ih =>
      show UnorderedTree.mk (Quotient.out hd) :: ((tl.map Quotient.out).map UnorderedTree.mk) =
           hd :: tl
      rw [ih]
      congr 1
      exact hd.out_eq
  rw [h_map_id]
  exact F.coe_toList

/-- With no host but non-empty guests, no vertices to graft into:
    `insertionMultiset 0 G = 0`. -/
theorem insertionMultiset_zero_left_of_ne_zero (G : Multiset (UnorderedTree α))
    (h : G ≠ 0) :
    insertionMultiset 0 G = 0 := by
  unfold insertionMultiset
  rw [Multiset.toList_zero]
  have h_toList : G.toList ≠ [] := fun h_eq => h (Multiset.toList_eq_nil.mp h_eq)
  rcases hg : G.toList with _ | ⟨g, gs⟩
  · exact absurd hg h_toList
  · show (RoseTree.Pathed.insertionForest [] (Quotient.out g :: gs.map Quotient.out)).map _ = 0
    rw [RoseTree.Pathed.insertionForest_empty_host_nonempty_guests, Multiset.map_zero]

/-- One host and one guest: the multi-insertion is the pre-Lie product, each output a
    singleton forest. -/
theorem insertionMultiset_singleton_singleton (T g : UnorderedTree α) :
    insertionMultiset {T} {g} =
      (UnorderedTree.insertSum T g).map fun S => ({S} : Multiset (UnorderedTree α)) := by
  have h : UnorderedTree.insertSum T g =
      (RoseTree.insertSum (Quotient.out T) (Quotient.out g)).map UnorderedTree.mk := by
    rw [← mk_insertSum]
    exact (congrArg₂ _ T.out_eq g.out_eq).symm
  unfold insertionMultiset
  dsimp only
  rw [Multiset.toList_singleton, Multiset.toList_singleton, List.map_singleton,
    List.map_singleton, RoseTree.Pathed.insertionForest_singleton,
    RoseTree.Pathed.insertion_singleton, h, Multiset.map_map, Multiset.map_map]
  rfl

/-! ## §2: toList helpers

Multiset's `toList` returns a non-canonical list representative. Two
different choices of representative produce `Perm`-equivalent lists.
Below: a Perm bridge between `(M + N).toList` and `M.toList ++ N.toList`,
and its `Q.out`-mapped lift to the tree level. Used by
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

/-- `Quotient.out`-mapped lift of `Multiset.toList_add_perm`: at the tree
    level, `(M + N).toList.map Quotient.out` is Perm to
    `M.toList.map Quotient.out ++ N.toList.map Quotient.out`. -/
theorem toList_map_quotientOut_add_perm (M N : Multiset (UnorderedTree α)) :
    ((M + N).toList.map Quotient.out).Perm
      (M.toList.map Quotient.out ++ N.toList.map Quotient.out) := by
  rw [← List.map_append]
  exact (Multiset.toList_add_perm M N).map _

/-- Every output list of `insertionForest host guests` has the host's length. -/
private theorem _root_.RoseTree.Pathed.insertionForest_length {α : Type*}
    (host guests : List (RoseTree α)) {L : List (RoseTree α)}
    (hL : L ∈ RoseTree.Pathed.insertionForest host guests) : L.length = host.length := by
  rw [RoseTree.Pathed.insertionForest_def, Multiset.mem_coe, List.mem_map] at hL
  obtain ⟨ch, -, rfl⟩ := hL
  exact RoseTree.Pathed.multiGraftChildren_length host _

/-- The insertion multiset preserves cardinality: every forest in
    `insertionMultiset A B` has the same cardinality as `A`.

    Proof: `insertionMultiset A B` is built from
    `insertionForest (A.toList.map Q.out) (B.toList.map Q.out)`; every
    output list `L` has `L.length = (A.toList.map Q.out).length = A.card`
    (via `RoseTree.Pathed.insertionForest_length`); and the cardinality of
    the lifted `Multiset.ofList (L.map mk)` equals `L.length`. -/
theorem insertionMultiset_card_eq {α : Type*} (A B : Multiset (UnorderedTree α))
    {F' : Multiset (UnorderedTree α)} (hF' : F' ∈ insertionMultiset A B) :
    F'.card = A.card := by
  unfold insertionMultiset at hF'
  rw [Multiset.mem_map] at hF'
  obtain ⟨L, hL_mem, hL_eq⟩ := hF'
  have hLlen : L.length = (A.toList.map Quotient.out).length :=
    RoseTree.Pathed.insertionForest_length _ _ hL_mem
  rw [← hL_eq]
  -- F'.card = (Multiset.ofList (L.map mk)).card = (L.map mk).length = L.length.
  show (Multiset.ofList (L.map UnorderedTree.mk)).card = A.card
  rw [Multiset.coe_card, List.length_map, hLlen, List.length_map]
  exact Multiset.length_toList A

/-! ## §3: Root-value preservation for singleton hosts

When the host forest is a single tree `{T}`, every output forest of
`insertionMultiset {T} B` is a singleton `{T'}` and `T'.value =
T.value`: grafting guests into a tree only modifies its subtrees,
never its root value.

The proof descends through the tree substrate using
`RoseTree.Pathed.insertionForest_singleton` and `multiGraft_node` (which
preserves the head value by structure). -/

/-- **Root-value preservation**: `RoseTree.value (multiGraft T pairs) =
    RoseTree.value T`. Follows directly from `multiGraft_node`, which
    rebuilds the root with the same value `a`. -/
private theorem _root_.RoseTree.value_multiGraft
    (T : RoseTree α) (pairs : List (RoseTree.Pathed.Path × RoseTree α)) :
    (RoseTree.Pathed.multiGraft T pairs).value = T.value := by
  cases T with
  | node a cs => rw [RoseTree.Pathed.multiGraft_node, RoseTree.value_node, RoseTree.value_node]

/-- **Singleton-host root preservation**: every forest in
    `insertionMultiset {T} B` is a singleton `{T'}` and `T'.value =
    T.value`. Descends through `insertionForest_singleton` +
    `RoseTree.value_multiGraft`. -/
theorem insertionMultiset_singleton_value
    (T : UnorderedTree α) (B : Multiset (UnorderedTree α))
    {F' : Multiset (UnorderedTree α)} (hF' : F' ∈ insertionMultiset {T} B) :
    ∃ T' : UnorderedTree α, F' = ({T'} : Multiset (UnorderedTree α)) ∧
      T'.value = T.value := by
  unfold insertionMultiset at hF'
  rw [Multiset.mem_map] at hF'
  obtain ⟨L, hL_mem, hL_eq⟩ := hF'
  -- ({T} : Multiset _).toList = [T] via `Multiset.toList_singleton`.
  have h_toList : ({T} : Multiset (UnorderedTree α)).toList.map Quotient.out =
      [Quotient.out T] := by
    rw [Multiset.toList_singleton]; rfl
  rw [h_toList] at hL_mem
  -- Use `insertionForest_singleton`.
  rw [RoseTree.Pathed.insertionForest_singleton] at hL_mem
  rw [Multiset.mem_map] at hL_mem
  obtain ⟨T'_tr, hT'_tr_mem, hT'_tr_eq⟩ := hL_mem
  -- T'_tr ∈ insertion (Q.out T) gs, so T'_tr = multiGraft (Q.out T) (choice.zip gs)
  -- for some choice. Hence value T'_tr = value (Q.out T) = T.value.
  refine ⟨UnorderedTree.mk T'_tr, ?_, ?_⟩
  · -- F' = {UnorderedTree.mk T'_tr}: L = [T'_tr], so F' = ofList [mk T'_tr] = {mk T'_tr}.
    rw [← hL_eq, ← hT'_tr_eq]
    show (Multiset.ofList (([T'_tr] : List (RoseTree α)).map UnorderedTree.mk) :
            Multiset (UnorderedTree α)) = {UnorderedTree.mk T'_tr}
    rfl
  · -- Root value preservation through the tree substrate.
    -- T'_tr ∈ insertion T.out (...): T'_tr = multiGraft T.out pairs for some pairs.
    rw [UnorderedTree.value_mk]
    -- Unfold `insertion` to extract the choice and reduce value-equality.
    rw [RoseTree.Pathed.insertion_def, Multiset.mem_coe, List.mem_map] at hT'_tr_mem
    obtain ⟨choice, _hchoice_mem, hchoice_eq⟩ := hT'_tr_mem
    rw [← hchoice_eq]
    -- Now: value (multiGraft T.out (choice.zip ...)) = T.value
    rw [RoseTree.value_multiGraft]
    -- value T.out = value T via `value_mk T.out_eq`.
    -- (Quotient.out T).value = (mk (Quotient.out T)).value by `value_mk`;
    -- mk (Quotient.out T) = T by `T.out_eq`.
    show (Quotient.out T).value = T.value
    have h_eq : UnorderedTree.mk (Quotient.out T) = T := T.out_eq
    calc (Quotient.out T).value
        = (UnorderedTree.mk (Quotient.out T)).value := (UnorderedTree.value_mk _).symm
      _ = T.value := by rw [h_eq]


/-! ### Insertion into a singleton node host -/

/-- `Multiset.bind` as a mapped sum (`join` is definitionally `sum`). -/
private theorem bind_eq_map_sum {γ δ : Type*} (s : Multiset γ)
    (f : γ → Multiset δ) : s.bind f = (s.map f).sum := rfl

/-- **NIM-level keystone**: grafting `B` into the singleton host `{node a A'}` decomposes by
    which guests are grafted at the root (new children) and which into `A'`'s trees (a
    recursive NIM).

    Descent through the quotient: the host's canonical planar representative is
    `Perm`-swapped for a visible planar node, `RoseTree.Pathed.insertion_node` splits the
    planar guests as `sublists'.revzip`, and `Multiset.coe_revzip_sublists'` carries that
    split to the powerset bind. -/
theorem insertionMultiset_singleton_node [DecidableEq α]
    (a : α) (A' B : Multiset (UnorderedTree α)) :
    UnorderedTree.insertionMultiset
        ({UnorderedTree.node a A'} : Multiset (UnorderedTree α)) B =
      (B.powerset.bind fun B₁ =>
         (UnorderedTree.insertionMultiset A' B₁).map fun F' =>
           ({UnorderedTree.node a (F' + (B - B₁))} : Multiset (UnorderedTree α))) := by
  -- §1: the canonical planar representative of the host is equivalent to
  -- the visible node on A''s canonical children list.
  have h_mk2 : UnorderedTree.mk (RoseTree.node a (A'.toList.map Quotient.out)) =
      UnorderedTree.node a A' := by
    rw [← UnorderedTree.node_mk_tree_list]
    congr 1
    rw [List.map_map,
        show A'.toList.map (UnorderedTree.mk ∘ Quotient.out) = A'.toList from
          (List.map_congr_left fun x _ => Quotient.out_eq x).trans
            (List.map_id _)]
    exact A'.coe_toList
  have h_equiv : RoseTree.Perm
      (Quotient.out (UnorderedTree.node a A'))
      (RoseTree.node a (A'.toList.map Quotient.out)) :=
    UnorderedTree.mk_eq_mk_iff.mp
      (((UnorderedTree.node a A').out_eq).trans h_mk2.symm)
  -- §2: unfold NIM; the host list is the singleton of the canonical rep.
  unfold UnorderedTree.insertionMultiset
  rw [show (({UnorderedTree.node a A'} : Multiset (UnorderedTree α)).toList.map
        Quotient.out : List (RoseTree α))
      = [Quotient.out (UnorderedTree.node a A')] from by
    rw [Multiset.toList_singleton]
    rfl]
  -- §3: swap the host representative under the msform map.
  rw [RoseTree.Pathed.insertionForest_permList_host_msform
    (RoseTree.PermList.of_forall₂ (List.Forall₂.cons h_equiv List.Forall₂.nil)) _]
  -- §4: singleton-forest reduction + the node split, over `sublists'.revzip` of `B.toList`.
  rw [RoseTree.Pathed.insertionForest_singleton, Multiset.map_map,
    RoseTree.Pathed.insertion_node, Multiset.map_bind, List.sublists'_map, List.revzip_map,
    ← Multiset.map_coe, Multiset.bind_map]
  -- §5: the powerset bind as a bind over `sublists'.revzip`, root bucket first.
  have h_rhs : (B.powerset.bind fun B₁ =>
        (UnorderedTree.insertionMultiset A' B₁).map fun F' =>
          ({UnorderedTree.node a (F' + (B - B₁))} : Multiset (UnorderedTree α))) =
      (B.toList.sublists'.revzip :
          Multiset (List (UnorderedTree α) × List (UnorderedTree α))).bind fun p =>
        (UnorderedTree.insertionMultiset A' ↑p.2).map fun F' =>
          ({UnorderedTree.node a (F' + ↑p.1)} : Multiset (UnorderedTree α)) := by
    have h := Multiset.coe_revzip_sublists' B.toList
    rw [Multiset.coe_toList] at h
    calc _ = (B.powerset.map fun s => (s, B - s)).bind fun q =>
            (UnorderedTree.insertionMultiset A' q.2).map fun F' =>
              ({UnorderedTree.node a (F' + q.1)} : Multiset (UnorderedTree α)) := by
          rw [Multiset.bind_map, bind_eq_map_sum, bind_eq_map_sum]
          exact Multiset.powerset_partition_swap B fun B₁ rest =>
            (UnorderedTree.insertionMultiset A' B₁).map fun F' =>
              ({UnorderedTree.node a (F' + rest)} : Multiset (UnorderedTree α))
      _ = _ := by rw [← h, ← Multiset.map_coe, Multiset.bind_map]
  refine Eq.trans ?_ h_rhs.symm
  -- §6: per guest split, the planar buckets are `Quotient.out` images of the nonplanar ones.
  refine Multiset.bind_congr fun (p : List (UnorderedTree α) × List (UnorderedTree α)) _ => ?_
  dsimp only [Prod.map_fst, Prod.map_snd]
  have h_out : ∀ l : List (UnorderedTree α), (l.map Quotient.out).map UnorderedTree.mk = l :=
    fun l => by
      rw [List.map_map]
      exact (List.map_congr_left fun x _ => Quotient.out_eq x).trans (List.map_id _)
  have h_guests := RoseTree.Pathed.insertionForest_msform_invariance_guests
    (A'.toList.map Quotient.out) (gs1 := p.2.map Quotient.out)
    (gs2 := (↑p.2 : Multiset (UnorderedTree α)).toList.map Quotient.out)
    (Multiset.coe_eq_coe.mp (by rw [h_out, h_out, Multiset.coe_toList]))
  rw [Multiset.map_map]
  calc (RoseTree.Pathed.insertionForest (A'.toList.map Quotient.out) (p.2.map Quotient.out)).map
        ((((fun L => (Multiset.ofList (L.map UnorderedTree.mk) :
            Multiset (UnorderedTree α))) ∘ fun T' => [T']))
          ∘ (fun cs' => RoseTree.node a (p.1.map Quotient.out ++ cs')))
      = ((RoseTree.Pathed.insertionForest (A'.toList.map Quotient.out)
            (p.2.map Quotient.out)).map
          (fun L => (Multiset.ofList (L.map UnorderedTree.mk) :
            Multiset (UnorderedTree α)))).map
        (fun M => ({UnorderedTree.node a (↑p.1 + M)} : Multiset (UnorderedTree α))) := by
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl fun cs' _ => ?_
        show ({UnorderedTree.mk (RoseTree.node a (p.1.map Quotient.out ++ cs'))} :
          Multiset (UnorderedTree α)) = _
        rw [← UnorderedTree.node_mk_tree_list, List.map_append, ← Multiset.coe_add, h_out]
        rfl
    _ = ((RoseTree.Pathed.insertionForest (A'.toList.map Quotient.out)
            ((↑p.2 : Multiset (UnorderedTree α)).toList.map Quotient.out)).map
          (fun L => (Multiset.ofList (L.map UnorderedTree.mk) :
            Multiset (UnorderedTree α)))).map
        (fun M => ({UnorderedTree.node a (↑p.1 + M)} : Multiset (UnorderedTree α))) := by
        rw [h_guests]
    _ = (UnorderedTree.insertionMultiset A' ↑p.2).map
        (fun F' => ({UnorderedTree.node a (F' + ↑p.1)} : Multiset (UnorderedTree α))) := by
        unfold UnorderedTree.insertionMultiset
        rw [Multiset.map_map, Multiset.map_map]
        refine Multiset.map_congr rfl fun L _ => ?_
        show ({UnorderedTree.node a (↑p.1 + Multiset.ofList (L.map UnorderedTree.mk))} :
          Multiset (UnorderedTree α)) = _
        rw [add_comm]
        rfl


/-! ### Disjoint-union hosts, representatives, and iterated grafting

Multi-graft into a disjoint-union host decomposes over guest partitions
(the combinatorial heart of [oudom-guin-2008] Prop 2.7.iii);
`insertionMultiset` computes on arbitrary `RoseTree`-level
representatives. Proved by descent from `RoseTree.Pathed.insertionForest_append`. -/

section
variable [DecidableEq α]

theorem insertionMultiset_add_host
    (A B C : Multiset (UnorderedTree α)) :
    UnorderedTree.insertionMultiset (A + B) C =
      (C.powerset.bind fun C₁ =>
        ((UnorderedTree.insertionMultiset A C₁) ×ˢ
          (UnorderedTree.insertionMultiset B (C - C₁))).map
          (fun p => p.1 + p.2)) := by
  unfold UnorderedTree.insertionMultiset
  -- §1: permute the host to the concatenation, then split the guests along `sublists'.revzip`.
  rw [RoseTree.Pathed.insertionForest_perm_host_msform
      (UnorderedTree.toList_map_quotientOut_add_perm A B) (C.toList.map Quotient.out),
    RoseTree.Pathed.insertionForest_append, Multiset.map_bind, List.sublists'_map,
    List.revzip_map, ← Multiset.map_coe, Multiset.bind_map]
  -- §2: the powerset bind is the bind over `sublists'.revzip` of `C.toList`.
  have h_rhs : (C.powerset.bind fun C₁ =>
        ((UnorderedTree.insertionMultiset A C₁) ×ˢ
          (UnorderedTree.insertionMultiset B (C - C₁))).map fun p => p.1 + p.2) =
      (C.toList.sublists'.revzip :
          Multiset (List (UnorderedTree α) × List (UnorderedTree α))).bind fun p =>
        ((UnorderedTree.insertionMultiset A ↑p.1) ×ˢ
          (UnorderedTree.insertionMultiset B ↑p.2)).map fun q => q.1 + q.2 := by
    have h := Multiset.coe_revzip_sublists' C.toList
    rw [Multiset.coe_toList] at h
    calc _ = (C.powerset.map fun s => (s, C - s)).bind fun q =>
            ((UnorderedTree.insertionMultiset A q.1) ×ˢ
              (UnorderedTree.insertionMultiset B q.2)).map fun r => r.1 + r.2 :=
          (Multiset.bind_map _ _ _).symm
      _ = _ := by rw [← h, ← Multiset.map_coe, Multiset.bind_map]
  refine Eq.trans ?_ h_rhs.symm
  -- §3: per guest split, the planar buckets are `Quotient.out` images of the nonplanar ones.
  refine Multiset.bind_congr fun (p : List (UnorderedTree α) × List (UnorderedTree α)) _ => ?_
  dsimp only [Prod.map_fst, Prod.map_snd]
  have h_out : ∀ l : List (UnorderedTree α), (l.map Quotient.out).map UnorderedTree.mk = l :=
    fun l => by
      rw [List.map_map]
      exact (List.map_congr_left fun x _ => Quotient.out_eq x).trans (List.map_id _)
  have hA := RoseTree.Pathed.insertionForest_msform_invariance_guests
    (A.toList.map Quotient.out) (gs1 := p.1.map Quotient.out)
    (gs2 := (↑p.1 : Multiset (UnorderedTree α)).toList.map Quotient.out)
    (Multiset.coe_eq_coe.mp (by rw [h_out, h_out, Multiset.coe_toList]))
  have hB := RoseTree.Pathed.insertionForest_msform_invariance_guests
    (B.toList.map Quotient.out) (gs1 := p.2.map Quotient.out)
    (gs2 := (↑p.2 : Multiset (UnorderedTree α)).toList.map Quotient.out)
    (Multiset.coe_eq_coe.mp (by rw [h_out, h_out, Multiset.coe_toList]))
  unfold UnorderedTree.insertionMultiset
  rw [← hA, ← hB]
  -- §4: `msform` turns `++` into `+`, so the product form is the bind form.
  show _ = ((Multiset.map _ (RoseTree.Pathed.insertionForest (A.toList.map Quotient.out)
        (p.1.map Quotient.out))).bind fun ma =>
      (Multiset.map _ (RoseTree.Pathed.insertionForest (B.toList.map Quotient.out)
        (p.2.map Quotient.out))).map (Prod.mk ma)).map _
  rw [Multiset.map_bind, Multiset.map_bind, Multiset.bind_map]
  refine Multiset.bind_congr fun a _ => ?_
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  show (↑((a ++ b).map UnorderedTree.mk) : Multiset (UnorderedTree α)) =
    ↑(a.map UnorderedTree.mk) + ↑(b.map UnorderedTree.mk)
  rw [List.map_append, Multiset.coe_add]

end

/-! ### Split law for multi-graft outputs

Splits of a multi-graft output factor through splits of host and guests (each guest follows its
host): the descent of `RoseTree.Pathed.insertionForest_bind_revzip_sublists'`. Consumed by the
pairing product rule for the GL product (`GrossmanLarson/PairingMul.lean`). -/

section
variable [DecidableEq α]

omit [DecidableEq α] in
private theorem bind_coe_map {β γ δ : Type*} (l : List β) (f : β → γ)
    (g : γ → Multiset δ) :
    (↑(l.map f) : Multiset γ).bind g = (↑l : Multiset β).bind fun x => g (f x) := by
  rw [← Multiset.map_coe, Multiset.bind_map]

/-- **Splits of an insertion output factor through splits of host and guests.** Each
    component of a multi-graft output `X ∈ NIM(A, G)` is one host component of `A` carrying the
    guests grafted into it, so a sub-multiset split of `X` induces a split of `A` and a split of
    `G` (guests follow their host), and the correspondence is multiplicity-faithful:

    `Σ_{X ∈ NIM(A,G)} Σ_{X = X₁ + X₂} (X₁, X₂)
       = Σ_{A = A₁+A₂} Σ_{G = G₁+G₂} NIM(A₁,G₁) ×ˢ NIM(A₂,G₂)`. -/
theorem insertionMultiset_antidiagonal
    (A G : Multiset (UnorderedTree α)) :
    (UnorderedTree.insertionMultiset A G).bind Multiset.antidiagonal =
      (Multiset.antidiagonal A).bind (fun pa =>
        (Multiset.antidiagonal G).bind (fun pg =>
          (UnorderedTree.insertionMultiset pa.1 pg.1) ×ˢ
            (UnorderedTree.insertionMultiset pa.2 pg.2))) := by
  have h_out : ∀ l : List (UnorderedTree α), (l.map Quotient.out).map UnorderedTree.mk = l :=
    fun l => by
      rw [List.map_map]
      exact (List.map_congr_left fun x _ => Quotient.out_eq x).trans (List.map_id _)
  -- The insertion multiset on coerced lists, with the lists themselves as representatives.
  have h_rep : ∀ hl gl : List (UnorderedTree α),
      UnorderedTree.insertionMultiset ↑hl ↑gl =
        (RoseTree.Pathed.insertionForest (hl.map Quotient.out) (gl.map Quotient.out)).map
          (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) := by
    intro hl gl
    unfold UnorderedTree.insertionMultiset
    dsimp only
    rw [RoseTree.Pathed.insertionForest_perm_host_msform
        ((Multiset.coe_eq_coe.mp
          (Multiset.coe_toList (hl : Multiset (UnorderedTree α)))).map Quotient.out),
      RoseTree.Pathed.insertionForest_msform_invariance_guests _
        (gs1 := (↑gl : Multiset (UnorderedTree α)).toList.map Quotient.out)
        (gs2 := gl.map Quotient.out)
        (Multiset.coe_eq_coe.mp (by rw [h_out, h_out, Multiset.coe_toList]))]
  -- LHS: the planar split law, read through `mk`.
  have h_anti : ∀ L : List (RoseTree α),
      Multiset.antidiagonal (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α)) =
        (L.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun x =>
          {((↑(x.1.map UnorderedTree.mk) : Multiset (UnorderedTree α)),
            (↑(x.2.map UnorderedTree.mk) : Multiset (UnorderedTree α)))} := by
    intro L
    rw [Multiset.antidiagonal_coe_sublists', List.sublists'_map, List.revzip_map, List.map_map,
      ← Multiset.map_coe, ← Multiset.bind_singleton]
    rfl
  have h_lhs : (UnorderedTree.insertionMultiset A G).bind Multiset.antidiagonal =
      (A.toList.sublists'.revzip :
          Multiset (List (UnorderedTree α) × List (UnorderedTree α))).bind fun h =>
        (G.toList.sublists'.revzip :
            Multiset (List (UnorderedTree α) × List (UnorderedTree α))).bind fun q =>
          (RoseTree.Pathed.insertionForest (h.2.map Quotient.out) (q.2.map Quotient.out)).bind
            fun L₂ =>
              (RoseTree.Pathed.insertionForest (h.1.map Quotient.out)
                  (q.1.map Quotient.out)).bind fun L₁ =>
                {((↑(L₁.map UnorderedTree.mk) : Multiset (UnorderedTree α)),
                  (↑(L₂.map UnorderedTree.mk) : Multiset (UnorderedTree α)))} := by
    unfold UnorderedTree.insertionMultiset
    dsimp only
    rw [Multiset.bind_map]
    simp only [h_anti]
    rw [RoseTree.Pathed.insertionForest_bind_revzip_sublists' _ _
      fun L₁ L₂ : List (RoseTree α) =>
        ({((↑(L₁.map UnorderedTree.mk) : Multiset (UnorderedTree α)),
          (↑(L₂.map UnorderedTree.mk) : Multiset (UnorderedTree α)))} :
          Multiset (Multiset (UnorderedTree α) × Multiset (UnorderedTree α)))]
    simp only [List.sublists'_map, List.revzip_map, bind_coe_map, Prod.map_fst, Prod.map_snd]
    rfl
  -- RHS: the antidiagonals as `sublists'.revzip` of the representative lists.
  have h_rhs : (Multiset.antidiagonal A).bind (fun pa =>
        (Multiset.antidiagonal G).bind (fun pg =>
          (UnorderedTree.insertionMultiset pa.1 pg.1) ×ˢ
            (UnorderedTree.insertionMultiset pa.2 pg.2))) =
      (A.toList.sublists'.revzip :
          Multiset (List (UnorderedTree α) × List (UnorderedTree α))).bind fun h =>
        (G.toList.sublists'.revzip :
            Multiset (List (UnorderedTree α) × List (UnorderedTree α))).bind fun q =>
          (UnorderedTree.insertionMultiset ↑h.1 ↑q.1) ×ˢ
            (UnorderedTree.insertionMultiset ↑h.2 ↑q.2) := by
    conv_lhs => rw [← Multiset.coe_toList A, ← Multiset.coe_toList G,
      Multiset.antidiagonal_coe_sublists', Multiset.antidiagonal_coe_sublists',
      ← Multiset.map_coe, ← Multiset.map_coe, Multiset.bind_map]
    refine Multiset.bind_congr fun h _ => ?_
    rw [Multiset.bind_map]
  rw [h_lhs, h_rhs]
  refine Multiset.bind_congr fun h _ => Multiset.bind_congr fun q _ => ?_
  rw [h_rep, h_rep, Multiset.bind_bind]
  show _ = (Multiset.map _ (RoseTree.Pathed.insertionForest _ _)).bind fun a =>
    (Multiset.map _ (RoseTree.Pathed.insertionForest _ _)).map (Prod.mk a)
  rw [Multiset.bind_map]
  refine Multiset.bind_congr fun L₁ _ => ?_
  rw [Multiset.map_map, ← Multiset.bind_singleton]
  rfl

end

end UnorderedTree
