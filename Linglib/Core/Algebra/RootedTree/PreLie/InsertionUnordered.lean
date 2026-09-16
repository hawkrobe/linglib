/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
import Linglib.Core.Data.List.Zip
import Linglib.Core.Data.Multiset.Antidiagonal
import Linglib.Core.Data.RoseTree.DecEq
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
`insertionMultiset {T} B` is a singleton `{T'}` and `T'.rootValue =
T.rootValue`: grafting guests into a tree only modifies its subtrees,
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
    `insertionMultiset {T} B` is a singleton `{T'}` and `T'.rootValue =
    T.rootValue`. Descends through `insertionForest_singleton` +
    `RoseTree.value_multiGraft`. -/
theorem insertionMultiset_singleton_rootValue
    (T : UnorderedTree α) (B : Multiset (UnorderedTree α))
    {F' : Multiset (UnorderedTree α)} (hF' : F' ∈ insertionMultiset {T} B) :
    ∃ T' : UnorderedTree α, F' = ({T'} : Multiset (UnorderedTree α)) ∧
      T'.rootValue = T.rootValue := by
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
  -- for some choice. Hence value T'_tr = value (Q.out T) = T.rootValue.
  refine ⟨UnorderedTree.mk T'_tr, ?_, ?_⟩
  · -- F' = {UnorderedTree.mk T'_tr}: L = [T'_tr], so F' = ofList [mk T'_tr] = {mk T'_tr}.
    rw [← hL_eq, ← hT'_tr_eq]
    show (Multiset.ofList (([T'_tr] : List (RoseTree α)).map UnorderedTree.mk) :
            Multiset (UnorderedTree α)) = {UnorderedTree.mk T'_tr}
    rfl
  · -- Root value preservation through the tree substrate.
    -- T'_tr ∈ insertion T.out (...): T'_tr = multiGraft T.out pairs for some pairs.
    rw [UnorderedTree.rootValue_mk]
    -- Unfold `insertion` to extract the choice and reduce value-equality.
    rw [RoseTree.Pathed.insertion_def, Multiset.mem_coe, List.mem_map] at hT'_tr_mem
    obtain ⟨choice, _hchoice_mem, hchoice_eq⟩ := hT'_tr_mem
    rw [← hchoice_eq]
    -- Now: value (multiGraft T.out (choice.zip ...)) = T.rootValue
    rw [RoseTree.value_multiGraft]
    -- value T.out = rootValue T via `rootValue_mk T.out_eq`.
    -- (Quotient.out T).value = (mk (Quotient.out T)).rootValue by `rootValue_mk`;
    -- mk (Quotient.out T) = T by `T.out_eq`.
    show (Quotient.out T).value = T.rootValue
    have h_eq : UnorderedTree.mk (Quotient.out T) = T := T.out_eq
    calc (Quotient.out T).value
        = (UnorderedTree.mk (Quotient.out T)).rootValue := (UnorderedTree.rootValue_mk _).symm
      _ = T.rootValue := by rw [h_eq]


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

Splits of a multi-graft output factor through splits of host and guests
(each guest follows its host component): the multi-graft counterpart of
`insertionMultiset_add_host`, from which it is proved by induction on
the host. Consumed by the pairing product rule for the GL product
(`GrossmanLarson/PairingMul.lean`). -/

section
variable [DecidableEq α]

/-! ### Helper lemmas

A few small multiset/insertion building blocks used by both targets below.
-/

/-- `Multiset.antidiagonal` of a singleton: `antidiag {a} = {(0, {a}), ({a}, 0)}`.
    Follows from `antidiagonal_cons` + `antidiagonal_zero`. -/
private theorem antidiagonal_singleton {β : Type*} (a : β) :
    Multiset.antidiagonal ({a} : Multiset β) =
      ({(0, {a}), ({a}, 0)} : Multiset (Multiset β × Multiset β)) := by
  show Multiset.antidiagonal (a ::ₘ (0 : Multiset β)) = _
  rw [Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
  simp [Multiset.map_singleton, Prod.map]

omit [DecidableEq α] in
/-- A `NIM {T} G` output is always a singleton forest (card 1). This is the
    `UnorderedTree.insertionMultiset_card_eq` specialization to a singleton host. -/
private theorem insertionMultiset_singleton_host_singleton
    (T : UnorderedTree α) (G : Multiset (UnorderedTree α))
    {X : Multiset (UnorderedTree α)} (hX : X ∈ UnorderedTree.insertionMultiset {T} G) :
    ∃ T' : UnorderedTree α, X = {T'} := by
  have hcard : X.card = ({T} : Multiset (UnorderedTree α)).card :=
    UnorderedTree.insertionMultiset_card_eq {T} G hX
  rw [Multiset.card_singleton] at hcard
  exact Multiset.card_eq_one.mp hcard

/-- **Triple-partition reindexing** (`[UPSTREAM]` candidate): two equivalent
    enumerations of ordered triple-partitions of a multiset `G`. The
    "powerset-then-antidiagonal" enumeration (pick `G₁ ⊆ G`, then split
    `G - G₁`) equals the "antidiagonal-then-powerset" enumeration (split
    `G`, then pick `G₂ ⊆` second part of the split), under the bijection
    `(G₁, pg'.1, pg'.2) ↔ (pg.1, G₂, pg.2 - G₂)` where `G₂ = G₁`,
    `pg.1 = pg'.1`, `pg.2 = G₁ + pg'.2`.

    Reduces to `Multiset.powerset_powerset_pair_swap` after
    converting both `antidiagonal` factors to `powerset.map` form via
    `antidiagonal_eq_map_powerset` and identifying the inner bind as `f`
    applied to the implicit third-part `G - G₁ - S`.

    Used by `insertionMultiset_antidiagonal` to align the LHS structure
    (one host tree peeled, free guest split, A' substructure split) with
    the RHS structure (A split, G split, free guest sub-split). -/
private theorem triple_partition_reindex {β γ : Type*} [DecidableEq β]
    (G : Multiset β)
    (f : Multiset β → Multiset β → Multiset β → Multiset γ) :
    (G.powerset.bind fun G₁ =>
        (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
          f G₁ pg'.1 pg'.2) =
      (Multiset.antidiagonal G).bind fun pg =>
        pg.2.powerset.bind fun G₂ =>
          f G₂ pg.1 (pg.2 - G₂) := by
  -- Step 1: Reformulate LHS as a `(pair-enum).bind h` where `h (a, b) := f a (G - a - b) b`.
  -- Use `antidiagonal_eq_map_powerset` to turn `antidiag (G - G₁)` into
  -- `(G - G₁).powerset.map (S ↦ ((G - G₁) - S, S))`.
  set h : Multiset β × Multiset β → Multiset γ :=
    fun p => f p.1 (G - p.1 - p.2) p.2 with h_def
  have h_lhs : (G.powerset.bind fun G₁ =>
            (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
              f G₁ pg'.1 pg'.2) =
        (G.powerset.bind fun G₁ =>
          (G - G₁).powerset.map (fun B => (G₁, B))).bind h := by
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun G₁ _ => ?_
    rw [Multiset.antidiagonal_eq_map_powerset, Multiset.bind_map, Multiset.bind_map]
  -- Step 2: Reformulate RHS similarly.
  have h_rhs : (Multiset.antidiagonal G).bind (fun pg =>
            pg.2.powerset.bind (fun G₂ =>
              f G₂ pg.1 (pg.2 - G₂))) =
        (G.powerset.bind fun F₁ =>
          F₁.powerset.map (fun A => (A, F₁ - A))).bind h := by
    -- RHS uses antidiag G, the second coord pg.2 indexes the bind. By antidiag_eq_map_powerset
    -- with t ↦ (G - t, t), pg = (G - pg.2, pg.2). Set T = pg.2. Then pg.1 = G - T.
    rw [Multiset.antidiagonal_eq_map_powerset, Multiset.bind_map]
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun T hT => ?_
    rw [Multiset.bind_map]
    refine Multiset.bind_congr fun G₂ hG₂ => ?_
    -- Goal: f G₂ (G - T) (T - G₂) = h (G₂, T - G₂) = f G₂ (G - G₂ - (T - G₂)) (T - G₂).
    -- Need: G - G₂ - (T - G₂) = G - T. Since G₂ ⊆ T ⊆ G, use tsub_tsub + add identities.
    have hG₂_le : G₂ ≤ T := Multiset.mem_powerset.mp hG₂
    have hT_le : T ≤ G := Multiset.mem_powerset.mp hT
    show f G₂ (G - T) (T - G₂) = f G₂ (G - G₂ - (T - G₂)) (T - G₂)
    congr 1
    -- G - G₂ - (T - G₂) = G - (G₂ + (T - G₂)) = G - T (using G₂ + (T - G₂) = T from add_tsub_cancel_of_le).
    rw [tsub_tsub, add_tsub_cancel_of_le hG₂_le]
  rw [h_lhs, h_rhs, Multiset.powerset_powerset_pair_swap]

/-- **Triple-partition reindexing (flipped)**: variant of
    `triple_partition_reindex` where the second-level powerset goes through
    the *first* coordinate of the antidiagonal instead of the second.

    Bijection: `(G₁, pg'.1, pg'.2) ↔ (G₂, pg.1 - G₂, pg.2)` where `G₂ = G₁`,
    `pg.1 = G₁ + pg'.1`, `pg.2 = pg'.2`.

    Derived from `triple_partition_reindex` via `Multiset.antidiagonal_swap`. -/
private theorem triple_partition_reindex_flip {β γ : Type*} [DecidableEq β]
    (G : Multiset β)
    (f : Multiset β → Multiset β → Multiset β → Multiset γ) :
    (G.powerset.bind fun G₁ =>
        (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
          f G₁ pg'.1 pg'.2) =
      (Multiset.antidiagonal G).bind fun pg =>
        pg.1.powerset.bind fun G₂ =>
          f G₂ (pg.1 - G₂) pg.2 := by
  -- Reindex the inner `antidiag (G - G₁)` via `antidiagonal_swap` to switch pg'.1 ↔ pg'.2,
  -- then apply `triple_partition_reindex` with f's arguments shifted.
  -- LHS = G.powerset.bind (G₁ ↦ ((antidiag (G - G₁)).map swap).bind (pg' ↦ f G₁ pg'.2 pg'.1))
  --     [using antidiag_swap to expose pg.swap]
  -- = G.powerset.bind (G₁ ↦ antidiag (G - G₁).bind (pg' ↦ f G₁ pg'.2 pg'.1))
  --     [the swap.bind absorbed into pg'.swap]
  -- Now apply triple_partition_reindex with f' G₁ x y := f G₁ y x.
  -- Define helper function with swapped 2nd/3rd args.
  set g : Multiset β → Multiset β → Multiset β → Multiset γ :=
    fun a b c => f a c b with g_def
  -- LHS: original form (using f).
  -- Goal: ... = antidiag G.bind (pg ↦ pg.1.powerset.bind (G₂ ↦ f G₂ (pg.1 - G₂) pg.2))
  -- Rewrite LHS as g G₁ pg'.2 pg'.1 (= f G₁ pg'.1 pg'.2 by def of g).
  have h_lhs : (G.powerset.bind fun G₁ =>
            (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
              f G₁ pg'.1 pg'.2) =
        G.powerset.bind fun G₁ =>
          ((Multiset.antidiagonal (G - G₁)).map Prod.swap).bind fun pg' =>
            g G₁ pg'.1 pg'.2 := by
    refine Multiset.bind_congr fun G₁ _ => ?_
    rw [Multiset.bind_map]
    refine Multiset.bind_congr fun pg' _ => ?_
    rfl
  rw [h_lhs]
  -- Use antidiag_swap to absorb the .map Prod.swap.
  simp_rw [Multiset.antidiagonal_swap]
  -- Now LHS is `G.powerset.bind (G₁ ↦ antidiag (G - G₁).bind (pg' ↦ g G₁ pg'.1 pg'.2))`.
  rw [triple_partition_reindex G g]
  -- Goal: antidiag G.bind (pg ↦ pg.2.powerset.bind (G₂ ↦ g G₂ pg.1 (pg.2 - G₂)))
  --     = antidiag G.bind (pg ↦ pg.1.powerset.bind (G₂ ↦ f G₂ (pg.1 - G₂) pg.2))
  -- g G₂ pg.1 (pg.2 - G₂) = f G₂ (pg.2 - G₂) pg.1. Use antidiag_swap to flip pg.
  conv_lhs => rw [show Multiset.antidiagonal G =
      (Multiset.antidiagonal G).map Prod.swap from (Multiset.antidiagonal_swap G).symm]
  rw [Multiset.bind_map]
  refine Multiset.bind_congr fun pg _ => ?_
  -- After swap: (Prod.swap pg).2 = pg.1, (Prod.swap pg).1 = pg.2. So:
  --   g G₂ (Prod.swap pg).1 ((Prod.swap pg).2 - G₂) = g G₂ pg.2 (pg.1 - G₂)
  --                                                 = f G₂ (pg.1 - G₂) pg.2.
  rfl

/-- Antidiagonal of `(X_T + X_A')` where `X_T` is a singleton multiset
    `{T'}`: by `antidiagonal_add` + `antidiagonal_singleton`, the result
    splits into two summands "T' joins right" + "T' joins left". -/
private theorem antidiagonal_singleton_add {β : Type*} [DecidableEq β] (T' : β) (Y : Multiset β) :
    Multiset.antidiagonal (({T'} : Multiset β) + Y) =
      (Multiset.antidiagonal Y).map (fun pA' => (pA'.1, ({T'} : Multiset β) + pA'.2)) +
      (Multiset.antidiagonal Y).map (fun pA' => (({T'} : Multiset β) + pA'.1, pA'.2)) := by
  rw [Multiset.antidiagonal_add, antidiagonal_singleton]
  show ({(0, {T'}), ({T'}, 0)} :
            Multiset (Multiset β × Multiset β)).bind (fun pT =>
        (Multiset.antidiagonal Y).map (fun pA' => (pT.1 + pA'.1, pT.2 + pA'.2))) = _
  -- {(0,{T'}), ({T'},0)}.bind f = f (0,{T'}) + f ({T'},0)
  rw [show ({(0, {T'}), ({T'}, 0)} : Multiset (Multiset β × Multiset β)) =
        (0, ({T'} : Multiset β)) ::ₘ (({T'} : Multiset β), 0) ::ₘ 0 from rfl,
      Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  -- Now compute each .map by 0 + x = x.
  congr 1
  · apply Multiset.map_congr rfl
    intro pA' _
    show ((0 : Multiset β) + pA'.1, ({T'} : Multiset β) + pA'.2) =
         (pA'.1, ({T'} : Multiset β) + pA'.2)
    rw [zero_add]
  · apply Multiset.map_congr rfl
    intro pA' _
    show (({T'} : Multiset β) + pA'.1, (0 : Multiset β) + pA'.2) =
         (({T'} : Multiset β) + pA'.1, pA'.2)
    rw [zero_add]

/-! ### Split law for multi-graft outputs -/

/-- **Splits of an insertion output factor through splits of host and
    guests.** Each component of a multi-graft output `X ∈ NIM(A, G)` is
    one host component of `A` carrying the guests grafted into it, so a
    sub-multiset split of `X` induces a split of `A` and a split of `G`
    (guests follow their host), and the correspondence is
    multiplicity-faithful:

    `Σ_{X ∈ NIM(A,G)} Σ_{X = X₁ + X₂} (X₁, X₂)
       = Σ_{A = A₁+A₂} Σ_{G = G₁+G₂} NIM(A₁,G₁) ×ˢ NIM(A₂,G₂)`.

    Proved by induction on `A` from `insertionMultiset_add_host`
    (peeling one host tree; `NIM({T}, G)` outputs are singleton
    forests, whose antidiagonal is the trivial two-way split). -/
theorem insertionMultiset_antidiagonal
    (A G : Multiset (UnorderedTree α)) :
    (UnorderedTree.insertionMultiset A G).bind Multiset.antidiagonal =
      (Multiset.antidiagonal A).bind (fun pa =>
        (Multiset.antidiagonal G).bind (fun pg =>
          (UnorderedTree.insertionMultiset pa.1 pg.1) ×ˢ
            (UnorderedTree.insertionMultiset pa.2 pg.2))) := by
  induction A using Multiset.induction_on generalizing G with
  | empty =>
    -- A = 0. Case on G.
    rw [Multiset.antidiagonal_zero, Multiset.singleton_bind]
    by_cases hG : G = 0
    · -- G = 0: NIM 0 0 = {0}, antidiag 0 = {(0,0)}. RHS = NIM 0 0 ×ˢ NIM 0 0 = {(0,0)}.
      subst hG
      rw [UnorderedTree.insertionMultiset_zero_right, Multiset.singleton_bind,
          Multiset.antidiagonal_zero, Multiset.singleton_bind,
          UnorderedTree.insertionMultiset_zero_right]
      rfl
    · -- G ≠ 0: LHS = (NIM 0 G).bind antidiag = 0.bind = 0. RHS: each pg has at least one nonzero side.
      rw [UnorderedTree.insertionMultiset_zero_left_of_ne_zero G hG, Multiset.zero_bind]
      -- RHS: prove the bind is 0 by showing each summand is 0.
      symm
      have h_rhs_eq :
          (Multiset.antidiagonal G).bind (fun pg =>
              (UnorderedTree.insertionMultiset 0 pg.1) ×ˢ
              (UnorderedTree.insertionMultiset 0 pg.2)) =
          (Multiset.antidiagonal G).bind (fun _ => (0 : Multiset (Multiset (UnorderedTree α) ×
            Multiset (UnorderedTree α)))) := by
        refine Multiset.bind_congr fun pg hpg => ?_
        have hpg_sum : pg.1 + pg.2 = G := Multiset.mem_antidiagonal.mp hpg
        by_cases h1 : pg.1 = 0
        · -- pg.1 = 0 ⇒ pg.2 = G ≠ 0.
          have h2 : pg.2 ≠ 0 := by
            intro h2eq
            apply hG
            rw [← hpg_sum, h1, h2eq]; rfl
          rw [UnorderedTree.insertionMultiset_zero_left_of_ne_zero pg.2 h2,
              Multiset.product_zero]
        · rw [UnorderedTree.insertionMultiset_zero_left_of_ne_zero pg.1 h1,
              Multiset.zero_product]
      rw [h_rhs_eq, Multiset.bind_zero]
  | cons T A' ih =>
    -- A = T ::ₘ A' = {T} + A'.
    have h_cons_eq : (T ::ₘ A' : Multiset (UnorderedTree α)) = ({T} : Multiset _) + A' := by
      rw [Multiset.singleton_add]
    -- Step 1: Rewrite LHS via insertionMultiset_add_host.
    rw [h_cons_eq, UnorderedTree.insertionMultiset_add_host {T} A' G]
    -- LHS = (G.powerset.bind (G₁ ↦ (NIM {T} G₁ ×ˢ NIM A' (G-G₁)).map (·.1+·.2))).bind antidiag
    rw [Multiset.bind_assoc]
    -- LHS = G.powerset.bind (G₁ ↦ ((NIM {T} G₁ ×ˢ NIM A' (G-G₁)).map (·.1+·.2)).bind antidiag)
    -- Step 2: Push antidiag through the .map ↦ bind, expand antidiag (X_T + X_A')
    -- via antidiagonal_singleton_add (since X_T is a singleton).
    have h_lhs_inner : ∀ G₁ : Multiset (UnorderedTree α),
        (((UnorderedTree.insertionMultiset {T} G₁) ×ˢ
            (UnorderedTree.insertionMultiset A' (G - G₁))).map
            (fun p => p.1 + p.2)).bind Multiset.antidiagonal =
        ((UnorderedTree.insertionMultiset {T} G₁).bind fun X_T =>
            (UnorderedTree.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (pA'.1, X_T + pA'.2)) +
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (X_T + pA'.1, pA'.2))) := by
      intro G₁
      -- LHS_inner: bind . map = map then bind = ... apply antidiagonal_singleton_add per X_T.
      rw [Multiset.bind_map]
      -- Goal: (NIM {T} G₁ ×ˢ NIM A' (G-G₁)).bind (p ↦ antidiag (p.1 + p.2)) = (NIM {T} G₁).bind ...
      -- Unfold ×ˢ as bind.
      show ((UnorderedTree.insertionMultiset {T} G₁).bind (fun X_T =>
              (UnorderedTree.insertionMultiset A' (G - G₁)).map (Prod.mk X_T))).bind
                (fun p => Multiset.antidiagonal (p.1 + p.2)) = _
      rw [Multiset.bind_assoc]
      refine Multiset.bind_congr fun X_T hX_T => ?_
      rw [Multiset.bind_map]
      refine Multiset.bind_congr fun X_A' hX_A' => ?_
      -- Each X_T is a singleton {T'}. Apply antidiagonal_singleton_add.
      obtain ⟨T', hT'⟩ := insertionMultiset_singleton_host_singleton T G₁ hX_T
      subst hT'
      exact antidiagonal_singleton_add T' X_A'
    rw [show (G.powerset.bind fun G₁ =>
            (((UnorderedTree.insertionMultiset {T} G₁) ×ˢ
                (UnorderedTree.insertionMultiset A' (G - G₁))).map
                (fun p => p.1 + p.2)).bind Multiset.antidiagonal) =
          G.powerset.bind fun G₁ =>
            ((UnorderedTree.insertionMultiset {T} G₁).bind fun X_T =>
                (UnorderedTree.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                  (Multiset.antidiagonal X_A').map
                      (fun pA' => (pA'.1, X_T + pA'.2)) +
                  (Multiset.antidiagonal X_A').map
                      (fun pA' => (X_T + pA'.1, pA'.2)))
        from Multiset.bind_congr (fun G₁ _ => h_lhs_inner G₁)]
    -- Step 3: Split LHS into two summands (T-right + T-left) using bind_add via map_add and sum_add.
    -- Strategy: each inner sum splits via bind_congr.
    have h_split_inner : ∀ G₁ : Multiset (UnorderedTree α),
        ((UnorderedTree.insertionMultiset {T} G₁).bind fun X_T =>
            (UnorderedTree.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (pA'.1, X_T + pA'.2)) +
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (X_T + pA'.1, pA'.2))) =
        ((UnorderedTree.insertionMultiset {T} G₁).bind fun X_T =>
            (UnorderedTree.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (pA'.1, X_T + pA'.2))) +
        ((UnorderedTree.insertionMultiset {T} G₁).bind fun X_T =>
            (UnorderedTree.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (X_T + pA'.1, pA'.2))) := by
      intro G₁
      -- Split each X_A' bind summand and each X_T bind summand.
      rw [← Multiset.bind_add]
      refine Multiset.bind_congr fun X_T _ => ?_
      rw [← Multiset.bind_add]
    rw [show (G.powerset.bind fun G₁ =>
            (UnorderedTree.insertionMultiset {T} G₁).bind fun X_T =>
              (UnorderedTree.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (pA'.1, X_T + pA'.2)) +
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (X_T + pA'.1, pA'.2))) =
          (G.powerset.bind fun G₁ =>
            (UnorderedTree.insertionMultiset {T} G₁).bind fun X_T =>
              (UnorderedTree.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (pA'.1, X_T + pA'.2))) +
          (G.powerset.bind fun G₁ =>
            (UnorderedTree.insertionMultiset {T} G₁).bind fun X_T =>
              (UnorderedTree.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (X_T + pA'.1, pA'.2)))
        from by
      rw [← Multiset.bind_add]
      exact Multiset.bind_congr (fun G₁ _ => h_split_inner G₁)]
    -- Step 4: Now rewrite RHS via antidiagonal_cons split into T-right + T-left summands.
    rw [show (Multiset.antidiagonal ({T} + A' : Multiset (UnorderedTree α))) =
            Multiset.antidiagonal (T ::ₘ A') from by rw [← h_cons_eq],
        Multiset.antidiagonal_cons]
    -- RHS: antidiag (T ::ₘ A') = antidiag A'.map (Prod.map id (cons T)) + antidiag A'.map (Prod.map (cons T) id)
    rw [Multiset.add_bind]
    -- RHS = RHS_T_right_old + RHS_T_left_old
    -- The two map-binds become bind-(after rebrand).
    rw [Multiset.bind_map, Multiset.bind_map]
    -- Goal: (LHS_T_right + LHS_T_left) = (RHS_T_right + RHS_T_left)
    -- We'll match LHS_T_right ↔ RHS_T_right (T on right side of pair) and similarly for left.
    congr 1
    · -- Match T-right: pair has X_T on .2.
      -- Strategy: massage both LHS_T_right and RHS_T_right into a common form
      --   "antidiag A'.bind (pa' ↦ (NIM A').bind X_A' ↦ antidiag X_A' .bind (...) ...)"
      -- via IH on the LHS and `insertionMultiset_add_host` on the RHS, then apply
      -- `triple_partition_reindex` to align the G-indexing.
      -- 1) Reorder LHS_T_right using bind_map_comm to expose `antidiag (NIM A' (G-G₁)).bind`.
      rw [show (G.powerset.bind fun G₁ =>
              (UnorderedTree.insertionMultiset {T} G₁).bind fun X_T =>
                (UnorderedTree.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                  (Multiset.antidiagonal X_A').map (fun pA' => (pA'.1, X_T + pA'.2))) =
            (G.powerset.bind fun G₁ =>
              ((UnorderedTree.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        rw [Multiset.bind_bind]
        refine Multiset.bind_congr fun X_A' _ => ?_
        rw [Multiset.bind_map_comm]]
      -- 2) Apply IH on (NIM A' (G - G₁)).bind antidiag.
      rw [show (G.powerset.bind fun G₁ =>
              ((UnorderedTree.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) =
            (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (UnorderedTree.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (UnorderedTree.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [ih (G - G₁)]]
      -- 3) Pull the binds inside via bind_assoc.
      rw [show (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (UnorderedTree.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (UnorderedTree.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) =
            (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((UnorderedTree.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (UnorderedTree.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                      fun X_T => (pA'.1, X_T + pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        refine Multiset.bind_congr fun pa' _ => ?_
        rw [Multiset.bind_assoc]]
      -- 4) Reorder G₁ and pa' binds (swap G.powerset and antidiag A').
      rw [show (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((UnorderedTree.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (UnorderedTree.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                      fun X_T => (pA'.1, X_T + pA'.2)) =
            (Multiset.antidiagonal A').bind fun pa' =>
              G.powerset.bind fun G₁ =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((UnorderedTree.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (UnorderedTree.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                      fun X_T => (pA'.1, X_T + pA'.2)
        from Multiset.bind_bind _ _]
      -- 5) Apply triple_partition_reindex on the G.powerset / antidiag (G - G₁) layer.
      refine Multiset.bind_congr fun pa' _ => ?_
      rw [triple_partition_reindex G
        (fun G₁ x y =>
          ((UnorderedTree.insertionMultiset pa'.1 x) ×ˢ
              (UnorderedTree.insertionMultiset pa'.2 y)).bind
            (fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
              fun X_T => (pA'.1, X_T + pA'.2)))]
      -- 6) Now LHS form matches RHS form (with bind_bind for G₂/X_T to T ::ₘ pa'.2 NIM).
      -- The RHS form (after bind_map): antidiag G.bind (pg ↦
      --   NIM pa'.1 pg.1 ×ˢ NIM (T ::ₘ pa'.2) pg.2).
      -- Compare with our current LHS form: antidiag G.bind (pg ↦ pg.2.powerset.bind (G₂ ↦ ...))
      refine Multiset.bind_congr fun pg _ => ?_
      -- RHS at this position: NIM pa'.1 pg.1 ×ˢ NIM (T ::ₘ pa'.2) pg.2 (after Prod.map id (cons T)).
      -- The Prod.map id (cons T) pa' has fst = pa'.1 and snd = T ::ₘ pa'.2 = {T} + pa'.2.
      -- Apply insertionMultiset_add_host on the RHS to peel {T} from the second argument.
      have h_prod_map_id : (Prod.map (id : Multiset (UnorderedTree α) → _) (Multiset.cons T) pa') =
          (pa'.1, T ::ₘ pa'.2) := rfl
      rw [h_prod_map_id]
      show (pg.2.powerset.bind fun G₂ =>
              ((UnorderedTree.insertionMultiset pa'.1 pg.1) ×ˢ
                  (UnorderedTree.insertionMultiset pa'.2 (pg.2 - G₂))).bind
                (fun pA' => (UnorderedTree.insertionMultiset {T} G₂).map
                  fun X_T => (pA'.1, X_T + pA'.2))) =
            (UnorderedTree.insertionMultiset pa'.1 pg.1) ×ˢ
              (UnorderedTree.insertionMultiset (T ::ₘ pa'.2) pg.2)
      -- Apply insertionMultiset_add_host to NIM (T ::ₘ pa'.2) pg.2.
      rw [show (T ::ₘ pa'.2 : Multiset (UnorderedTree α)) = ({T} : Multiset _) + pa'.2 from
            (Multiset.singleton_add T pa'.2).symm,
          UnorderedTree.insertionMultiset_add_host {T} pa'.2 pg.2]
      -- RHS: NIM pa'.1 pg.1 ×ˢ (pg.2.powerset.bind (G₂ ↦ (NIM {T} G₂ ×ˢ NIM pa'.2 (pg.2-G₂)).map (·.1+·.2)))
      -- Need: pg.2.powerset.bind LHS_inner = NIM pa'.1 pg.1 ×ˢ (pg.2.powerset.bind RHS_inner_form).
      -- Use s ×ˢ (t.bind f) = t.bind (b ↦ s ×ˢ f b).
      rw [show ∀ s : Multiset (Multiset (UnorderedTree α)),
              ∀ tt : Multiset (UnorderedTree α) → Multiset (Multiset (UnorderedTree α)),
                s ×ˢ (pg.2.powerset.bind tt) =
                  pg.2.powerset.bind (fun G₂ => s ×ˢ tt G₂) from ?_]
      · refine Multiset.bind_congr fun G₂ _ => ?_
        -- Goal: ((NIM pa'.1 pg.1) ×ˢ NIM pa'.2 (pg.2-G₂)).bind (pA' ↦ NIM {T} G₂.map (X_T ↦ (pA'.1, X_T + pA'.2)))
        --     = NIM pa'.1 pg.1 ×ˢ ((NIM {T} G₂ ×ˢ NIM pa'.2 (pg.2-G₂)).map (·.1+·.2))
        -- Both sides describe pairs (Y₁, X_T + Y₂) for (Y₁, Y₂, X_T) ∈
        -- NIM pa'.1 pg.1 × NIM pa'.2 (pg.2-G₂) × NIM {T} G₂.
        -- Unfold ×ˢ as bind on both sides.
        show ((UnorderedTree.insertionMultiset pa'.1 pg.1).bind (fun Y₁ =>
              (UnorderedTree.insertionMultiset pa'.2 (pg.2 - G₂)).map (Prod.mk Y₁))).bind
                (fun pA' => (UnorderedTree.insertionMultiset {T} G₂).map
                  fun X_T => (pA'.1, X_T + pA'.2)) =
              (UnorderedTree.insertionMultiset pa'.1 pg.1).bind (fun Y₁ =>
                (((UnorderedTree.insertionMultiset {T} G₂).bind fun X_T =>
                  (UnorderedTree.insertionMultiset pa'.2 (pg.2 - G₂)).map (Prod.mk X_T)).map
                    (fun p => p.1 + p.2)).map (Prod.mk Y₁))
        rw [Multiset.bind_assoc]
        refine Multiset.bind_congr fun Y₁ _ => ?_
        rw [Multiset.bind_map]
        -- Compose the outer (Prod.mk Y₁) and (·.1+·.2) maps + push through bind.
        rw [Multiset.map_map, Multiset.map_bind]
        -- Inside each X_T, compose Prod.mk X_T with (Y₁, ·.1+·.2): Y₂ ↦ (Y₁, X_T + Y₂).
        rw [show ((UnorderedTree.insertionMultiset {T} G₂).bind fun X_T =>
                Multiset.map ((Prod.mk Y₁) ∘
                    fun p : Multiset (UnorderedTree α) × Multiset (UnorderedTree α) => p.1 + p.2)
                  (Multiset.map (Prod.mk X_T)
                    (UnorderedTree.insertionMultiset pa'.2 (pg.2 - G₂)))) =
              ((UnorderedTree.insertionMultiset {T} G₂).bind fun X_T =>
                (UnorderedTree.insertionMultiset pa'.2 (pg.2 - G₂)).map
                  (fun Y₂ => (Y₁, X_T + Y₂))) from by
          refine Multiset.bind_congr fun X_T _ => ?_
          rw [Multiset.map_map]
          rfl]
        -- Both sides now: bind/bind ⇒ bind_map_comm.
        exact Multiset.bind_map_comm _ _
      · -- Prove the helper: s ×ˢ (t.bind f) = t.bind (b ↦ s ×ˢ f b).
        intros s tt
        show s.bind (fun a => (pg.2.powerset.bind tt).map (Prod.mk a)) =
            pg.2.powerset.bind (fun G₂ => s.bind (fun a => (tt G₂).map (Prod.mk a)))
        rw [Multiset.bind_bind]
        refine Multiset.bind_congr fun G₂ _ => ?_
        rw [Multiset.map_bind]
    · -- Match T-left: pair has X_T on .1. Symmetric to T-right by mirror argument.
      -- Same proof scheme as T-right but with X_T joining the first coord of the pair.
      rw [show (G.powerset.bind fun G₁ =>
              (UnorderedTree.insertionMultiset {T} G₁).bind fun X_T =>
                (UnorderedTree.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                  (Multiset.antidiagonal X_A').map (fun pA' => (X_T + pA'.1, pA'.2))) =
            (G.powerset.bind fun G₁ =>
              ((UnorderedTree.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        rw [Multiset.bind_bind]
        refine Multiset.bind_congr fun X_A' _ => ?_
        rw [Multiset.bind_map_comm]]
      rw [show (G.powerset.bind fun G₁ =>
              ((UnorderedTree.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) =
            (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (UnorderedTree.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (UnorderedTree.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [ih (G - G₁)]]
      rw [show (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (UnorderedTree.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (UnorderedTree.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) =
            (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((UnorderedTree.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (UnorderedTree.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                      fun X_T => (X_T + pA'.1, pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        refine Multiset.bind_congr fun pa' _ => ?_
        rw [Multiset.bind_assoc]]
      rw [show (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((UnorderedTree.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (UnorderedTree.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                      fun X_T => (X_T + pA'.1, pA'.2)) =
            (Multiset.antidiagonal A').bind fun pa' =>
              G.powerset.bind fun G₁ =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((UnorderedTree.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (UnorderedTree.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
                      fun X_T => (X_T + pA'.1, pA'.2)
        from Multiset.bind_bind _ _]
      -- For T-left RHS: antidiag G.bind (pg ↦ NIM (T ::ₘ pa'.1) pg.1 ×ˢ NIM pa'.2 pg.2).
      -- Symmetry: T attaches to the *first* host part. Apply triple_partition_reindex_flip.
      refine Multiset.bind_congr fun pa' _ => ?_
      rw [triple_partition_reindex_flip G
        (fun G₁ x y =>
          ((UnorderedTree.insertionMultiset pa'.1 x) ×ˢ
              (UnorderedTree.insertionMultiset pa'.2 y)).bind
            (fun pA' => (UnorderedTree.insertionMultiset {T} G₁).map
              fun X_T => (X_T + pA'.1, pA'.2)))]
      refine Multiset.bind_congr fun pg _ => ?_
      have h_prod_map_id : (Prod.map (Multiset.cons T) (id : Multiset (UnorderedTree α) → _) pa') =
          (T ::ₘ pa'.1, pa'.2) := rfl
      rw [h_prod_map_id]
      show (pg.1.powerset.bind fun G₂ =>
              ((UnorderedTree.insertionMultiset pa'.1 (pg.1 - G₂)) ×ˢ
                  (UnorderedTree.insertionMultiset pa'.2 pg.2)).bind
                (fun pA' => (UnorderedTree.insertionMultiset {T} G₂).map
                  fun X_T => (X_T + pA'.1, pA'.2))) =
            (UnorderedTree.insertionMultiset (T ::ₘ pa'.1) pg.1) ×ˢ
              (UnorderedTree.insertionMultiset pa'.2 pg.2)
      -- Apply insertionMultiset_add_host on NIM (T ::ₘ pa'.1) pg.1.
      rw [show (T ::ₘ pa'.1 : Multiset (UnorderedTree α)) = ({T} : Multiset _) + pa'.1 from
            (Multiset.singleton_add T pa'.1).symm,
          UnorderedTree.insertionMultiset_add_host {T} pa'.1 pg.1]
      -- RHS: (pg.1.powerset.bind (G₂ ↦ (NIM {T} G₂ ×ˢ NIM pa'.1 (pg.1-G₂)).map (·.1+·.2))) ×ˢ NIM pa'.2 pg.2
      -- Use (s.bind f) ×ˢ t = s.bind (a ↦ f a ×ˢ t).
      rw [show ∀ s : Multiset (Multiset (UnorderedTree α)),
              ∀ tt : Multiset (UnorderedTree α) → Multiset (Multiset (UnorderedTree α)),
                (pg.1.powerset.bind tt) ×ˢ s =
                  pg.1.powerset.bind (fun G₂ => tt G₂ ×ˢ s) from ?_]
      · refine Multiset.bind_congr fun G₂ _ => ?_
        -- Goal: ((NIM pa'.1 (pg.1-G₂)) ×ˢ NIM pa'.2 pg.2).bind (pA' ↦ NIM {T} G₂.map (X_T ↦ (X_T + pA'.1, pA'.2)))
        --     = ((NIM {T} G₂ ×ˢ NIM pa'.1 (pg.1-G₂)).map (·.1+·.2)) ×ˢ NIM pa'.2 pg.2
        -- Unfold ×ˢ everywhere.
        show ((UnorderedTree.insertionMultiset pa'.1 (pg.1 - G₂)).bind (fun Y₁ =>
              (UnorderedTree.insertionMultiset pa'.2 pg.2).map (Prod.mk Y₁))).bind
                (fun pA' => (UnorderedTree.insertionMultiset {T} G₂).map
                  fun X_T => (X_T + pA'.1, pA'.2)) =
            (Multiset.map (fun p : Multiset (UnorderedTree α) × Multiset (UnorderedTree α) => p.1 + p.2)
                ((UnorderedTree.insertionMultiset {T} G₂).bind (fun X_T =>
                  (UnorderedTree.insertionMultiset pa'.1 (pg.1 - G₂)).map (Prod.mk X_T)))).bind
              (fun first => (UnorderedTree.insertionMultiset pa'.2 pg.2).map (Prod.mk first))
        -- Reformulate LHS: bind, bind_map, bind.
        rw [Multiset.bind_assoc]
        -- Goal: NIM pa'.1 (pg.1-G₂).bind (Y₁ ↦ ((NIM pa'.2 pg.2).map (Prod.mk Y₁)).bind (pA' ↦ NIM {T} G₂.map (...)))
        rw [show ((UnorderedTree.insertionMultiset pa'.1 (pg.1 - G₂)).bind (fun Y₁ =>
                ((UnorderedTree.insertionMultiset pa'.2 pg.2).map (Prod.mk Y₁)).bind
                  (fun pA' => (UnorderedTree.insertionMultiset {T} G₂).map
                    fun X_T => (X_T + pA'.1, pA'.2)))) =
              (UnorderedTree.insertionMultiset pa'.1 (pg.1 - G₂)).bind (fun Y₁ =>
                (UnorderedTree.insertionMultiset pa'.2 pg.2).bind (fun Y₂ =>
                  (UnorderedTree.insertionMultiset {T} G₂).map
                    fun X_T => (X_T + Y₁, Y₂))) from by
          refine Multiset.bind_congr fun Y₁ _ => ?_
          rw [Multiset.bind_map]]
        -- RHS: Push map p.1+p.2 through inner bind, then bind outer.
        rw [show (Multiset.map (fun p : Multiset (UnorderedTree α) × Multiset (UnorderedTree α) =>
                  p.1 + p.2)
                ((UnorderedTree.insertionMultiset {T} G₂).bind (fun X_T =>
                  (UnorderedTree.insertionMultiset pa'.1 (pg.1 - G₂)).map (Prod.mk X_T)))).bind
              (fun first => (UnorderedTree.insertionMultiset pa'.2 pg.2).map (Prod.mk first)) =
              ((UnorderedTree.insertionMultiset {T} G₂).bind fun X_T =>
                (UnorderedTree.insertionMultiset pa'.1 (pg.1 - G₂)).bind fun Y₁ =>
                  (UnorderedTree.insertionMultiset pa'.2 pg.2).map (fun Y₂ => (X_T + Y₁, Y₂)))
            from by
          rw [Multiset.map_bind, Multiset.bind_assoc]
          refine Multiset.bind_congr fun X_T _ => ?_
          rw [Multiset.map_map, Multiset.bind_map]
          refine Multiset.bind_congr fun Y₁ _ => ?_
          rfl]
        -- Now LHS: NIM pa'.1.bind (Y₁ ↦ NIM pa'.2.bind (Y₂ ↦ NIM {T} G₂.map (X_T ↦ (X_T + Y₁, Y₂))))
        -- RHS: NIM {T} G₂.bind (X_T ↦ NIM pa'.1.bind (Y₁ ↦ NIM pa'.2.map (Y₂ ↦ (X_T + Y₁, Y₂))))
        -- Step a: Apply bind_map_comm to swap Y₂ and X_T inside Y₁.
        rw [show ((UnorderedTree.insertionMultiset pa'.1 (pg.1 - G₂)).bind fun Y₁ =>
              (UnorderedTree.insertionMultiset pa'.2 pg.2).bind (fun Y₂ =>
                (UnorderedTree.insertionMultiset {T} G₂).map fun X_T => (X_T + Y₁, Y₂))) =
            ((UnorderedTree.insertionMultiset pa'.1 (pg.1 - G₂)).bind fun Y₁ =>
              (UnorderedTree.insertionMultiset {T} G₂).bind (fun X_T =>
                (UnorderedTree.insertionMultiset pa'.2 pg.2).map fun Y₂ => (X_T + Y₁, Y₂)))
            from by
          refine Multiset.bind_congr fun Y₁ _ => ?_
          rw [Multiset.bind_map_comm]]
        -- Step b: Swap Y₁ and X_T via bind_bind.
        rw [Multiset.bind_bind]
      · -- Prove the helper: (s.bind f) ×ˢ t = s.bind (a ↦ f a ×ˢ t).
        intros s tt
        show (pg.1.powerset.bind tt).bind (fun a => s.map (Prod.mk a)) =
            pg.1.powerset.bind (fun G₂ => (tt G₂).bind (fun a => s.map (Prod.mk a)))
        rw [Multiset.bind_assoc]


end

end UnorderedTree
