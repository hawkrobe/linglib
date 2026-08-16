/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
import Linglib.Core.Algebra.RootedTree.PreLie.InsertionAddHost
import Linglib.Core.Algebra.RootedTree.PreLie.InsertionNodeDecomp
import Linglib.Core.Data.Multiset.Antidiagonal
import Linglib.Core.Data.RoseTree.DecEq
import Linglib.Core.Data.RoseTree.Nonplanar
import Mathlib.Data.Multiset.Basic

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# Nonplanar multi-tree insertion

Lift of `RoseTree.Pathed.insertionForest` through `Nonplanar.mk`.

Given two multisets of nonplanar trees `F` (host forest) and `G` (guest
forest), `Nonplanar.insertionMultiset F G` produces the multiset of all
forests obtained by inserting `G`'s trees at vertices of `F`'s trees,
summing over all assignments (Foissy 2021 Theorem 5.1).

## Main results

* `Nonplanar.insertionMultiset_add_host`: multi-graft into a
  disjoint-union host decomposes over guest partitions
  ([oudom-guin-2008] Prop 2.7.iii substrate).
* `Nonplanar.insertionMultiset_antidiagonal`: splits of a multi-graft
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


namespace RoseTree.Nonplanar

variable {α : Type*}

/-- Multi-tree insertion at the nonplanar level. Given a host forest
    `F` and guest forest `G` (both `Multiset (Nonplanar α)`), produces
    the multiset of all forests obtained by inserting `G`'s trees at
    vertices of `F`'s trees. Defined via list representatives
    (`Multiset.toList`) + tree representatives (`Quotient.out`) +
    `RoseTree.Pathed.insertionForest`. -/
noncomputable def insertionMultiset (F G : Multiset (Nonplanar α)) :
    Multiset (Multiset (Nonplanar α)) :=
  let hostTrees : List (RoseTree α) := F.toList.map Quotient.out
  let guestTrees : List (RoseTree α) := G.toList.map Quotient.out
  (RoseTree.Pathed.insertionForest hostTrees guestTrees).map
    fun L => Multiset.ofList (L.map Nonplanar.mk)

/-- With no guests, the multi-graft leaves `F` unchanged:
    `insertionMultiset F 0 = {F}`. -/
theorem insertionMultiset_zero_right (F : Multiset (Nonplanar α)) :
    insertionMultiset F 0 = ({F} : Multiset (Multiset (Nonplanar α))) := by
  unfold insertionMultiset
  rw [Multiset.toList_zero]
  show (RoseTree.Pathed.insertionForest (F.toList.map Quotient.out) []).map
        (fun L => (Multiset.ofList (L.map Nonplanar.mk) :
                    Multiset (Nonplanar α))) = ({F} : Multiset _)
  rw [RoseTree.Pathed.insertionForest_nil_guests, Multiset.map_singleton]
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
  · show (RoseTree.Pathed.insertionForest [] (Quotient.out g :: gs.map Quotient.out)).map _ = 0
    rw [RoseTree.Pathed.insertionForest_empty_host_nonempty_guests, Multiset.map_zero]

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
theorem toList_map_quotientOut_add_perm (M N : Multiset (Nonplanar α)) :
    ((M + N).toList.map Quotient.out).Perm
      (M.toList.map Quotient.out ++ N.toList.map Quotient.out) := by
  rw [← List.map_append]
  exact (Multiset.toList_add_perm M N).map _

/-- Substrate for `insertionMultiset_card_eq`: every output list in
    `insertionForest host guests` has length equal to the host length.
    `insertionForest` produces `T' :: F'` lists by recursion on the host;
    each step prepends one tree and recurses on the tail. -/
private theorem _root_.RoseTree.Pathed.insertionForest_length
    {α : Type*} :
    ∀ (host guests : List (RoseTree α)) {L : List (RoseTree α)},
      L ∈ RoseTree.Pathed.insertionForest host guests → L.length = host.length
  | [],     [],         L, hL => by
    rw [RoseTree.Pathed.insertionForest_nil_nil] at hL
    rw [Multiset.mem_singleton.mp hL]
  | [],     _ :: _,     L, hL => by
    rw [RoseTree.Pathed.insertionForest_empty_host_nonempty_guests] at hL
    exact absurd hL (Multiset.notMem_zero L)
  | T :: F, [],         L, hL => by
    rw [RoseTree.Pathed.insertionForest_cons_host_nil_guests] at hL
    rw [Multiset.mem_singleton.mp hL]
  | T :: F, T_g :: Ts,  L, hL => by
    rw [RoseTree.Pathed.insertionForest_cons_cons] at hL
    -- L ∈ bind of bind of map; unfold mem step by step.
    rw [Multiset.mem_bind] at hL
    obtain ⟨assignment, _hass, hL⟩ := hL
    rw [Multiset.mem_bind] at hL
    obtain ⟨T', _hT', hL⟩ := hL
    rw [Multiset.mem_map] at hL
    obtain ⟨F', hF'mem, hL_eq⟩ := hL
    -- L = T' :: F', with F' from the inner insertionForest F (sub-guests).
    have hF'len : F'.length = F.length :=
      RoseTree.Pathed.insertionForest_length F _ hF'mem
    rw [← hL_eq, List.length_cons, hF'len, List.length_cons]
  termination_by host _ => host.length

/-- The insertion multiset preserves cardinality: every forest in
    `insertionMultiset A B` has the same cardinality as `A`.

    Proof: `insertionMultiset A B` is built from
    `insertionForest (A.toList.map Q.out) (B.toList.map Q.out)`; every
    output list `L` has `L.length = (A.toList.map Q.out).length = A.card`
    (via `RoseTree.Pathed.insertionForest_length`); and the cardinality of
    the lifted `Multiset.ofList (L.map mk)` equals `L.length`. -/
theorem insertionMultiset_card_eq {α : Type*} (A B : Multiset (Nonplanar α))
    {F' : Multiset (Nonplanar α)} (hF' : F' ∈ insertionMultiset A B) :
    F'.card = A.card := by
  unfold insertionMultiset at hF'
  rw [Multiset.mem_map] at hF'
  obtain ⟨L, hL_mem, hL_eq⟩ := hF'
  have hLlen : L.length = (A.toList.map Quotient.out).length :=
    RoseTree.Pathed.insertionForest_length _ _ hL_mem
  rw [← hL_eq]
  -- F'.card = (Multiset.ofList (L.map mk)).card = (L.map mk).length = L.length.
  show (Multiset.ofList (L.map Nonplanar.mk)).card = A.card
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
    (T : Nonplanar α) (B : Multiset (Nonplanar α))
    {F' : Multiset (Nonplanar α)} (hF' : F' ∈ insertionMultiset {T} B) :
    ∃ T' : Nonplanar α, F' = ({T'} : Multiset (Nonplanar α)) ∧
      T'.rootValue = T.rootValue := by
  unfold insertionMultiset at hF'
  rw [Multiset.mem_map] at hF'
  obtain ⟨L, hL_mem, hL_eq⟩ := hF'
  -- ({T} : Multiset _).toList = [T] via `Multiset.toList_singleton`.
  have h_toList : ({T} : Multiset (Nonplanar α)).toList.map Quotient.out =
      [Quotient.out T] := by
    rw [Multiset.toList_singleton]; rfl
  rw [h_toList] at hL_mem
  -- Use `insertionForest_singleton`.
  rw [RoseTree.Pathed.insertionForest_singleton] at hL_mem
  rw [Multiset.mem_map] at hL_mem
  obtain ⟨T'_tr, hT'_tr_mem, hT'_tr_eq⟩ := hL_mem
  -- T'_tr ∈ insertion (Q.out T) gs, so T'_tr = multiGraft (Q.out T) (choice.zip gs)
  -- for some choice. Hence value T'_tr = value (Q.out T) = T.rootValue.
  refine ⟨Nonplanar.mk T'_tr, ?_, ?_⟩
  · -- F' = {Nonplanar.mk T'_tr}: L = [T'_tr], so F' = ofList [mk T'_tr] = {mk T'_tr}.
    rw [← hL_eq, ← hT'_tr_eq]
    show (Multiset.ofList (([T'_tr] : List (RoseTree α)).map Nonplanar.mk) :
            Multiset (Nonplanar α)) = {Nonplanar.mk T'_tr}
    rfl
  · -- Root value preservation through the tree substrate.
    -- T'_tr ∈ insertion T.out (...): T'_tr = multiGraft T.out pairs for some pairs.
    rw [Nonplanar.rootValue_mk]
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
    have h_eq : Nonplanar.mk (Quotient.out T) = T := T.out_eq
    calc (Quotient.out T).value
        = (Nonplanar.mk (Quotient.out T)).rootValue := (Nonplanar.rootValue_mk _).symm
      _ = T.rootValue := by rw [h_eq]


/-! ### Insertion into a singleton node host -/

/-- `Multiset.bind` as a mapped sum (`join` is definitionally `sum`). -/
private theorem bind_eq_map_sum {γ δ : Type*} (s : Multiset γ)
    (f : γ → Multiset δ) : s.bind f = (s.map f).sum := rfl

/-- The `true`-bucket of a zip over `Quotient.out` representatives has
    the nonplanar `true`-bucket as its `mk`-image. -/
private theorem filterMap_zip_out_mk_t (l : List (Nonplanar α)) (assn : List Bool) :
    (((l.map Quotient.out).zip assn).filterMap
        (fun p => if p.2 then some p.1 else none)).map Nonplanar.mk =
      (l.zip assn).filterMap (fun p => if p.2 then some p.1 else none) := by
  induction l generalizing assn with
  | nil => rfl
  | cons x l ih =>
    cases assn with
    | nil => rfl
    | cons b assn =>
      cases b with
      | true =>
        show Nonplanar.mk (Quotient.out x) ::
            ((((l.map Quotient.out).zip assn).filterMap _).map Nonplanar.mk) = _
        have hx : Nonplanar.mk (Quotient.out x) = x := Quotient.out_eq x
        rw [hx, ih]
        rfl
      | false => exact ih assn

/-- The `false`-bucket analog of `filterMap_zip_out_mk_t`. -/
private theorem filterMap_zip_out_mk_f (l : List (Nonplanar α)) (assn : List Bool) :
    (((l.map Quotient.out).zip assn).filterMap
        (fun p => if p.2 then none else some p.1)).map Nonplanar.mk =
      (l.zip assn).filterMap (fun p => if p.2 then none else some p.1) := by
  induction l generalizing assn with
  | nil => rfl
  | cons x l ih =>
    cases assn with
    | nil => rfl
    | cons b assn =>
      cases b with
      | true => exact ih assn
      | false =>
        show Nonplanar.mk (Quotient.out x) ::
            ((((l.map Quotient.out).zip assn).filterMap _).map Nonplanar.mk) = _
        have hx : Nonplanar.mk (Quotient.out x) = x := Quotient.out_eq x
        rw [hx, ih]
        rfl

/-- **NIM-level keystone**: at the Nonplanar multi-insertion level, grafting
    `B` into the singleton host `{node a A'}` decomposes by partitioning
    B's grafting positions into "at the root vertex" (becomes new
    children) vs "in A's subtrees" (recursive NIM).

    Descent through the quotient: the singleton host's canonical planar
    representative is `Perm`-swapped for a visible planar node,
    `RoseTree.Pathed.insertion_node_split` provides the root-vs-subtree
    mask decomposition, and the mask enumeration is converted to the
    powerset bind via `listChoices_bridge_powerset_paired` plus the
    powerset partition involution (the mask convention has `true` =
    root guests, while the powerset bind runs over the subtree bucket). -/
theorem insertionMultiset_singleton_node [DecidableEq α]
    (a : α) (A' B : Multiset (Nonplanar α)) :
    Nonplanar.insertionMultiset
        ({Nonplanar.node a A'} : Multiset (Nonplanar α)) B =
      (B.powerset.bind fun B₁ =>
         (Nonplanar.insertionMultiset A' B₁).map fun F' =>
           ({Nonplanar.node a (F' + (B - B₁))} : Multiset (Nonplanar α))) := by
  -- §1: the canonical planar representative of the host is equivalent to
  -- the visible node on A''s canonical children list.
  have h_mk2 : Nonplanar.mk (RoseTree.node a (A'.toList.map Quotient.out)) =
      Nonplanar.node a A' := by
    rw [← Nonplanar.node_mk_tree_list]
    congr 1
    rw [List.map_map,
        show A'.toList.map (Nonplanar.mk ∘ Quotient.out) = A'.toList from
          (List.map_congr_left fun x _ => Quotient.out_eq x).trans
            (List.map_id _)]
    exact A'.coe_toList
  have h_equiv : RoseTree.Perm
      (Quotient.out (Nonplanar.node a A'))
      (RoseTree.node a (A'.toList.map Quotient.out)) :=
    Nonplanar.mk_eq_mk_iff.mp
      (((Nonplanar.node a A').out_eq).trans h_mk2.symm)
  -- §2: unfold NIM; the host list is the singleton of the canonical rep.
  unfold Nonplanar.insertionMultiset
  rw [show (({Nonplanar.node a A'} : Multiset (Nonplanar α)).toList.map
        Quotient.out : List (RoseTree α))
      = [Quotient.out (Nonplanar.node a A')] from by
    rw [Multiset.toList_singleton]
    rfl]
  -- §3: swap the host representative under the msform map.
  have h_host := RoseTree.Pathed.insertionForest_perm_host
    (B.toList.map Quotient.out) (List.Forall₂.cons h_equiv List.Forall₂.nil)
  have h_host' :
      (RoseTree.Pathed.insertionForest [Quotient.out (Nonplanar.node a A')]
          (B.toList.map Quotient.out)).map
        (fun L => (Multiset.ofList (L.map Nonplanar.mk) :
          Multiset (Nonplanar α))) =
      (RoseTree.Pathed.insertionForest
          [RoseTree.node a (A'.toList.map Quotient.out)]
          (B.toList.map Quotient.out)).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
    have h2 := congrArg
      (Multiset.map (fun l : List (Nonplanar α) =>
        (Multiset.ofList l : Multiset (Nonplanar α)))) h_host
    rw [Multiset.map_map, Multiset.map_map] at h2
    exact h2
  rw [h_host']
  -- §4: singleton-forest reduction + the node-split engine.
  rw [RoseTree.Pathed.insertionForest_singleton, Multiset.map_map,
      RoseTree.Pathed.insertion_node_split, Multiset.map_bind]
  -- §5: convert the RHS powerset bind to the mask enumeration. The mask
  -- convention has `true` = root guests, so the powerset bind (over the
  -- subtree bucket B₁) is first flipped by the partition involution.
  have h_rhs : (B.powerset.bind fun B₁ =>
        (Nonplanar.insertionMultiset A' B₁).map fun F' =>
          ({Nonplanar.node a (F' + (B - B₁))} : Multiset (Nonplanar α))) =
      (Multiset.ofList
          (RoseTree.Pathed.listChoices [true, false] B.toList.length)).bind
        (fun assn =>
          (Nonplanar.insertionMultiset A'
              (((B.toList.zip assn).filterMap
                fun p => if p.2 then none else some p.1 : List (Nonplanar α)) :
                Multiset (Nonplanar α))).map
            fun F' => ({Nonplanar.node a (F' +
              (((B.toList.zip assn).filterMap
                fun p => if p.2 then some p.1 else none : List (Nonplanar α)) :
                Multiset (Nonplanar α)))} : Multiset (Nonplanar α))) := by
    -- Step A: flip the partition so the bind variable is the root bucket.
    rw [bind_eq_map_sum]
    rw [Multiset.powerset_partition_swap B
      (fun B₁ rest => (Nonplanar.insertionMultiset A' B₁).map fun F' =>
        ({Nonplanar.node a (F' + rest)} : Multiset (Nonplanar α)))]
    -- Step B: pair form + the powerset↔mask bridge.
    rw [show (B.powerset.map fun s =>
          (Nonplanar.insertionMultiset A' (B - s)).map fun F' =>
            ({Nonplanar.node a (F' + s)} : Multiset (Nonplanar α))) =
        ((B.powerset.map fun s => (s, B - s)).map
          fun pr => (Nonplanar.insertionMultiset A' pr.2).map fun F' =>
            ({Nonplanar.node a (F' + pr.1)} : Multiset (Nonplanar α))) from by
      rw [Multiset.map_map]
      rfl]
    rw [show (B.powerset.map fun s => (s, B - s)) =
        (Multiset.ofList
            (RoseTree.Pathed.listChoices [true, false] B.toList.length)).map
          (fun assn =>
            ((((B.toList.zip assn).filterMap
                fun p => if p.2 then some p.1 else none : List (Nonplanar α)) :
                Multiset (Nonplanar α)),
             (((B.toList.zip assn).filterMap
                fun p => if p.2 then none else some p.1 : List (Nonplanar α)) :
                Multiset (Nonplanar α)))) from by
      conv_lhs => rw [show B = (↑(B.toList) : Multiset (Nonplanar α)) from
        B.coe_toList.symm]
      rw [← RoseTree.Pathed.listChoices_bridge_powerset_paired (l := B.toList)]]
    rw [Multiset.map_map, ← bind_eq_map_sum]
    rfl
  refine Eq.trans ?_ h_rhs.symm
  -- §6: per-mask congruence. Align mask lengths, then reduce each mask.
  rw [List.length_map]
  refine Multiset.bind_congr fun assn h_assn => ?_
  -- Named buckets: planar (out-rep) and nonplanar (canonical) per side.
  set gs_t : List (RoseTree α) := ((B.toList.map Quotient.out).zip assn).filterMap
    (fun p => if p.2 then some p.1 else none) with hgs_t
  set gs_f : List (RoseTree α) := ((B.toList.map Quotient.out).zip assn).filterMap
    (fun p => if p.2 then none else some p.1) with hgs_f
  set s_t : Multiset (Nonplanar α) := Multiset.ofList
    ((B.toList.zip assn).filterMap
      (fun p => if p.2 then some p.1 else none)) with hs_t
  set s_f : Multiset (Nonplanar α) := Multiset.ofList
    ((B.toList.zip assn).filterMap
      (fun p => if p.2 then none else some p.1)) with hs_f
  -- mk-image facts for the two planar buckets.
  have h_t_mk : Multiset.ofList (gs_t.map Nonplanar.mk) = s_t := by
    rw [hgs_t, filterMap_zip_out_mk_t, hs_t]
  have h_f_perm : (gs_f.map Nonplanar.mk).Perm
      ((s_f.toList.map Quotient.out).map Nonplanar.mk) := by
    apply Multiset.coe_eq_coe.mp
    rw [hgs_f, filterMap_zip_out_mk_f, List.map_map,
        show s_f.toList.map (Nonplanar.mk ∘ Quotient.out) = s_f.toList from
          (List.map_congr_left fun x _ => Quotient.out_eq x).trans
            (List.map_id _),
        Multiset.coe_toList, hs_f]
  have h_guests := RoseTree.Pathed.insertionForest_msform_invariance_guests
    (A'.toList.map Quotient.out) h_f_perm
  -- Assemble: fuse post-maps, factor through msform, swap guests, recombine.
  rw [Multiset.map_map]
  calc (RoseTree.Pathed.insertionForest (A'.toList.map Quotient.out) gs_f).map
        ((((fun L => (Multiset.ofList (L.map Nonplanar.mk) :
            Multiset (Nonplanar α))) ∘ fun T' => [T']))
          ∘ (fun cs' => RoseTree.node a (gs_t ++ cs')))
      = ((RoseTree.Pathed.insertionForest (A'.toList.map Quotient.out) gs_f).map
          (fun L => (Multiset.ofList (L.map Nonplanar.mk) :
            Multiset (Nonplanar α)))).map
        (fun M => ({Nonplanar.node a (s_t + M)} : Multiset (Nonplanar α))) := by
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl fun cs' _ => ?_
        show ({Nonplanar.mk (RoseTree.node a (gs_t ++ cs'))} :
          Multiset (Nonplanar α)) = _
        congr 1
        rw [← Nonplanar.node_mk_tree_list]
        congr 1
        rw [List.map_append, ← Multiset.coe_add, h_t_mk]
    _ = ((RoseTree.Pathed.insertionForest (A'.toList.map Quotient.out)
            (s_f.toList.map Quotient.out)).map
          (fun L => (Multiset.ofList (L.map Nonplanar.mk) :
            Multiset (Nonplanar α)))).map
        (fun M => ({Nonplanar.node a (s_t + M)} : Multiset (Nonplanar α))) := by
        rw [h_guests]
    _ = (Nonplanar.insertionMultiset A' s_f).map
        (fun F' => ({Nonplanar.node a (F' + s_t)} : Multiset (Nonplanar α))) := by
        unfold Nonplanar.insertionMultiset
        rw [Multiset.map_map, Multiset.map_map]
        refine Multiset.map_congr rfl fun L _ => ?_
        show ({Nonplanar.node a (s_t + Multiset.ofList (L.map Nonplanar.mk))} :
          Multiset (Nonplanar α)) = _
        rw [add_comm]
        rfl


/-! ### Disjoint-union hosts, representatives, and iterated grafting

Multi-graft into a disjoint-union host decomposes over guest partitions
(the combinatorial heart of [oudom-guin-2008] Prop 2.7.iii);
`insertionMultiset` computes on arbitrary `RoseTree`-level
representatives. Proved by descent from the `RoseTree.Pathed` substrate
(`InsertionAddHost.lean`). -/

section
variable [DecidableEq α]

theorem insertionMultiset_add_host
    (A B C : Multiset (Nonplanar α)) :
    Nonplanar.insertionMultiset (A + B) C =
      (C.powerset.bind fun C₁ =>
        ((Nonplanar.insertionMultiset A C₁) ×ˢ
          (Nonplanar.insertionMultiset B (C - C₁))).map
          (fun p => p.1 + p.2)) := by
  -- Steps 1-5: Unfold NIM, apply host-Perm bridge, hostBucketSum bridge, assignment
  -- rewrite, and push msform through the outer bind.
  unfold Nonplanar.insertionMultiset
  rw [RoseTree.Pathed.insertionForest_perm_host_msform
        (Nonplanar.toList_map_quotientOut_add_perm A B) (C.toList.map Quotient.out)]
  rw [← RoseTree.Pathed.hostBucketSum_eq_insertionForest]
  rw [RoseTree.Pathed.hostBucketSum_assignment_rewrite]
  rw [Multiset.map_bind, List.length_map]
  simp only [List.nil_append]
  -- Step 6: Define `msform : List (RoseTree α) → Multiset (Nonplanar α)` as a local
  -- abbreviation matching `Nonplanar.insertionMultiset`'s post-processing.
  set msform : List (RoseTree α) → Multiset (Nonplanar α) :=
    fun L => (Multiset.ofList (L.map Nonplanar.mk)) with hmsform
  -- Step 7: Strategy — define `F : Multiset × Multiset → Multiset Multiset` so:
  --   LHS_inner(assn) = F (↑filter_t (C.toList zip assn), ↑filter_f (...))
  --   RHS_inner(C₁)   = F (C₁, C - C₁)
  -- Then RHS = (C.powerset.map (s ↦ (s, C - s))).bind F = (↑lc).bind (F ∘ ...) by
  -- the powerset bridge. The remaining work is per-assn equality.
  set F : Multiset (Nonplanar α) × Multiset (Nonplanar α) →
            Multiset (Multiset (Nonplanar α)) :=
    fun pair =>
      Multiset.map (fun p : Multiset (Nonplanar α) × Multiset (Nonplanar α) => p.1 + p.2)
        (Multiset.map msform
            (RoseTree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList A))
              (List.map Quotient.out pair.1.toList)) ×ˢ
          Multiset.map msform
            (RoseTree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList B))
              (List.map Quotient.out (Multiset.toList pair.2)))) with hF
  -- Step 7a: RHS = (C.powerset.map (s ↦ (s, C - s))).bind F via `← Multiset.bind_map`.
  have h_rhs_step1 :
      ((Multiset.powerset C).bind fun C₁ => F (C₁, C - C₁)) =
      ((Multiset.powerset C).map (fun s : Multiset (Nonplanar α) => (s, C - s))).bind F := by
    rw [Multiset.bind_map]
  -- Step 7b: Apply the powerset bridge to convert
  -- `(C.powerset.map (s, C-s))` to `(↑lc).map (filter_t, filter_f)`.
  have h_rhs_step2 :
      ((Multiset.powerset C).map (fun s : Multiset (Nonplanar α) => (s, C - s))) =
      (Multiset.ofList (RoseTree.Pathed.listChoices [true, false] C.toList.length)).map
        (fun assn : List Bool =>
          let s_t : Multiset (Nonplanar α) :=
            (C.toList.zip assn).filterMap (fun p => if p.snd then some p.fst else none)
          let s_f : Multiset (Nonplanar α) :=
            (C.toList.zip assn).filterMap (fun p => if p.snd then none else some p.fst)
          (s_t, s_f)) := by
    rw [show C = (↑(C.toList) : Multiset (Nonplanar α)) from C.coe_toList.symm]
    rw [← RoseTree.Pathed.listChoices_bridge_powerset_paired (l := C.toList)]
    simp only [Multiset.coe_toList]
  -- Step 7c: Reshape RHS to (↑lc).bind (F ∘ ...) so we can match per-assn.
  show ((↑(RoseTree.Pathed.listChoices [true, false] C.toList.length) :
          Multiset (List Bool)).bind fun a =>
        Multiset.map msform
          (RoseTree.Pathed.hostBucketSum (List.map Quotient.out (Multiset.toList A))
            (List.map Quotient.out (Multiset.toList B))
            (List.filterMap (fun p => if p.snd = true then some p.fst else none)
              ((List.map Quotient.out (Multiset.toList C)).zip a))
            (List.filterMap (fun p => if p.snd = true then none else some p.fst)
              ((List.map Quotient.out (Multiset.toList C)).zip a))
            [])) =
      (Multiset.powerset C).bind fun C₁ => F (C₁, C - C₁)
  rw [h_rhs_step1, h_rhs_step2, Multiset.bind_map]
  -- Step 8: Per-assn reduction via Multiset.bind_congr.
  refine Multiset.bind_congr fun assn h_assn => ?_
  have hlen : assn.length = C.toList.length := by
    have : assn ∈ RoseTree.Pathed.listChoices [true, false] C.toList.length :=
      Multiset.mem_coe.mp h_assn
    exact RoseTree.Pathed.mem_listChoices_bool_length C.toList.length assn this
  -- Step 8a: Apply hostBucketSum_nil_remaining and combine the two `.map`s.
  rw [RoseTree.Pathed.hostBucketSum_nil_remaining, Multiset.map_map]
  -- Step 8b: Unfold F on the RHS and abbreviate the filter results at multiset level.
  rw [hF]
  set s_t : Multiset (Nonplanar α) :=
    (List.filterMap (fun p => if p.snd = true then some p.fst else none)
      ((Multiset.toList C).zip assn) : Multiset (Nonplanar α)) with hs_t
  set s_f : Multiset (Nonplanar α) :=
    (List.filterMap (fun p => if p.snd = true then none else some p.fst)
      ((Multiset.toList C).zip assn) : Multiset (Nonplanar α)) with hs_f
  -- Beta-reduce the let binding on the RHS via `show`.
  show ((RoseTree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList A))
            (List.filterMap (fun p => if p.snd = true then some p.fst else none)
              ((List.map Quotient.out (Multiset.toList C)).zip assn))) ×ˢ
        RoseTree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList B))
            (List.filterMap (fun p => if p.snd = true then none else some p.fst)
              ((List.map Quotient.out (Multiset.toList C)).zip assn))).map
        (msform ∘ fun p => p.fst ++ p.snd) =
      (Multiset.map msform
          (RoseTree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList A))
            (List.map Quotient.out s_t.toList)) ×ˢ
        Multiset.map msform
          (RoseTree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList B))
            (List.map Quotient.out s_f.toList))).map (fun p => p.fst + p.snd)
  -- Step 8c: Set up `RoseTree`-level/canonical guest lists and bridge them via Perm.
  -- LHS uses `((C.toList.map Q.out).zip assn).filterMap_t` (`RoseTree` level).
  -- RHS uses `s_t.toList.map Q.out` (canonical Q.out of multiset). Both have multiset
  -- image `s_t = ↑((C.toList.zip assn).filterMap_t)` after `.map mk`.
  set ft_tree : List (RoseTree α) :=
    List.filterMap (fun p => if p.snd = true then some p.fst else none)
      ((List.map Quotient.out (Multiset.toList C)).zip assn) with hft_tree
  set ff_tree : List (RoseTree α) :=
    List.filterMap (fun p => if p.snd = true then none else some p.fst)
      ((List.map Quotient.out (Multiset.toList C)).zip assn) with hff_tree
  set ft_canon : List (RoseTree α) := s_t.toList.map Quotient.out with hft_canon
  set ff_canon : List (RoseTree α) := s_f.toList.map Quotient.out with hff_canon
  -- Step 8c.1: List-level: `((l.map Q.out).zip a).filterMap_t.map mk = (l.zip a).filterMap_t`.
  have h_ft_mk_eq : ft_tree.map Nonplanar.mk =
      (((Multiset.toList C).zip assn).filterMap
        (fun p => if p.snd then some p.fst else none) : List (Nonplanar α)) := by
    have h_aux : ∀ (l : List (Nonplanar α)) (a : List Bool),
        (((l.map Quotient.out).zip a).filterMap (fun p => if p.snd = true then some p.fst else none)).map
          Nonplanar.mk = (l.zip a).filterMap (fun p => if p.snd = true then some p.fst else none) := by
      intro l a
      induction l generalizing a with
      | nil =>
        show (((([] : List (Nonplanar α)).map Quotient.out).zip a).filterMap _).map Nonplanar.mk = _
        rw [show ([] : List (Nonplanar α)).map Quotient.out = [] from rfl]
        rfl
      | cons x rest ih =>
        cases a with
        | nil =>
          rw [show ((x :: rest).map Quotient.out).zip ([] : List Bool) = [] from by
            cases (x :: rest).map Quotient.out <;> rfl]
          rfl
        | cons b a_rest =>
          rw [show (x :: rest).map Quotient.out =
                Quotient.out x :: rest.map Quotient.out from rfl]
          rw [show (Quotient.out x :: rest.map Quotient.out).zip (b :: a_rest) =
                (Quotient.out x, b) :: (rest.map Quotient.out).zip a_rest from rfl]
          rw [show (x :: rest).zip (b :: a_rest) = (x, b) :: rest.zip a_rest from rfl]
          rw [List.filterMap_cons, List.filterMap_cons]
          cases b with
          | true =>
            -- if true then some Q.out x else none = some (Q.out x); on RHS some x.
            show (Quotient.out x ::
                ((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then some p.fst else none)).map Nonplanar.mk =
                x ::
                (rest.zip a_rest).filterMap
                  (fun p => if p.snd = true then some p.fst else none)
            rw [show ((Quotient.out x ::
                ((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then some p.fst else none)).map Nonplanar.mk) =
                Nonplanar.mk (Quotient.out x) ::
                  (((rest.map Quotient.out).zip a_rest).filterMap
                    (fun p => if p.snd = true then some p.fst else none)).map Nonplanar.mk from rfl]
            rw [ih a_rest]
            congr 1
            exact x.out_eq
          | false =>
            -- if false then some else none = none; both sides skip.
            show (((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then some p.fst else none)).map Nonplanar.mk =
                (rest.zip a_rest).filterMap
                  (fun p => if p.snd = true then some p.fst else none)
            exact ih a_rest
    show (ft_tree.map Nonplanar.mk : List (Nonplanar α)) =
        ((Multiset.toList C).zip assn).filterMap (fun p => if p.snd = true then some p.fst else none)
    exact h_aux C.toList assn
  -- Step 8c.2: Same identity for filter_f.
  have h_ff_mk_eq : ff_tree.map Nonplanar.mk =
      (((Multiset.toList C).zip assn).filterMap
        (fun p => if p.snd then none else some p.fst) : List (Nonplanar α)) := by
    have h_aux : ∀ (l : List (Nonplanar α)) (a : List Bool),
        (((l.map Quotient.out).zip a).filterMap
          (fun p => if p.snd = true then none else some p.fst)).map Nonplanar.mk =
        (l.zip a).filterMap (fun p => if p.snd = true then none else some p.fst) := by
      intro l a
      induction l generalizing a with
      | nil =>
        show (((([] : List (Nonplanar α)).map Quotient.out).zip a).filterMap _).map Nonplanar.mk = _
        rw [show ([] : List (Nonplanar α)).map Quotient.out = [] from rfl]
        rfl
      | cons x rest ih =>
        cases a with
        | nil =>
          rw [show ((x :: rest).map Quotient.out).zip ([] : List Bool) = [] from by
            cases (x :: rest).map Quotient.out <;> rfl]
          rfl
        | cons b a_rest =>
          rw [show (x :: rest).map Quotient.out =
                Quotient.out x :: rest.map Quotient.out from rfl]
          rw [show (Quotient.out x :: rest.map Quotient.out).zip (b :: a_rest) =
                (Quotient.out x, b) :: (rest.map Quotient.out).zip a_rest from rfl]
          rw [show (x :: rest).zip (b :: a_rest) = (x, b) :: rest.zip a_rest from rfl]
          rw [List.filterMap_cons, List.filterMap_cons]
          cases b with
          | true =>
            -- if true then none else some = none; both sides skip.
            show (((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then none else some p.fst)).map Nonplanar.mk =
                (rest.zip a_rest).filterMap
                  (fun p => if p.snd = true then none else some p.fst)
            exact ih a_rest
          | false =>
            -- if false then none else some Q.out x = some Q.out x; on RHS some x.
            show (Quotient.out x ::
                ((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then none else some p.fst)).map Nonplanar.mk =
                x ::
                (rest.zip a_rest).filterMap
                  (fun p => if p.snd = true then none else some p.fst)
            rw [show ((Quotient.out x ::
                ((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then none else some p.fst)).map Nonplanar.mk) =
                Nonplanar.mk (Quotient.out x) ::
                  (((rest.map Quotient.out).zip a_rest).filterMap
                    (fun p => if p.snd = true then none else some p.fst)).map Nonplanar.mk from rfl]
            rw [ih a_rest]
            congr 1
            exact x.out_eq
    show (ff_tree.map Nonplanar.mk : List (Nonplanar α)) =
        ((Multiset.toList C).zip assn).filterMap (fun p => if p.snd = true then none else some p.fst)
    exact h_aux C.toList assn
  -- Step 8c.3: `(s.toList.map Q.out).map mk = s.toList` (Quotient.out_eq componentwise).
  have h_ft_canon_mk : ft_canon.map Nonplanar.mk = s_t.toList := by
    show (s_t.toList.map Quotient.out).map Nonplanar.mk = s_t.toList
    induction s_t.toList with
    | nil => rfl
    | cons hd tl ih =>
      show Nonplanar.mk (Quotient.out hd) :: ((tl.map Quotient.out).map Nonplanar.mk) =
           hd :: tl
      rw [ih]
      congr 1
      exact hd.out_eq
  have h_ff_canon_mk : ff_canon.map Nonplanar.mk = s_f.toList := by
    show (s_f.toList.map Quotient.out).map Nonplanar.mk = s_f.toList
    induction s_f.toList with
    | nil => rfl
    | cons hd tl ih =>
      show Nonplanar.mk (Quotient.out hd) :: ((tl.map Quotient.out).map Nonplanar.mk) =
           hd :: tl
      rw [ih]
      congr 1
      exact hd.out_eq
  -- Step 8c.4: Both `(ft_tree.map mk)` and `(ft_canon.map mk)` have multiset image `s_t`,
  -- hence are `Perm`-equivalent (via `Multiset.coe_eq_coe`).
  have h_ft_eq_coe : (↑(ft_tree.map Nonplanar.mk) : Multiset (Nonplanar α)) = s_t := by
    rw [h_ft_mk_eq, hs_t]
  have h_ff_eq_coe : (↑(ff_tree.map Nonplanar.mk) : Multiset (Nonplanar α)) = s_f := by
    rw [h_ff_mk_eq, hs_f]
  have h_ft_canon_eq_coe : (↑(ft_canon.map Nonplanar.mk) : Multiset (Nonplanar α)) = s_t := by
    rw [h_ft_canon_mk]; exact s_t.coe_toList
  have h_ff_canon_eq_coe : (↑(ff_canon.map Nonplanar.mk) : Multiset (Nonplanar α)) = s_f := by
    rw [h_ff_canon_mk]; exact s_f.coe_toList
  have h_ft_perm : (ft_tree.map Nonplanar.mk).Perm (ft_canon.map Nonplanar.mk) := by
    rw [← Multiset.coe_eq_coe, h_ft_eq_coe, h_ft_canon_eq_coe]
  have h_ff_perm : (ff_tree.map Nonplanar.mk).Perm (ff_canon.map Nonplanar.mk) := by
    rw [← Multiset.coe_eq_coe, h_ff_eq_coe, h_ff_canon_eq_coe]
  -- Step 8c.5: Apply guest-msform invariance to swap `RoseTree`-level guests for canonical.
  have h_iF_A : (RoseTree.Pathed.insertionForest
        (List.map Quotient.out (Multiset.toList A)) ft_tree).map msform =
      (RoseTree.Pathed.insertionForest
        (List.map Quotient.out (Multiset.toList A)) ft_canon).map msform :=
    RoseTree.Pathed.insertionForest_msform_invariance_guests _ h_ft_perm
  have h_iF_B : (RoseTree.Pathed.insertionForest
        (List.map Quotient.out (Multiset.toList B)) ff_tree).map msform =
      (RoseTree.Pathed.insertionForest
        (List.map Quotient.out (Multiset.toList B)) ff_canon).map msform :=
    RoseTree.Pathed.insertionForest_msform_invariance_guests _ h_ff_perm
  -- Step 8d: Use guest-msform invariance to align the canonical-guest form on the
  -- RHS back to the `RoseTree`-level guest form. Then both sides share `M_A` and `M_B` below.
  rw [← h_iF_A, ← h_iF_B]
  set M_A : Multiset (List (RoseTree α)) :=
    RoseTree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList A)) ft_tree with hM_A
  set M_B : Multiset (List (RoseTree α)) :=
    RoseTree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList B)) ff_tree with hM_B
  -- Step 8e: Push msform through `(M_A ×ˢ M_B)`. Both sides expand via
  -- `Multiset.product = bind` and `msform (a ++ b) = msform a + msform b`.
  show (M_A.bind (fun a => M_B.map (Prod.mk a))).map (msform ∘ fun p => p.fst ++ p.snd) =
      ((M_A.map msform).bind (fun ma => (M_B.map msform).map (Prod.mk ma))).map
        (fun p => p.fst + p.snd)
  rw [Multiset.map_bind, Multiset.map_bind, Multiset.bind_map]
  refine Multiset.bind_congr fun a _ => ?_
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intros b _
  show msform (a ++ b) = msform a + msform b
  rw [hmsform]
  show (↑((a ++ b).map Nonplanar.mk) : Multiset (Nonplanar α)) =
       ↑(a.map Nonplanar.mk) + ↑(b.map Nonplanar.mk)
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
    `Nonplanar.insertionMultiset_card_eq` specialization to a singleton host. -/
private theorem insertionMultiset_singleton_host_singleton
    (T : Nonplanar α) (G : Multiset (Nonplanar α))
    {X : Multiset (Nonplanar α)} (hX : X ∈ Nonplanar.insertionMultiset {T} G) :
    ∃ T' : Nonplanar α, X = {T'} := by
  have hcard : X.card = ({T} : Multiset (Nonplanar α)).card :=
    Nonplanar.insertionMultiset_card_eq {T} G hX
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
    (A G : Multiset (Nonplanar α)) :
    (Nonplanar.insertionMultiset A G).bind Multiset.antidiagonal =
      (Multiset.antidiagonal A).bind (fun pa =>
        (Multiset.antidiagonal G).bind (fun pg =>
          (Nonplanar.insertionMultiset pa.1 pg.1) ×ˢ
            (Nonplanar.insertionMultiset pa.2 pg.2))) := by
  induction A using Multiset.induction_on generalizing G with
  | empty =>
    -- A = 0. Case on G.
    rw [Multiset.antidiagonal_zero, Multiset.singleton_bind]
    by_cases hG : G = 0
    · -- G = 0: NIM 0 0 = {0}, antidiag 0 = {(0,0)}. RHS = NIM 0 0 ×ˢ NIM 0 0 = {(0,0)}.
      subst hG
      rw [Nonplanar.insertionMultiset_zero_right, Multiset.singleton_bind,
          Multiset.antidiagonal_zero, Multiset.singleton_bind,
          Nonplanar.insertionMultiset_zero_right]
      rfl
    · -- G ≠ 0: LHS = (NIM 0 G).bind antidiag = 0.bind = 0. RHS: each pg has at least one nonzero side.
      rw [Nonplanar.insertionMultiset_zero_left_of_ne_zero G hG, Multiset.zero_bind]
      -- RHS: prove the bind is 0 by showing each summand is 0.
      symm
      have h_rhs_eq :
          (Multiset.antidiagonal G).bind (fun pg =>
              (Nonplanar.insertionMultiset 0 pg.1) ×ˢ
              (Nonplanar.insertionMultiset 0 pg.2)) =
          (Multiset.antidiagonal G).bind (fun _ => (0 : Multiset (Multiset (Nonplanar α) ×
            Multiset (Nonplanar α)))) := by
        refine Multiset.bind_congr fun pg hpg => ?_
        have hpg_sum : pg.1 + pg.2 = G := Multiset.mem_antidiagonal.mp hpg
        by_cases h1 : pg.1 = 0
        · -- pg.1 = 0 ⇒ pg.2 = G ≠ 0.
          have h2 : pg.2 ≠ 0 := by
            intro h2eq
            apply hG
            rw [← hpg_sum, h1, h2eq]; rfl
          rw [Nonplanar.insertionMultiset_zero_left_of_ne_zero pg.2 h2,
              Multiset.product_zero]
        · rw [Nonplanar.insertionMultiset_zero_left_of_ne_zero pg.1 h1,
              Multiset.zero_product]
      rw [h_rhs_eq, Multiset.bind_zero]
  | cons T A' ih =>
    -- A = T ::ₘ A' = {T} + A'.
    have h_cons_eq : (T ::ₘ A' : Multiset (Nonplanar α)) = ({T} : Multiset _) + A' := by
      rw [Multiset.singleton_add]
    -- Step 1: Rewrite LHS via insertionMultiset_add_host.
    rw [h_cons_eq, Nonplanar.insertionMultiset_add_host {T} A' G]
    -- LHS = (G.powerset.bind (G₁ ↦ (NIM {T} G₁ ×ˢ NIM A' (G-G₁)).map (·.1+·.2))).bind antidiag
    rw [Multiset.bind_assoc]
    -- LHS = G.powerset.bind (G₁ ↦ ((NIM {T} G₁ ×ˢ NIM A' (G-G₁)).map (·.1+·.2)).bind antidiag)
    -- Step 2: Push antidiag through the .map ↦ bind, expand antidiag (X_T + X_A')
    -- via antidiagonal_singleton_add (since X_T is a singleton).
    have h_lhs_inner : ∀ G₁ : Multiset (Nonplanar α),
        (((Nonplanar.insertionMultiset {T} G₁) ×ˢ
            (Nonplanar.insertionMultiset A' (G - G₁))).map
            (fun p => p.1 + p.2)).bind Multiset.antidiagonal =
        ((Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
            (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (pA'.1, X_T + pA'.2)) +
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (X_T + pA'.1, pA'.2))) := by
      intro G₁
      -- LHS_inner: bind . map = map then bind = ... apply antidiagonal_singleton_add per X_T.
      rw [Multiset.bind_map]
      -- Goal: (NIM {T} G₁ ×ˢ NIM A' (G-G₁)).bind (p ↦ antidiag (p.1 + p.2)) = (NIM {T} G₁).bind ...
      -- Unfold ×ˢ as bind.
      show ((Nonplanar.insertionMultiset {T} G₁).bind (fun X_T =>
              (Nonplanar.insertionMultiset A' (G - G₁)).map (Prod.mk X_T))).bind
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
            (((Nonplanar.insertionMultiset {T} G₁) ×ˢ
                (Nonplanar.insertionMultiset A' (G - G₁))).map
                (fun p => p.1 + p.2)).bind Multiset.antidiagonal) =
          G.powerset.bind fun G₁ =>
            ((Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
                (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                  (Multiset.antidiagonal X_A').map
                      (fun pA' => (pA'.1, X_T + pA'.2)) +
                  (Multiset.antidiagonal X_A').map
                      (fun pA' => (X_T + pA'.1, pA'.2)))
        from Multiset.bind_congr (fun G₁ _ => h_lhs_inner G₁)]
    -- Step 3: Split LHS into two summands (T-right + T-left) using bind_add via map_add and sum_add.
    -- Strategy: each inner sum splits via bind_congr.
    have h_split_inner : ∀ G₁ : Multiset (Nonplanar α),
        ((Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
            (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (pA'.1, X_T + pA'.2)) +
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (X_T + pA'.1, pA'.2))) =
        ((Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
            (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (pA'.1, X_T + pA'.2))) +
        ((Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
            (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (X_T + pA'.1, pA'.2))) := by
      intro G₁
      -- Split each X_A' bind summand and each X_T bind summand.
      rw [← Multiset.bind_add]
      refine Multiset.bind_congr fun X_T _ => ?_
      rw [← Multiset.bind_add]
    rw [show (G.powerset.bind fun G₁ =>
            (Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
              (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (pA'.1, X_T + pA'.2)) +
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (X_T + pA'.1, pA'.2))) =
          (G.powerset.bind fun G₁ =>
            (Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
              (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (pA'.1, X_T + pA'.2))) +
          (G.powerset.bind fun G₁ =>
            (Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
              (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (X_T + pA'.1, pA'.2)))
        from by
      rw [← Multiset.bind_add]
      exact Multiset.bind_congr (fun G₁ _ => h_split_inner G₁)]
    -- Step 4: Now rewrite RHS via antidiagonal_cons split into T-right + T-left summands.
    rw [show (Multiset.antidiagonal ({T} + A' : Multiset (Nonplanar α))) =
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
              (Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
                (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                  (Multiset.antidiagonal X_A').map (fun pA' => (pA'.1, X_T + pA'.2))) =
            (G.powerset.bind fun G₁ =>
              ((Nonplanar.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        rw [Multiset.bind_bind]
        refine Multiset.bind_congr fun X_A' _ => ?_
        rw [Multiset.bind_map_comm]]
      -- 2) Apply IH on (NIM A' (G - G₁)).bind antidiag.
      rw [show (G.powerset.bind fun G₁ =>
              ((Nonplanar.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) =
            (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [ih (G - G₁)]]
      -- 3) Pull the binds inside via bind_assoc.
      rw [show (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) =
            (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (pA'.1, X_T + pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        refine Multiset.bind_congr fun pa' _ => ?_
        rw [Multiset.bind_assoc]]
      -- 4) Reorder G₁ and pa' binds (swap G.powerset and antidiag A').
      rw [show (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (pA'.1, X_T + pA'.2)) =
            (Multiset.antidiagonal A').bind fun pa' =>
              G.powerset.bind fun G₁ =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (pA'.1, X_T + pA'.2)
        from Multiset.bind_bind _ _]
      -- 5) Apply triple_partition_reindex on the G.powerset / antidiag (G - G₁) layer.
      refine Multiset.bind_congr fun pa' _ => ?_
      rw [triple_partition_reindex G
        (fun G₁ x y =>
          ((Nonplanar.insertionMultiset pa'.1 x) ×ˢ
              (Nonplanar.insertionMultiset pa'.2 y)).bind
            (fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
              fun X_T => (pA'.1, X_T + pA'.2)))]
      -- 6) Now LHS form matches RHS form (with bind_bind for G₂/X_T to T ::ₘ pa'.2 NIM).
      -- The RHS form (after bind_map): antidiag G.bind (pg ↦
      --   NIM pa'.1 pg.1 ×ˢ NIM (T ::ₘ pa'.2) pg.2).
      -- Compare with our current LHS form: antidiag G.bind (pg ↦ pg.2.powerset.bind (G₂ ↦ ...))
      refine Multiset.bind_congr fun pg _ => ?_
      -- RHS at this position: NIM pa'.1 pg.1 ×ˢ NIM (T ::ₘ pa'.2) pg.2 (after Prod.map id (cons T)).
      -- The Prod.map id (cons T) pa' has fst = pa'.1 and snd = T ::ₘ pa'.2 = {T} + pa'.2.
      -- Apply insertionMultiset_add_host on the RHS to peel {T} from the second argument.
      have h_prod_map_id : (Prod.map (id : Multiset (Nonplanar α) → _) (Multiset.cons T) pa') =
          (pa'.1, T ::ₘ pa'.2) := rfl
      rw [h_prod_map_id]
      show (pg.2.powerset.bind fun G₂ =>
              ((Nonplanar.insertionMultiset pa'.1 pg.1) ×ˢ
                  (Nonplanar.insertionMultiset pa'.2 (pg.2 - G₂))).bind
                (fun pA' => (Nonplanar.insertionMultiset {T} G₂).map
                  fun X_T => (pA'.1, X_T + pA'.2))) =
            (Nonplanar.insertionMultiset pa'.1 pg.1) ×ˢ
              (Nonplanar.insertionMultiset (T ::ₘ pa'.2) pg.2)
      -- Apply insertionMultiset_add_host to NIM (T ::ₘ pa'.2) pg.2.
      rw [show (T ::ₘ pa'.2 : Multiset (Nonplanar α)) = ({T} : Multiset _) + pa'.2 from
            (Multiset.singleton_add T pa'.2).symm,
          Nonplanar.insertionMultiset_add_host {T} pa'.2 pg.2]
      -- RHS: NIM pa'.1 pg.1 ×ˢ (pg.2.powerset.bind (G₂ ↦ (NIM {T} G₂ ×ˢ NIM pa'.2 (pg.2-G₂)).map (·.1+·.2)))
      -- Need: pg.2.powerset.bind LHS_inner = NIM pa'.1 pg.1 ×ˢ (pg.2.powerset.bind RHS_inner_form).
      -- Use s ×ˢ (t.bind f) = t.bind (b ↦ s ×ˢ f b).
      rw [show ∀ s : Multiset (Multiset (Nonplanar α)),
              ∀ tt : Multiset (Nonplanar α) → Multiset (Multiset (Nonplanar α)),
                s ×ˢ (pg.2.powerset.bind tt) =
                  pg.2.powerset.bind (fun G₂ => s ×ˢ tt G₂) from ?_]
      · refine Multiset.bind_congr fun G₂ _ => ?_
        -- Goal: ((NIM pa'.1 pg.1) ×ˢ NIM pa'.2 (pg.2-G₂)).bind (pA' ↦ NIM {T} G₂.map (X_T ↦ (pA'.1, X_T + pA'.2)))
        --     = NIM pa'.1 pg.1 ×ˢ ((NIM {T} G₂ ×ˢ NIM pa'.2 (pg.2-G₂)).map (·.1+·.2))
        -- Both sides describe pairs (Y₁, X_T + Y₂) for (Y₁, Y₂, X_T) ∈
        -- NIM pa'.1 pg.1 × NIM pa'.2 (pg.2-G₂) × NIM {T} G₂.
        -- Unfold ×ˢ as bind on both sides.
        show ((Nonplanar.insertionMultiset pa'.1 pg.1).bind (fun Y₁ =>
              (Nonplanar.insertionMultiset pa'.2 (pg.2 - G₂)).map (Prod.mk Y₁))).bind
                (fun pA' => (Nonplanar.insertionMultiset {T} G₂).map
                  fun X_T => (pA'.1, X_T + pA'.2)) =
              (Nonplanar.insertionMultiset pa'.1 pg.1).bind (fun Y₁ =>
                (((Nonplanar.insertionMultiset {T} G₂).bind fun X_T =>
                  (Nonplanar.insertionMultiset pa'.2 (pg.2 - G₂)).map (Prod.mk X_T)).map
                    (fun p => p.1 + p.2)).map (Prod.mk Y₁))
        rw [Multiset.bind_assoc]
        refine Multiset.bind_congr fun Y₁ _ => ?_
        rw [Multiset.bind_map]
        -- Compose the outer (Prod.mk Y₁) and (·.1+·.2) maps + push through bind.
        rw [Multiset.map_map, Multiset.map_bind]
        -- Inside each X_T, compose Prod.mk X_T with (Y₁, ·.1+·.2): Y₂ ↦ (Y₁, X_T + Y₂).
        rw [show ((Nonplanar.insertionMultiset {T} G₂).bind fun X_T =>
                Multiset.map ((Prod.mk Y₁) ∘
                    fun p : Multiset (Nonplanar α) × Multiset (Nonplanar α) => p.1 + p.2)
                  (Multiset.map (Prod.mk X_T)
                    (Nonplanar.insertionMultiset pa'.2 (pg.2 - G₂)))) =
              ((Nonplanar.insertionMultiset {T} G₂).bind fun X_T =>
                (Nonplanar.insertionMultiset pa'.2 (pg.2 - G₂)).map
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
              (Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
                (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                  (Multiset.antidiagonal X_A').map (fun pA' => (X_T + pA'.1, pA'.2))) =
            (G.powerset.bind fun G₁ =>
              ((Nonplanar.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        rw [Multiset.bind_bind]
        refine Multiset.bind_congr fun X_A' _ => ?_
        rw [Multiset.bind_map_comm]]
      rw [show (G.powerset.bind fun G₁ =>
              ((Nonplanar.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) =
            (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [ih (G - G₁)]]
      rw [show (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) =
            (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (X_T + pA'.1, pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        refine Multiset.bind_congr fun pa' _ => ?_
        rw [Multiset.bind_assoc]]
      rw [show (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (X_T + pA'.1, pA'.2)) =
            (Multiset.antidiagonal A').bind fun pa' =>
              G.powerset.bind fun G₁ =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (X_T + pA'.1, pA'.2)
        from Multiset.bind_bind _ _]
      -- For T-left RHS: antidiag G.bind (pg ↦ NIM (T ::ₘ pa'.1) pg.1 ×ˢ NIM pa'.2 pg.2).
      -- Symmetry: T attaches to the *first* host part. Apply triple_partition_reindex_flip.
      refine Multiset.bind_congr fun pa' _ => ?_
      rw [triple_partition_reindex_flip G
        (fun G₁ x y =>
          ((Nonplanar.insertionMultiset pa'.1 x) ×ˢ
              (Nonplanar.insertionMultiset pa'.2 y)).bind
            (fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
              fun X_T => (X_T + pA'.1, pA'.2)))]
      refine Multiset.bind_congr fun pg _ => ?_
      have h_prod_map_id : (Prod.map (Multiset.cons T) (id : Multiset (Nonplanar α) → _) pa') =
          (T ::ₘ pa'.1, pa'.2) := rfl
      rw [h_prod_map_id]
      show (pg.1.powerset.bind fun G₂ =>
              ((Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)) ×ˢ
                  (Nonplanar.insertionMultiset pa'.2 pg.2)).bind
                (fun pA' => (Nonplanar.insertionMultiset {T} G₂).map
                  fun X_T => (X_T + pA'.1, pA'.2))) =
            (Nonplanar.insertionMultiset (T ::ₘ pa'.1) pg.1) ×ˢ
              (Nonplanar.insertionMultiset pa'.2 pg.2)
      -- Apply insertionMultiset_add_host on NIM (T ::ₘ pa'.1) pg.1.
      rw [show (T ::ₘ pa'.1 : Multiset (Nonplanar α)) = ({T} : Multiset _) + pa'.1 from
            (Multiset.singleton_add T pa'.1).symm,
          Nonplanar.insertionMultiset_add_host {T} pa'.1 pg.1]
      -- RHS: (pg.1.powerset.bind (G₂ ↦ (NIM {T} G₂ ×ˢ NIM pa'.1 (pg.1-G₂)).map (·.1+·.2))) ×ˢ NIM pa'.2 pg.2
      -- Use (s.bind f) ×ˢ t = s.bind (a ↦ f a ×ˢ t).
      rw [show ∀ s : Multiset (Multiset (Nonplanar α)),
              ∀ tt : Multiset (Nonplanar α) → Multiset (Multiset (Nonplanar α)),
                (pg.1.powerset.bind tt) ×ˢ s =
                  pg.1.powerset.bind (fun G₂ => tt G₂ ×ˢ s) from ?_]
      · refine Multiset.bind_congr fun G₂ _ => ?_
        -- Goal: ((NIM pa'.1 (pg.1-G₂)) ×ˢ NIM pa'.2 pg.2).bind (pA' ↦ NIM {T} G₂.map (X_T ↦ (X_T + pA'.1, pA'.2)))
        --     = ((NIM {T} G₂ ×ˢ NIM pa'.1 (pg.1-G₂)).map (·.1+·.2)) ×ˢ NIM pa'.2 pg.2
        -- Unfold ×ˢ everywhere.
        show ((Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind (fun Y₁ =>
              (Nonplanar.insertionMultiset pa'.2 pg.2).map (Prod.mk Y₁))).bind
                (fun pA' => (Nonplanar.insertionMultiset {T} G₂).map
                  fun X_T => (X_T + pA'.1, pA'.2)) =
            (Multiset.map (fun p : Multiset (Nonplanar α) × Multiset (Nonplanar α) => p.1 + p.2)
                ((Nonplanar.insertionMultiset {T} G₂).bind (fun X_T =>
                  (Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).map (Prod.mk X_T)))).bind
              (fun first => (Nonplanar.insertionMultiset pa'.2 pg.2).map (Prod.mk first))
        -- Reformulate LHS: bind, bind_map, bind.
        rw [Multiset.bind_assoc]
        -- Goal: NIM pa'.1 (pg.1-G₂).bind (Y₁ ↦ ((NIM pa'.2 pg.2).map (Prod.mk Y₁)).bind (pA' ↦ NIM {T} G₂.map (...)))
        rw [show ((Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind (fun Y₁ =>
                ((Nonplanar.insertionMultiset pa'.2 pg.2).map (Prod.mk Y₁)).bind
                  (fun pA' => (Nonplanar.insertionMultiset {T} G₂).map
                    fun X_T => (X_T + pA'.1, pA'.2)))) =
              (Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind (fun Y₁ =>
                (Nonplanar.insertionMultiset pa'.2 pg.2).bind (fun Y₂ =>
                  (Nonplanar.insertionMultiset {T} G₂).map
                    fun X_T => (X_T + Y₁, Y₂))) from by
          refine Multiset.bind_congr fun Y₁ _ => ?_
          rw [Multiset.bind_map]]
        -- RHS: Push map p.1+p.2 through inner bind, then bind outer.
        rw [show (Multiset.map (fun p : Multiset (Nonplanar α) × Multiset (Nonplanar α) =>
                  p.1 + p.2)
                ((Nonplanar.insertionMultiset {T} G₂).bind (fun X_T =>
                  (Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).map (Prod.mk X_T)))).bind
              (fun first => (Nonplanar.insertionMultiset pa'.2 pg.2).map (Prod.mk first)) =
              ((Nonplanar.insertionMultiset {T} G₂).bind fun X_T =>
                (Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind fun Y₁ =>
                  (Nonplanar.insertionMultiset pa'.2 pg.2).map (fun Y₂ => (X_T + Y₁, Y₂)))
            from by
          rw [Multiset.map_bind, Multiset.bind_assoc]
          refine Multiset.bind_congr fun X_T _ => ?_
          rw [Multiset.map_map, Multiset.bind_map]
          refine Multiset.bind_congr fun Y₁ _ => ?_
          rfl]
        -- Now LHS: NIM pa'.1.bind (Y₁ ↦ NIM pa'.2.bind (Y₂ ↦ NIM {T} G₂.map (X_T ↦ (X_T + Y₁, Y₂))))
        -- RHS: NIM {T} G₂.bind (X_T ↦ NIM pa'.1.bind (Y₁ ↦ NIM pa'.2.map (Y₂ ↦ (X_T + Y₁, Y₂))))
        -- Step a: Apply bind_map_comm to swap Y₂ and X_T inside Y₁.
        rw [show ((Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind fun Y₁ =>
              (Nonplanar.insertionMultiset pa'.2 pg.2).bind (fun Y₂ =>
                (Nonplanar.insertionMultiset {T} G₂).map fun X_T => (X_T + Y₁, Y₂))) =
            ((Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind fun Y₁ =>
              (Nonplanar.insertionMultiset {T} G₂).bind (fun X_T =>
                (Nonplanar.insertionMultiset pa'.2 pg.2).map fun Y₂ => (X_T + Y₁, Y₂)))
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

end RoseTree.Nonplanar
