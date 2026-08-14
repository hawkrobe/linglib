/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
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


end RoseTree.Nonplanar
