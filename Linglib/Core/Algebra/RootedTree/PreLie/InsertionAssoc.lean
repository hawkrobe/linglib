/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.InsertionAddHost
import Mathlib.Data.Multiset.Powerset

set_option autoImplicit false

/-!
# Iterated multi-graft and `insertionMultiset_assoc`

The planar substrate for `Nonplanar.insertionMultiset_assoc` (Oudom-Guin
Prop 2.7.v at the basis level): iterating multi-graft (first B into A,
then C into the result) is equivalent to a partition of C between
"going into B" and "going directly to A as siblings of B".

## Combinatorial heart

For host forests `host_A`, `guests_B`, `guests_C` (planar lists):

`(insertionForest host_A guests_B).bind (fun X => insertionForest X guests_C)`

enumerates over assignments β of `guests_B` to vertices of `host_A`,
then γ of `guests_C` to vertices of the resulting X. Each guest in
`guests_C` lands at either:
- an "A-original" vertex (in a tree of `host_A` before B was grafted), or
- a "B-grafted" vertex (in one of the inserted `guests_B` trees).

Reorganizing by this dichotomy:

`(Multiset.ofList lc).bind (fun assn =>      -- bit-vector over guests_C
    -- filter_t = guests going to A-vertices ("siblings of B" piece)
    -- filter_f = guests going to B-vertices (nested inside B's grafting)
    (insertionForest host_B (filter_f guests_C assn)).bind (fun X' =>
      insertionForest host_A (X' ++ filter_t guests_C assn)))`

This planar identity, lifted via host-Perm + guest-msform invariance +
powerset bridge (all in InsertionAddHost.lean), gives
`Nonplanar.insertionMultiset_assoc`.

## Status

`[UPSTREAM]` candidate. Substrate scaffold; proofs in flight.
-/

namespace RootedTree

namespace Planar

namespace Pathed

variable {α : Type*}

/-! ## §1: `assocBucketSum` aggregator

For each guest in `guests_C`, we decide whether it goes to an
A-vertex (true bucket, accumulated in `pre_A`) or a B-vertex (false
bucket, accumulated in `pre_B`). At the leaf, the B-bucket guests are
multi-grafted into `host_B`; the resulting X' (planar list) is then
combined with the A-bucket guests (`X' ++ pre_A`) and multi-grafted
into `host_A`.

This is the planar analog of the RHS of `Nonplanar.insertionMultiset_assoc`.
-/

/-- Iterated multi-graft aggregator: each guest of `remaining` is
    assigned to either A's bucket (`pre_A`, true bit) or B's bucket
    (`pre_B`, false bit). At the leaf, B-bucket guests are grafted
    into `host_B` (giving X'); then `X' ++ pre_A` is grafted into
    `host_A`. -/
def assocBucketSum (host_A host_B : List (Planar α)) :
    List (Planar α) → List (Planar α) → List (Planar α) →
      Multiset (List (Planar α))
  | pre_A, pre_B, []        =>
      (insertionForest host_B pre_B).bind fun X' =>
        insertionForest host_A (X' ++ pre_A)
  | pre_A, pre_B, x :: rest =>
      (Multiset.ofList [true, false]).bind fun b =>
        if b then assocBucketSum host_A host_B (pre_A ++ [x]) pre_B rest
        else assocBucketSum host_A host_B pre_A (pre_B ++ [x]) rest

theorem assocBucketSum_nil_remaining (host_A host_B pre_A pre_B : List (Planar α)) :
    assocBucketSum host_A host_B pre_A pre_B [] =
      (insertionForest host_B pre_B).bind fun X' =>
        insertionForest host_A (X' ++ pre_A) := rfl

theorem assocBucketSum_cons_remaining
    (host_A host_B pre_A pre_B : List (Planar α))
    (x : Planar α) (rest : List (Planar α)) :
    assocBucketSum host_A host_B pre_A pre_B (x :: rest) =
      (Multiset.ofList [true, false]).bind fun b =>
        if b then assocBucketSum host_A host_B (pre_A ++ [x]) pre_B rest
        else assocBucketSum host_A host_B pre_A (pre_B ++ [x]) rest := rfl

/-- Assignment-rewrite: `assocBucketSum` over remaining guests `Ts`
    equals the sum over all `[true, false]`-assignments of `Ts` of
    `assocBucketSum` on the empty remaining list with the accumulators
    augmented by the partition. Mirrors `hostBucketSum_assignment_rewrite`. -/
theorem assocBucketSum_assignment_rewrite
    (host_A host_B : List (Planar α)) :
    ∀ (pre_A pre_B Ts : List (Planar α)),
    assocBucketSum host_A host_B pre_A pre_B Ts =
      (Multiset.ofList (listChoices [true, false] Ts.length)).bind fun assn =>
        assocBucketSum host_A host_B
          (pre_A ++ (Ts.zip assn).filterMap (fun p => if p.snd then some p.fst else none))
          (pre_B ++ (Ts.zip assn).filterMap (fun p => if p.snd then none else some p.fst))
          [] := by
  intro pre_A pre_B Ts
  induction Ts generalizing pre_A pre_B with
  | nil =>
    simp [listChoices_zero, List.filterMap_nil, List.append_nil]
  | cons x rest ih =>
    rw [assocBucketSum_cons_remaining]
    conv_rhs =>
      rw [show (x :: rest).length = rest.length + 1 from rfl, listChoices_succ]
      rw [show (Multiset.ofList ([true, false].flatMap fun v =>
                  (listChoices [true, false] rest.length).map (v :: ·)) :
                Multiset (List Bool)) =
              (Multiset.ofList [true, false]).bind fun v =>
                Multiset.ofList ((listChoices [true, false] rest.length).map (v :: ·))
              from by rw [← Multiset.coe_bind]]
      rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun b _ => ?_
    cases b with
    | true =>
      rw [if_pos rfl]
      rw [show (Multiset.ofList ((listChoices [true, false] rest.length).map (true :: ·)) :
                Multiset (List Bool)) =
              (Multiset.ofList (listChoices [true, false] rest.length)).map (true :: ·)
              from rfl]
      rw [Multiset.bind_map]
      rw [ih (pre_A ++ [x]) pre_B]
      refine Multiset.bind_congr fun assn _ => ?_
      rw [List.append_assoc, List.singleton_append]
      rfl
    | false =>
      rw [if_neg (by decide : (false : Bool) ≠ true)]
      rw [show (Multiset.ofList ((listChoices [true, false] rest.length).map (false :: ·)) :
                Multiset (List Bool)) =
              (Multiset.ofList (listChoices [true, false] rest.length)).map (false :: ·)
              from rfl]
      rw [Multiset.bind_map]
      rw [ih pre_A (pre_B ++ [x])]
      refine Multiset.bind_congr fun assn _ => ?_
      rw [List.append_assoc, List.singleton_append]
      rfl

/-! ## §2: Bridge: iterated insertionForest equals assocBucketSum

The headline planar identity:
```
(insertionForest host_A guests_B).bind (fun X => insertionForest X guests_C)
  = assocBucketSum host_A host_B [] [] guests_C    -- where host_B := guests_B
```

Wait, this isn't quite right. The LHS uses `insertionForest host_A guests_B`
to graft B INTO A first, then grafts C into the result. The
`assocBucketSum` form uses `insertionForest host_B (filter_f guests_C)` —
i.e., it grafts a C-piece into a forest ALREADY denoted `host_B`. But
`host_B` here would be `guests_B` (the trees of B that we're grafting into A).

Let me restate. In the assocBucketSum, `host_B` is the FOREST whose vertices
the "going-to-B" C-guests land at. Originally, B's trees are the things
being grafted. Their VERTICES are where C-guests can land.

So `host_B := guests_B` (rename for clarity in the bridge).

The bridge claim:
```
(insertionForest host_A guests_B).bind (fun X => insertionForest X guests_C)
  = assocBucketSum host_A guests_B [] [] guests_C
```

Hmm but wait, let me re-examine assocBucketSum's leaf:
```
assocBucketSum host_A host_B pre_A pre_B [] =
  (insertionForest host_B pre_B).bind fun X' =>
    insertionForest host_A (X' ++ pre_A)
```

So `host_B` is treated as a host (its vertices are graft targets), and `pre_B` is what gets grafted INTO it. Result X' is a planar list (host_B trees with pre_B grafted).

Then `insertionForest host_A (X' ++ pre_A)` grafts (X' ++ pre_A) INTO host_A.

For the LHS bridge: we have `insertionForest host_A guests_B`. Each X is host_A with guests_B grafted at A's vertices. Hmm but X here is what's grafted-with, not the host. So we want to enumerate all γ-assignments of guests_C to X's vertices.

The reorganization: each guest of guests_C lands at either an A-original-vertex of X (corresponds to filter_t / pre_A) or a B-grafted-vertex of X (corresponds to filter_f / pre_B). The B-grafted-vertices come from guests_B's trees. So for the "going to B" piece (pre_B), it's grafted INTO the trees of guests_B (treating guests_B as a host forest).

Thus: graft pre_B into guests_B (treated as host) → X' (forest of guests_B with pre_B grafted). Then graft (X' ++ pre_A) into host_A. This matches `assocBucketSum host_A guests_B [] [] guests_C`.

So `host_B = guests_B` in the bridge. -/

/-- The headline planar identity. Iterated multi-graft equals the
    iterated bucket-sum form.

    **TODO**: Major substrate. Proof structure mirrors
    `hostBucketSum_eq_insertionForest` but for the iterated grafting.
    Likely needs:
    - A 3-bucket triple aggregator (analog to `hostTripleSum`) for the
      cons-host-A case.
    - Induction on `host_A` (treating B-grafting as a parameter). -/
theorem assocBucketSum_eq_insertionForest_iterated
    (host_A guests_B guests_C : List (Planar α)) :
    (insertionForest host_A guests_B).bind (fun X => insertionForest X guests_C) =
      assocBucketSum host_A guests_B [] [] guests_C := by
  sorry

end Pathed

end Planar

end RootedTree
