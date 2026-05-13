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

`[UPSTREAM]` candidate. Substrate scaffold + base/edge cases sorry-free.
The `assocBucketSum_eq_insertionForest_iterated_msform` theorem has 1 sorry
remaining: the deepest combinatorial case (`host_A`, `guests_B`, `guests_C`
all non-empty). Strategy outlined in the theorem's docstring.
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

/-- `assocBucketSum` as a `kBucketSum` instance: 2 buckets indexed by `Bool`,
    iterated-bind leaf (true → A-bucket, false → B-bucket). -/
theorem assocBucketSum_eq_kBucketSum
    (host_A host_B pre_A pre_B Ts : List (Planar α)) :
    assocBucketSum host_A host_B pre_A pre_B Ts =
      kBucketSum [true, false]
        (fun pres' =>
          (insertionForest host_B (pres' false)).bind fun X' =>
            insertionForest host_A (X' ++ pres' true))
        (fun b => if b then pre_A else pre_B) Ts := by
  induction Ts generalizing pre_A pre_B with
  | nil =>
    rw [assocBucketSum_nil_remaining, kBucketSum_nil_remaining]
    simp
  | cons x rest ih =>
    rw [assocBucketSum_cons_remaining, kBucketSum_cons_remaining]
    refine Multiset.bind_congr fun b _ => ?_
    cases b with
    | true =>
      rw [if_pos rfl, ih]
      congr 1
      funext c
      cases c <;> simp [Function.update_self]
    | false =>
      rw [if_neg (by decide : (false : Bool) ≠ true), ih]
      congr 1
      funext c
      cases c <;> simp [Function.update_self]

/-! ## §1.5: 4-bucket aggregator `iteratedQuadSum`

LHS-side substrate for the deep case of
`assocBucketSum_eq_insertionForest_iterated_msform`. The LHS form
`(insertionForest host_A guests_B).bind (fun X => insertionForest X guests_C)`
in the deep case `host_A = T :: F_A` admits a 4-bucket refinement of
`guests_C`: each γ_C-guest lands at a vertex of `T_ins :: F_ins` (the
B-grafted result), which is one of:
- T's A-original vertices (T_orig bucket — siblings of pre_T_B at T)
- T's B-grafted vertices (T_graft bucket — inside one of pre_T_B's trees)
- F_A's A-original vertices (FA_orig bucket — siblings of pre_FA_B in F_A)
- F_A's B-grafted vertices (FA_graft bucket — inside one of pre_FA_B's trees)

The vertex-provenance comes from `vertices_multiGraft_decomp` (Graft.lean
§9): T_ins = `multiGraft T (something derived from pre_T_B)` partitions its
vertex set into preserved (A-original siblings), sourceSelf (A-original
B-graft targets), and lifted (inside B-trees).

`iteratedQuadSum` is the bucket-sum in this 4-bucket form. The leaf form
expresses the LHS computation: first insert T_graft-bucket guests into
pre_T_B (giving modified B-trees pre_T_B'), then insert pre_T_B' ++
T_orig-bucket guests into T's vertices; symmetrically for F_A.

Bridges:
- `iteratedQuadSum_eq_assocBucketSum` (A3.2, TODO) — RHS bridge.
- `iteratedQuadSum_eq_LHS_msform` (A3.3, TODO) — LHS bridge.
- Combined to close the deep case (A3.4, TODO). -/

/-- 4-bucket index for `iteratedQuadSum`. Each γ_C-guest assigns to one
    bucket; the leaf computes the corresponding LHS form. -/
private inductive QuadIdx where
  | T_orig   : QuadIdx
  | T_graft  : QuadIdx
  | FA_orig  : QuadIdx
  | FA_graft : QuadIdx
deriving DecidableEq

/-- 4-bucket aggregator: each `remaining` C-guest assigns to one of
    `T_orig`/`T_graft`/`FA_orig`/`FA_graft`. At the leaf, T_graft-bucket
    guests are first inserted into `pre_T_B` (giving modified B-trees);
    then `pre_T_B' ++ pres' T_orig` is inserted into `T`. Symmetric for
    `F_A` / `pre_FA_B`. -/
private def iteratedQuadSum (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    (QuadIdx → List (Planar α)) → List (Planar α) →
      Multiset (List (Planar α))
  | pres, [] =>
      (insertionForest pre_T_B (pres .T_graft)).bind fun pre_T_B' =>
        (insertion T (pre_T_B' ++ pres .T_orig)).bind fun T' =>
          (insertionForest pre_FA_B (pres .FA_graft)).bind fun pre_FA_B' =>
            (insertionForest F_A (pre_FA_B' ++ pres .FA_orig)).map fun F' =>
              T' :: F'
  | pres, x :: rest =>
      (Multiset.ofList [QuadIdx.T_orig, QuadIdx.T_graft,
                         QuadIdx.FA_orig, QuadIdx.FA_graft]).bind fun t =>
        iteratedQuadSum T F_A pre_T_B pre_FA_B
          (Function.update pres t (pres t ++ [x])) rest

private theorem iteratedQuadSum_nil_remaining
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (pres : QuadIdx → List (Planar α)) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B pres [] =
      (insertionForest pre_T_B (pres .T_graft)).bind fun pre_T_B' =>
        (insertion T (pre_T_B' ++ pres .T_orig)).bind fun T' =>
          (insertionForest pre_FA_B (pres .FA_graft)).bind fun pre_FA_B' =>
            (insertionForest F_A (pre_FA_B' ++ pres .FA_orig)).map fun F' =>
              T' :: F' := rfl

private theorem iteratedQuadSum_cons_remaining
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (pres : QuadIdx → List (Planar α))
    (x : Planar α) (rest : List (Planar α)) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B pres (x :: rest) =
      (Multiset.ofList [QuadIdx.T_orig, QuadIdx.T_graft,
                         QuadIdx.FA_orig, QuadIdx.FA_graft]).bind fun t =>
        iteratedQuadSum T F_A pre_T_B pre_FA_B
          (Function.update pres t (pres t ++ [x])) rest := rfl

/-- `iteratedQuadSum` as a `kBucketSum` instance: 4 buckets indexed by
    `QuadIdx`, parallel quad-bind leaf as in the definition. -/
private theorem iteratedQuadSum_eq_kBucketSum
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (pres : QuadIdx → List (Planar α)) (Ts : List (Planar α)) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B pres Ts =
      kBucketSum [QuadIdx.T_orig, QuadIdx.T_graft,
                   QuadIdx.FA_orig, QuadIdx.FA_graft]
        (fun pres' =>
          (insertionForest pre_T_B (pres' .T_graft)).bind fun pre_T_B' =>
            (insertion T (pre_T_B' ++ pres' .T_orig)).bind fun T' =>
              (insertionForest pre_FA_B (pres' .FA_graft)).bind fun pre_FA_B' =>
                (insertionForest F_A (pre_FA_B' ++ pres' .FA_orig)).map fun F' =>
                  T' :: F')
        pres Ts := by
  induction Ts generalizing pres with
  | nil => rw [iteratedQuadSum_nil_remaining, kBucketSum_nil_remaining]
  | cons x rest ih =>
    rw [iteratedQuadSum_cons_remaining, kBucketSum_cons_remaining]
    refine Multiset.bind_congr fun t _ => ?_
    exact ih (Function.update pres t (pres t ++ [x]))

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

/-! ### §2.1 Helper lemmas for the cons case -/

/-- Generalized helper: `assocBucketSum host_A [] pre_A pre_B remaining`.
    If `pre_B = []`, equals `insertionForest host_A (pre_A ++ remaining)`.
    If `pre_B ≠ []`, equals `0` (since `insertionForest [] non_empty = 0`).

    The single combined statement is via `pre_B`-case-analysis. We prove it
    via induction on `remaining`, splitting on `pre_B`'s emptiness at each step. -/
private theorem assocBucketSum_nil_guests_B_aux
    (host_A : List (Planar α)) :
    ∀ (pre_A pre_B remaining : List (Planar α)),
    assocBucketSum host_A ([] : List (Planar α)) pre_A pre_B remaining =
      (insertionForest ([] : List (Planar α)) pre_B).bind fun X' =>
        insertionForest host_A (X' ++ pre_A ++ remaining) := by
  intro pre_A pre_B remaining
  induction remaining generalizing pre_A pre_B with
  | nil =>
    rw [assocBucketSum_nil_remaining]
    refine Multiset.bind_congr fun X' _ => ?_
    rw [List.append_nil]
  | cons c rest ih =>
    rw [assocBucketSum_cons_remaining]
    rw [show (Multiset.ofList [true, false] : Multiset Bool) = (true ::ₘ false ::ₘ 0) from rfl]
    rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [if_pos rfl, if_neg (by decide : (false : Bool) ≠ true)]
    rw [ih (pre_A ++ [c]) pre_B, ih pre_A (pre_B ++ [c])]
    -- LHS = (ifd []) (X' ++ (pre_A ++ [c]) ++ rest)).bind ...
    --     + (ifd [] (pre_B ++ [c])).bind X' => ifd host_A (X' ++ pre_A ++ rest)
    -- Goal: prove this equals (ifd [] pre_B).bind X' => ifd host_A (X' ++ pre_A ++ (c :: rest))
    -- Strategy: case-split on pre_B.
    cases pre_B with
    | nil =>
      -- ifd [] [] = {[]}. (ifd [] (c :: ...)) = 0 if pre_B becomes [c]. Plus the [] case.
      -- After cases pre_B = [], pre_B ++ [c] = [c], so ifd [] [c] = 0.
      rw [show (insertionForest ([] : List (Planar α)) ([] ++ [c]) :
                Multiset (List (Planar α))) = 0 from by
          show insertionForest [] [c] = 0
          exact insertionForest_empty_host_nonempty_guests _ _]
      rw [Multiset.zero_bind, add_zero]
      rw [show (insertionForest ([] : List (Planar α))
                ([] : List (Planar α)) : Multiset (List (Planar α))) =
              (([] : List (Planar α)) ::ₘ 0) from by
            rw [insertionForest_nil_nil]; rfl]
      rw [Multiset.cons_bind, Multiset.zero_bind, add_zero,
          Multiset.cons_bind, Multiset.zero_bind, add_zero]
      rw [List.nil_append, List.nil_append]
      rw [show pre_A ++ [c] ++ rest = pre_A ++ (c :: rest) from by
            simp [List.append_assoc]]
    | cons b restB =>
      -- pre_B = b :: restB. ifd [] (b :: restB) = 0 (since pre_B is non-empty).
      rw [show (insertionForest ([] : List (Planar α)) (b :: restB) :
                Multiset (List (Planar α))) = 0 from
            insertionForest_empty_host_nonempty_guests _ _]
      rw [Multiset.zero_bind]
      rw [show (insertionForest ([] : List (Planar α)) ((b :: restB) ++ [c]) :
                Multiset (List (Planar α))) = 0 from
            insertionForest_empty_host_nonempty_guests _ _]
      rw [Multiset.zero_bind]
      rfl

/-- Helper: every element of `insertionForest (T :: F) gs` is non-empty (specifically,
    is of the form T_ins :: F_ins for some T_ins, F_ins). The proof is by induction on `gs`:
    base case `insertionForest_cons_host_nil_guests` gives `{T :: F}`, cons case
    follows from `insertionForest_cons_cons` which constructs `T_ins :: F_ins`. -/
private theorem insertionForest_cons_host_nonempty_elem
    (T : Planar α) (F gs : List (Planar α)) :
    ∀ X ∈ insertionForest (T :: F) gs, X ≠ [] := by
  induction gs generalizing T F with
  | nil =>
    intros X hX
    rw [insertionForest_cons_host_nil_guests] at hX
    rw [Multiset.mem_singleton] at hX
    rw [hX]
    exact List.cons_ne_nil _ _
  | cons g gs_rest ih =>
    intros X hX
    rw [insertionForest_cons_cons] at hX
    -- X ∈ bind α: bind T' ∈ insertion T (filter_t): (insertionForest F (filter_f)).map (T' :: ·)
    rcases Multiset.mem_bind.mp hX with ⟨α, _, hX2⟩
    rcases Multiset.mem_bind.mp hX2 with ⟨T', _, hX3⟩
    rcases Multiset.mem_map.mp hX3 with ⟨F', _, hX4⟩
    -- X = T' :: F'
    rw [← hX4]
    exact List.cons_ne_nil _ _

/-- Specialized helper: `assocBucketSum [] guests_B [] [] remaining = 0` when
    `guests_B ≠ []`. Reasoning: by assignment_rewrite, every assignment α produces
    `(insertionForest guests_B (filter_f α)).bind X' => insertionForest [] (X' ++ filter_t α)`.
    Since `guests_B = b :: restB` is non-empty, every X' ∈ insertionForest guests_B (...)
    has length ≥ 1, hence X' ++ filter_t is non-empty, hence insertionForest [] (...) = 0. -/
private theorem assocBucketSum_nil_host_nonempty_guests_B_zero
    (b : Planar α) (restB remaining : List (Planar α)) :
    assocBucketSum ([] : List (Planar α)) (b :: restB) [] [] remaining = 0 := by
  -- Generalized helper: assocBucketSum [] (b :: restB) pre_A pre_B remaining = 0.
  -- The (b :: restB) host produces X' of length ≥ 1 in any insertion.
  suffices h : ∀ (pre_A pre_B : List (Planar α)),
      assocBucketSum ([] : List (Planar α)) (b :: restB) pre_A pre_B remaining = 0 by
    exact h [] []
  intros pre_A pre_B
  induction remaining generalizing pre_A pre_B with
  | nil =>
    rw [assocBucketSum_nil_remaining]
    -- (insertionForest (b :: restB) pre_B).bind X' => insertionForest [] (X' ++ pre_A) = 0.
    -- For each X' ∈ insertionForest (b :: restB) pre_B, X' ≠ [] (by helper above).
    -- So X' ++ pre_A ≠ [], so insertionForest [] (X' ++ pre_A) = 0.
    -- Use Multiset.bind_congr to rewrite each X' to 0.
    rw [show (insertionForest (b :: restB) pre_B).bind
              (fun X' : List (Planar α) => insertionForest ([] : List (Planar α)) (X' ++ pre_A)) =
            (insertionForest (b :: restB) pre_B).bind
              (fun _ : List (Planar α) => (0 : Multiset (List (Planar α)))) from by
          refine Multiset.bind_congr fun X' hX' => ?_
          have hX'_ne : X' ≠ [] :=
            insertionForest_cons_host_nonempty_elem b restB pre_B X' hX'
          cases X' with
          | nil => exact absurd rfl hX'_ne
          | cons head tail =>
            rw [List.cons_append]
            exact insertionForest_empty_host_nonempty_guests _ _]
    rw [Multiset.bind_zero]
  | cons c rest ih =>
    rw [assocBucketSum_cons_remaining]
    rw [show (Multiset.ofList [true, false] : Multiset Bool) = (true ::ₘ false ::ₘ 0) from rfl]
    rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [if_pos rfl, if_neg (by decide : (false : Bool) ≠ true)]
    rw [ih (pre_A ++ [c]) pre_B, ih pre_A (pre_B ++ [c])]
    rfl

/-! ### §2.15 Host-routing split substrate (planar)

For a `host_B` partition into `pre_T_B = filter_t asn host_B` and
`pre_FA_B = filter_f asn host_B`, the multi-graft of `pre_B` into the
partitioned host (with per-c routing decision `sub_B`) equals the
multi-graft into the un-partitioned `host_B` (with the resulting X'
filtered by `asn`).

This is the planar-level "host-routing decomposition" lemma, the heart
of A3.2's base case. The bijection: given (sub_B, multi-graft into
pre_T_B for sub_B-true c's, multi-graft into pre_FA_B for sub_B-false
c's), the unified multi-graft into host_B yields an X' whose
`asn`-filtered components match (X_T, X_F). Conversely, each X' from
ifd host_B pre_B has a unique sub_B = (each c → asn-bit-of-tree-it-lands-in)
and decomposes via filter_t/filter_f asn.

Proof: induction on host_B with asn, pre_B, leaf-continuation
generalized. The cons step (host_B = h :: rest_h) uses
ifd_cons_assignment on both sides + IH on the recursive multi-graft into
rest_h. -/

/-! Helpers: filter_t / filter_f reductions at cons-front positions. -/

/-- `filter_t` at cons-true position prepends `c`. -/
private lemma filterMap_t_cons_true (c : Planar α) (qs : List (Planar α)) (a : List Bool) :
    ((c :: qs).zip (true :: a)).filterMap (fun p => if p.snd then some p.fst else none) =
    c :: (qs.zip a).filterMap (fun p => if p.snd then some p.fst else none) := by
  simp

/-- `filter_f` at cons-true position is unchanged (c routed to t-bucket). -/
private lemma filterMap_f_cons_true (c : Planar α) (qs : List (Planar α)) (a : List Bool) :
    ((c :: qs).zip (true :: a)).filterMap (fun p => if p.snd then none else some p.fst) =
    (qs.zip a).filterMap (fun p => if p.snd then none else some p.fst) := by
  simp

/-- `filter_t` at cons-false position is unchanged. -/
private lemma filterMap_t_cons_false (c : Planar α) (qs : List (Planar α)) (a : List Bool) :
    ((c :: qs).zip (false :: a)).filterMap (fun p => if p.snd then some p.fst else none) =
    (qs.zip a).filterMap (fun p => if p.snd then some p.fst else none) := by
  simp

/-- `filter_f` at cons-false position prepends `c`. -/
private lemma filterMap_f_cons_false (c : Planar α) (qs : List (Planar α)) (a : List Bool) :
    ((c :: qs).zip (false :: a)).filterMap (fun p => if p.snd then none else some p.fst) =
    c :: (qs.zip a).filterMap (fun p => if p.snd then none else some p.fst) := by
  simp

/-- LHS form of the 3-way partition helper. Encodes (sub_B, γ_T) over `qs`:
    each c ∈ qs is routed by (sub_B(c), γ_T(c)) into one of 3 K-buckets:
    (t, t) → bucket 1 (h), (t, f) → bucket 2 (T), (f) → bucket 3 (F). -/
private def splitPairLHSform {ω : Type*} (qs : List (Planar α))
    (K : List (Planar α) → List (Planar α) → List (Planar α) → Multiset ω) : Multiset ω :=
  (Multiset.ofList (listChoices [true, false] qs.length)).bind (fun sub_B =>
    (Multiset.ofList (listChoices [true, false]
      ((qs.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none)).length)).bind
        (fun γ_T =>
      K ((((qs.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none)).zip γ_T).filterMap
          (fun p => if p.snd then some p.fst else none))
        ((((qs.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none)).zip γ_T).filterMap
          (fun p => if p.snd then none else some p.fst))
        ((qs.zip sub_B).filterMap (fun p => if p.snd then none else some p.fst))))

/-- RHS form of the 3-way partition helper. Encodes (α', sub_B') over `qs`:
    each c ∈ qs is routed by (α'(c), sub_B'(c)) into one of 3 K-buckets:
    (t) → bucket 1 (h), (f, t) → bucket 2 (T), (f, f) → bucket 3 (F). -/
private def splitPairRHSform {ω : Type*} (qs : List (Planar α))
    (K : List (Planar α) → List (Planar α) → List (Planar α) → Multiset ω) : Multiset ω :=
  (Multiset.ofList (listChoices [true, false] qs.length)).bind (fun α' =>
    (Multiset.ofList (listChoices [true, false]
      ((qs.zip α').filterMap (fun p => if p.snd then none else some p.fst)).length)).bind
        (fun sub_B' =>
      K ((qs.zip α').filterMap (fun p => if p.snd then some p.fst else none))
        ((((qs.zip α').filterMap (fun p => if p.snd then none else some p.fst)).zip sub_B').filterMap
          (fun p => if p.snd then some p.fst else none))
        ((((qs.zip α').filterMap (fun p => if p.snd then none else some p.fst)).zip sub_B').filterMap
          (fun p => if p.snd then none else some p.fst))))

/-- LHS reduction: `splitPairLHSform (c :: rest) K` decomposes into 3 summands
    over `rest`, with `c` distributed across the 3 K-buckets. -/
private theorem splitPairLHSform_cons {ω : Type*} (c : Planar α) (rest : List (Planar α))
    (K : List (Planar α) → List (Planar α) → List (Planar α) → Multiset ω) :
    splitPairLHSform (c :: rest) K =
      splitPairLHSform rest (fun Z1 Z2 Z3 => K (c :: Z1) Z2 Z3) +
      splitPairLHSform rest (fun Z1 Z2 Z3 => K Z1 (c :: Z2) Z3) +
      splitPairLHSform rest (fun Z1 Z2 Z3 => K Z1 Z2 (c :: Z3)) := by
  unfold splitPairLHSform
  -- Peel outer sub_B via listChoices_succ_cons_bind, then split via bind_add
  rw [show (c :: rest).length = rest.length + 1 from rfl]
  rw [listChoices_succ_cons_bind]
  rw [Multiset.bind_add]
  -- (true :: sub_B) branch needs inner peel; (false :: sub_B) branch matches K_F by rfl.
  congr 1
  -- Reduce filter_t/f at (true :: sub_B) cons positions
  conv_lhs =>
    rhs; ext sub_B
    rw [filterMap_t_cons_true, filterMap_f_cons_true]
  -- Peel inner γ_T (length is c::F_t rest sub_B|.length = |F_t rest sub_B| + 1)
  conv_lhs =>
    rhs; ext sub_B
    rw [show (c :: ((rest.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none))).length =
            ((rest.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none)).length + 1 from rfl]
    rw [listChoices_succ_cons_bind]
  -- Reduce inner filter at (true/false :: γ_T_rest) cons positions
  conv_lhs =>
    rhs; ext sub_B
    rhs; ext γ_T_rest
    rw [filterMap_t_cons_true, filterMap_f_cons_true,
        filterMap_t_cons_false, filterMap_f_cons_false]
  -- Distribute via bind_add (inner γ_T_rest then outer sub_B)
  conv_lhs =>
    rhs; ext sub_B
    rw [Multiset.bind_add]
  rw [Multiset.bind_add]

/-- RHS reduction: `splitPairRHSform (c :: rest) K` decomposes into 3 summands
    over `rest`, with `c` distributed across the 3 K-buckets. -/
private theorem splitPairRHSform_cons {ω : Type*} (c : Planar α) (rest : List (Planar α))
    (K : List (Planar α) → List (Planar α) → List (Planar α) → Multiset ω) :
    splitPairRHSform (c :: rest) K =
      splitPairRHSform rest (fun Z1 Z2 Z3 => K (c :: Z1) Z2 Z3) +
      splitPairRHSform rest (fun Z1 Z2 Z3 => K Z1 (c :: Z2) Z3) +
      splitPairRHSform rest (fun Z1 Z2 Z3 => K Z1 Z2 (c :: Z3)) := by
  unfold splitPairRHSform
  rw [show (c :: rest).length = rest.length + 1 from rfl]
  rw [listChoices_succ_cons_bind]
  rw [Multiset.bind_add]
  -- Reassociate so (true :: α') branch matches K_h (rfl), (false :: α') branch matches K_T + K_F
  rw [add_assoc]
  congr 1
  -- Reduce filter_t/f at (false :: α') cons positions
  conv_lhs =>
    rhs; ext α'
    rw [filterMap_t_cons_false, filterMap_f_cons_false]
  -- Peel inner sub_B' (length is c::F_f rest α'|.length = |F_f rest α'| + 1)
  conv_lhs =>
    rhs; ext α'
    rw [show (c :: ((rest.zip α').filterMap (fun p => if p.snd then none else some p.fst))).length =
            ((rest.zip α').filterMap (fun p => if p.snd then none else some p.fst)).length + 1 from rfl]
    rw [listChoices_succ_cons_bind]
  -- Reduce inner filter at (true/false :: sub_B'_rest) cons positions
  conv_lhs =>
    rhs; ext α'
    rhs; ext sub_B'_rest
    rw [filterMap_t_cons_true, filterMap_f_cons_true,
        filterMap_t_cons_false, filterMap_f_cons_false]
  -- Distribute via bind_add (inner sub_B'_rest then outer α')
  conv_lhs =>
    rhs; ext α'
    rw [Multiset.bind_add]
  rw [Multiset.bind_add]

/-- 3-way bookkeeping helper (T-direction): the categorization
    `(sub_B, γ_T over filter_t sub_B pre_B)` ↔ `(α', sub_B' over filter_f α' pre_B)`
    on `pre_B`, where K takes (h-bucket, T_rest-bucket, F_rest-bucket).

    Each `pre_B`-c falls into one of 3 categories on each side:
    - LHS: (sub_B(c)=t, γ_T-bit=t) → c ∈ K's 1st arg
           (sub_B(c)=t, γ_T-bit=f) → c ∈ K's 2nd arg
           (sub_B(c)=f)             → c ∈ K's 3rd arg
    - RHS: (α'(c)=t)               → c ∈ K's 1st arg
           (α'(c)=f, sub_B'-bit=t) → c ∈ K's 2nd arg
           (α'(c)=f, sub_B'-bit=f) → c ∈ K's 3rd arg

    Proof: induction on `pre_B` via `splitPairLHSform_cons` / `splitPairRHSform_cons`
    decompositions and 3 IH instances. -/
private theorem split_pair_aux_T {ω : Type*} :
    ∀ (pre_B : List (Planar α))
      (K : List (Planar α) → List (Planar α) → List (Planar α) → Multiset ω),
    (Multiset.ofList (listChoices [true, false] pre_B.length)).bind (fun sub_B =>
      (Multiset.ofList (listChoices [true, false]
        ((pre_B.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none)).length)).bind
          (fun γ_T =>
        K ((((pre_B.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none)).zip γ_T).filterMap
            (fun p => if p.snd then some p.fst else none))
          ((((pre_B.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none)).zip γ_T).filterMap
            (fun p => if p.snd then none else some p.fst))
          ((pre_B.zip sub_B).filterMap (fun p => if p.snd then none else some p.fst))))
    = (Multiset.ofList (listChoices [true, false] pre_B.length)).bind (fun α' =>
        (Multiset.ofList (listChoices [true, false]
          ((pre_B.zip α').filterMap (fun p => if p.snd then none else some p.fst)).length)).bind
            (fun sub_B' =>
          K ((pre_B.zip α').filterMap (fun p => if p.snd then some p.fst else none))
            ((((pre_B.zip α').filterMap (fun p => if p.snd then none else some p.fst)).zip sub_B').filterMap
              (fun p => if p.snd then some p.fst else none))
            ((((pre_B.zip α').filterMap (fun p => if p.snd then none else some p.fst)).zip sub_B').filterMap
              (fun p => if p.snd then none else some p.fst)))) := by
  intro pre_B
  -- The inline expressions are definitionally equal to splitPairLHSform / splitPairRHSform.
  show ∀ K, splitPairLHSform pre_B K = splitPairRHSform pre_B K
  induction pre_B with
  | nil =>
    intro K
    rfl
  | cons c rest ih =>
    intro K
    have ih_h := ih (fun Z1 Z2 Z3 => K (c :: Z1) Z2 Z3)
    have ih_T := ih (fun Z1 Z2 Z3 => K Z1 (c :: Z2) Z3)
    have ih_F := ih (fun Z1 Z2 Z3 => K Z1 Z2 (c :: Z3))
    rw [splitPairLHSform_cons, ih_h, ih_T, ih_F, ← splitPairRHSform_cons]

/-- **Substrate**: host-routing decomposition at planar level.

    Bridges per-c routing decisions (sub_B) with the partition of multi-grafted
    output X' by `asn`-bit-of-host_B-position.

    Proof strategy: induction on `host_B` with asn, pre_B, leaf generalized.
    - Base case (host_B = []): asn = []; both sides reduce. For pre_B = [],
      both equal `leaf [] []`. For pre_B = c :: rest_pre, both equal `0`
      (LHS via per-sub_B vacuity, RHS via `insertionForest_empty_host_nonempty_guests`).
    - Cons case (host_B = h :: rest_h, asn = a :: asn_rest):
      - For a = true: expand `insertionForest_cons_assignment` on both sides, then
        the LHS bind structure reduces to `bind sub_B: bind γ_T: K(...)` where K
        is `(insertion h _).bind T_h => (ifd (filter_t rest_h asn_rest) _).bind F'_T_rest =>
        (ifd (filter_f rest_h asn_rest) _).bind X_F => leaf (T_h :: F'_T_rest) X_F`.
        The RHS expands to `bind α': bind T_h: bind F_rest: leaf ...` where applying
        IH on rest_h transforms `bind F_rest: leaf (filter_t F_rest asn_rest) (filter_f F_rest asn_rest)`
        into `bind sub_B': bind X_T': bind X_F': leaf X_T' X_F'`. Then
        `split_pair_aux_T` bridges (sub_B, γ_T) ↔ (α', sub_B') for the same K.
      - For a = false: symmetric, requires `split_pair_aux_F` (F-direction
        mirror of split_pair_aux_T) — bool inversion + K-arg permutation
        relates them.

    Estimated ~250-350 LOC. Deferred — substantial substrate work; closing #1
    (split_pair_aux_T) provides the LHS/RHS bridge but the surrounding
    `insertion`/`insertionForest` expansion + IH application + the F-direction
    mirror still need writing. -/
private theorem insertionForest_split_pair {ω : Type*}
    (leaf : List (Planar α) → List (Planar α) → Multiset ω) :
    ∀ (host_B : List (Planar α)) (asn : List Bool) (_ : asn.length = host_B.length)
      (pre_B : List (Planar α)),
    (Multiset.ofList (listChoices [true, false] pre_B.length)).bind (fun sub_B =>
      (insertionForest
          ((host_B.zip asn).filterMap (fun p => if p.snd then some p.fst else none))
          ((pre_B.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none))).bind fun X_T =>
        (insertionForest
            ((host_B.zip asn).filterMap (fun p => if p.snd then none else some p.fst))
            ((pre_B.zip sub_B).filterMap (fun p => if p.snd then none else some p.fst))).bind fun X_F =>
          leaf X_T X_F)
    = (insertionForest host_B pre_B).bind fun X' =>
        leaf
          ((X'.zip asn).filterMap (fun p => if p.snd then some p.fst else none))
          ((X'.zip asn).filterMap (fun p => if p.snd then none else some p.fst)) := by
  sorry

/-! ### §2.2 A3.2 — RHS bridge `assocBucketSum_eq_iteratedQuadSum_outer`

The planar bridge from the 4-bucket `iteratedQuadSum` (with an outer
`asn`-bind partitioning `host_B` into T-side and F_A-side) to the
2-bucket `assocBucketSum` form.

Generalized version with `pre_A`, `pre_B` arguments (and corresponding
`sub_A`, `sub_B` binds on the LHS) is proved by induction on `remaining`.
The base case (remaining = []) requires the **host-routing split substrate**
(currently sorry; proves a planar identity bridging
`bind sub_B: ifd pre_T_B (filter_t sub_B) ×ˢ ifd pre_FA_B (filter_f sub_B)`
to `(ifd host_B).map (fun X' => (filter_t asn X', filter_f asn X'))`).
The cons step uses listChoices_succ_append_bind to absorb the c-handling
into the sub_A/sub_B binds, matching the assocBucketSum_cons branching. -/

/-- Generalized RHS bridge: bind α: bind sub_A: bind sub_B: iteratedQuadSum
    (with sub-distributed pres) remaining = assocBucketSum (T :: F_A) host_B
    pre_A pre_B remaining. -/
private theorem assocBucketSum_eq_iteratedQuadSum_outer_gen
    (T : Planar α) (F_A host_B : List (Planar α)) :
    ∀ (pre_A pre_B remaining : List (Planar α)),
    (Multiset.ofList (listChoices [true, false] host_B.length)).bind (fun asn =>
      (Multiset.ofList (listChoices [true, false] pre_A.length)).bind fun sub_A =>
        (Multiset.ofList (listChoices [true, false] pre_B.length)).bind fun sub_B =>
          iteratedQuadSum T F_A
            ((host_B.zip asn).filterMap (fun p => if p.snd then some p.fst else none))
            ((host_B.zip asn).filterMap (fun p => if p.snd then none else some p.fst))
            (fun
              | .T_orig   => (pre_A.zip sub_A).filterMap (fun p => if p.snd then some p.fst else none)
              | .FA_orig  => (pre_A.zip sub_A).filterMap (fun p => if p.snd then none else some p.fst)
              | .T_graft  => (pre_B.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none)
              | .FA_graft => (pre_B.zip sub_B).filterMap (fun p => if p.snd then none else some p.fst))
            remaining)
    = assocBucketSum (T :: F_A) host_B pre_A pre_B remaining := by
  intro pre_A pre_B remaining
  induction remaining generalizing pre_A pre_B with
  | nil =>
    -- Base case (remaining = []): the heart of A3.2.
    -- Strategy: transform both sides to a common `bind X': bind asn: bind sub_A: leaf` form.
    -- (a) RHS: assocBucketSum_nil → ifd_cons_assignment + δ-split via listChoices_append_bind.
    -- (b) LHS: iteratedQuadSum_nil + bind_bind for inner reorder + substrate
    --     `insertionForest_split_pair` to bridge sub_B-multi-grafts with X' ∈ ifd host_B pre_B.
    -- (c) Match via bind_bind reorderings + zip_append + filterMap_append.
    --
    -- This proof requires careful bind manipulation; the substrate
    -- `insertionForest_split_pair` is the planar-level identity it rests on.
    -- TODO: complete after substrate is closed.
    sorry
  | cons c rest ih =>
    -- Cons step: branch γ_c on LHS (4 options) ↔ branch β_c on RHS (2 options) ×
    -- sub-bit absorbed into sub_A or sub_B. Uses listChoices_succ_append_bind.
    --
    -- Step 1: Apply assocBucketSum_cons on RHS, then IH on each branch.
    rw [assocBucketSum_cons_remaining]
    rw [show (Multiset.ofList ([true, false] : List Bool) : Multiset Bool) =
            (true ::ₘ false ::ₘ 0) from rfl]
    rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [if_pos rfl, if_neg (by decide : (false : Bool) ≠ true)]
    rw [← ih (pre_A ++ [c]) pre_B, ← ih pre_A (pre_B ++ [c])]
    -- Goal: LHS_gen pre_A pre_B (c :: rest)
    --     = LHS_gen (pre_A ++ [c]) pre_B rest + LHS_gen pre_A (pre_B ++ [c]) rest
    --
    -- Step 2: Pull the asn-bind out via bind_add.
    rw [← Multiset.bind_add]
    refine Multiset.bind_congr fun asn _ => ?_
    -- Goal at this asn: bind sub_A: bind sub_B: iteratedQuadSum (c :: rest)
    --                 = (bind sub_A' over (pre_A++[c]).length: bind sub_B: iQS rest)
    --                 + (bind sub_A: bind sub_B' over (pre_B++[c]).length: iQS rest)
    --
    -- Step 3: Expand iteratedQuadSum_cons on LHS, distributing the 4 QuadIdx branches.
    conv_lhs =>
      rhs; ext sub_A; rhs; ext sub_B
      rw [iteratedQuadSum_cons_remaining]
      rw [show (Multiset.ofList [QuadIdx.T_orig, QuadIdx.T_graft,
                                  QuadIdx.FA_orig, QuadIdx.FA_graft] : Multiset QuadIdx) =
              QuadIdx.T_orig ::ₘ QuadIdx.T_graft ::ₘ QuadIdx.FA_orig ::ₘ QuadIdx.FA_graft ::ₘ 0
              from rfl]
      rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.cons_bind, Multiset.cons_bind,
          Multiset.zero_bind, add_zero]
    -- LHS = bind sub_A: bind sub_B: T_orig + (T_graft + (FA_orig + FA_graft))
    -- (right-associated due to cons_bind expansion)
    --
    -- Step 4: Reorder summands as (T_orig + FA_orig) + (T_graft + FA_graft) and distribute binds.
    conv_lhs =>
      rhs; ext sub_A; rhs; ext sub_B
      rw [show ∀ (X1 X2 X3 X4 : Multiset (List (Planar α))),
              X1 + (X2 + (X3 + X4)) = (X1 + X3) + (X2 + X4) from by intros; abel]
    conv_lhs =>
      rhs; ext sub_A
      rw [Multiset.bind_add]
    rw [Multiset.bind_add]
    -- LHS = (A-side: bind sub_A: bind sub_B: T_orig + FA_orig)
    --     + (B-side: bind sub_A: bind sub_B: T_graft + FA_graft)
    --
    -- Step 5: Match A-side with extended-pre_A; B-side with extended-pre_B.
    refine congr_arg₂ (· + ·) ?_ ?_
    · -- A-side bridge:
      -- Goal: bind sub_A: bind sub_B: (T_orig_summand + FA_orig_summand)
      --     = bind sub_A' (over (pre_A++[c]).length): bind sub_B: iQS-with-(sub_A',pre_A++[c],sub_B,pre_B) rest
      -- Strategy: rewrite (pre_A++[c]).length = pre_A.length + 1, apply
      -- listChoices_succ_append_bind in reverse, then match each branch.
      rw [show ((pre_A ++ [c] : List (Planar α)).length : Nat) = pre_A.length + 1 from by simp]
      rw [listChoices_succ_append_bind pre_A.length]
      refine Multiset.bind_congr fun sub_A hsub_A => ?_
      have hsub_A_len : sub_A.length = pre_A.length := mem_listChoices_bool_length _ _ hsub_A
      rw [Multiset.bind_add]
      refine congr_arg₂ (· + ·) ?_ ?_
      · -- T_orig_summand = bind sub_B: iQS-with-(sub_A++[t], pre_A++[c], sub_B, pre_B) rest
        refine Multiset.bind_congr fun sub_B _ => ?_
        congr 1
        funext bucket
        -- Show pres-update for T_orig matches pres_quad with sub_A++[t], pre_A++[c]
        cases bucket
        case T_orig =>
          simp only [Function.update_self]
          -- F_t sub_A pre_A ++ [c] = F_t (sub_A ++ [t]) (pre_A ++ [c])
          rw [show (pre_A ++ [c]).zip (sub_A ++ [true]) = pre_A.zip sub_A ++ [(c, true)] from by
              rw [List.zip_append (by omega : pre_A.length = sub_A.length)]; rfl]
          rw [List.filterMap_append]
          rfl
        case T_graft =>
          rw [Function.update_of_ne (by decide : QuadIdx.T_graft ≠ QuadIdx.T_orig)]
        case FA_orig =>
          rw [Function.update_of_ne (by decide : QuadIdx.FA_orig ≠ QuadIdx.T_orig)]
          -- F_f sub_A pre_A = F_f (sub_A ++ [t]) (pre_A ++ [c])
          rw [show (pre_A ++ [c]).zip (sub_A ++ [true]) = pre_A.zip sub_A ++ [(c, true)] from by
              rw [List.zip_append (by omega : pre_A.length = sub_A.length)]; rfl]
          rw [List.filterMap_append]
          simp
        case FA_graft =>
          rw [Function.update_of_ne (by decide : QuadIdx.FA_graft ≠ QuadIdx.T_orig)]
      · -- FA_orig_summand = bind sub_B: iQS-with-(sub_A++[f], pre_A++[c], sub_B, pre_B) rest
        refine Multiset.bind_congr fun sub_B _ => ?_
        congr 1
        funext bucket
        cases bucket
        case T_orig =>
          rw [Function.update_of_ne (by decide : QuadIdx.T_orig ≠ QuadIdx.FA_orig)]
          -- F_t sub_A pre_A = F_t (sub_A ++ [f]) (pre_A ++ [c])
          rw [show (pre_A ++ [c]).zip (sub_A ++ [false]) = pre_A.zip sub_A ++ [(c, false)] from by
              rw [List.zip_append (by omega : pre_A.length = sub_A.length)]; rfl]
          rw [List.filterMap_append]
          simp
        case T_graft =>
          rw [Function.update_of_ne (by decide : QuadIdx.T_graft ≠ QuadIdx.FA_orig)]
        case FA_orig =>
          simp only [Function.update_self]
          -- F_f sub_A pre_A ++ [c] = F_f (sub_A ++ [f]) (pre_A ++ [c])
          rw [show (pre_A ++ [c]).zip (sub_A ++ [false]) = pre_A.zip sub_A ++ [(c, false)] from by
              rw [List.zip_append (by omega : pre_A.length = sub_A.length)]; rfl]
          rw [List.filterMap_append]
          rfl
        case FA_graft =>
          rw [Function.update_of_ne (by decide : QuadIdx.FA_graft ≠ QuadIdx.FA_orig)]
    · -- B-side bridge: symmetric to A-side, with pre_B/sub_B and T_graft/FA_graft.
      -- Goal: bind sub_A: bind sub_B: (T_graft_summand + FA_graft_summand)
      --     = bind sub_A: bind sub_B' (over (pre_B++[c]).length): iQS-with-(sub_A,pre_A,sub_B',pre_B++[c]) rest
      rw [show ((pre_B ++ [c] : List (Planar α)).length : Nat) = pre_B.length + 1 from by simp]
      refine Multiset.bind_congr fun sub_A hsub_A => ?_
      have hsub_A_len : sub_A.length = pre_A.length := mem_listChoices_bool_length _ _ hsub_A
      rw [listChoices_succ_append_bind pre_B.length]
      simp only [Multiset.bind_add]
      refine congr_arg₂ (· + ·) ?_ ?_
      · -- T_graft_summand = bind sub_B: iQS-with-(sub_A, pre_A, sub_B++[t], pre_B++[c]) rest
        refine Multiset.bind_congr fun sub_B hsub_B => ?_
        have hsub_B_len : sub_B.length = pre_B.length := mem_listChoices_bool_length _ _ hsub_B
        congr 1
        funext bucket
        cases bucket
        case T_orig =>
          rw [Function.update_of_ne (by decide : QuadIdx.T_orig ≠ QuadIdx.T_graft)]
        case T_graft =>
          simp only [Function.update_self]
          -- F_t sub_B pre_B ++ [c] = F_t (sub_B ++ [t]) (pre_B ++ [c])
          rw [show (pre_B ++ [c]).zip (sub_B ++ [true]) = pre_B.zip sub_B ++ [(c, true)] from by
              rw [List.zip_append (by omega : pre_B.length = sub_B.length)]; rfl]
          rw [List.filterMap_append]
          rfl
        case FA_orig =>
          rw [Function.update_of_ne (by decide : QuadIdx.FA_orig ≠ QuadIdx.T_graft)]
        case FA_graft =>
          rw [Function.update_of_ne (by decide : QuadIdx.FA_graft ≠ QuadIdx.T_graft)]
          -- F_f sub_B pre_B = F_f (sub_B ++ [t]) (pre_B ++ [c])
          rw [show (pre_B ++ [c]).zip (sub_B ++ [true]) = pre_B.zip sub_B ++ [(c, true)] from by
              rw [List.zip_append (by omega : pre_B.length = sub_B.length)]; rfl]
          rw [List.filterMap_append]
          simp
      · -- FA_graft_summand = bind sub_B: iQS-with-(sub_A, pre_A, sub_B++[f], pre_B++[c]) rest
        refine Multiset.bind_congr fun sub_B hsub_B => ?_
        have hsub_B_len : sub_B.length = pre_B.length := mem_listChoices_bool_length _ _ hsub_B
        congr 1
        funext bucket
        cases bucket
        case T_orig =>
          rw [Function.update_of_ne (by decide : QuadIdx.T_orig ≠ QuadIdx.FA_graft)]
        case T_graft =>
          rw [Function.update_of_ne (by decide : QuadIdx.T_graft ≠ QuadIdx.FA_graft)]
          -- F_t sub_B pre_B = F_t (sub_B ++ [f]) (pre_B ++ [c])
          rw [show (pre_B ++ [c]).zip (sub_B ++ [false]) = pre_B.zip sub_B ++ [(c, false)] from by
              rw [List.zip_append (by omega : pre_B.length = sub_B.length)]; rfl]
          rw [List.filterMap_append]
          simp
        case FA_orig =>
          rw [Function.update_of_ne (by decide : QuadIdx.FA_orig ≠ QuadIdx.FA_graft)]
        case FA_graft =>
          simp only [Function.update_self]
          -- F_f sub_B pre_B ++ [c] = F_f (sub_B ++ [f]) (pre_B ++ [c])
          rw [show (pre_B ++ [c]).zip (sub_B ++ [false]) = pre_B.zip sub_B ++ [(c, false)] from by
              rw [List.zip_append (by omega : pre_B.length = sub_B.length)]; rfl]
          rw [List.filterMap_append]
          rfl

/-- A3.2 specialized: `pre_A = pre_B = []` collapses sub_A and sub_B binds. -/
private theorem assocBucketSum_eq_iteratedQuadSum_outer
    (T : Planar α) (F_A host_B remaining : List (Planar α)) :
    (Multiset.ofList (listChoices [true, false] host_B.length)).bind (fun asn =>
      iteratedQuadSum T F_A
        ((host_B.zip asn).filterMap (fun p => if p.snd then some p.fst else none))
        ((host_B.zip asn).filterMap (fun p => if p.snd then none else some p.fst))
        (fun _ => []) remaining)
    = assocBucketSum (T :: F_A) host_B [] [] remaining := by
  have h := assocBucketSum_eq_iteratedQuadSum_outer_gen T F_A host_B [] [] remaining
  -- LHS of `h` has triple-bind: bind asn: bind sub_A (over []): bind sub_B (over []): leaf.
  -- For pre_A = pre_B = [], listChoices [t,f] 0 = [[]], so sub_A = sub_B = [].
  -- The sub_A/sub_B binds collapse to single-element binds, and the pres simplifies to (fun _ => []).
  -- We need to bridge LHS_specific = LHS_gen [] [] [], then chain via h.
  rw [← h]
  refine Multiset.bind_congr fun asn _ => ?_
  -- LHS at this asn: iteratedQuadSum T F_A pre_T_B pre_FA_B (fun _ => []) remaining
  -- LHS_gen at this asn: bind sub_A (over []): bind sub_B (over []): iteratedQuadSum (with sub-distributed pres) remaining
  -- Both reduce since listChoices [t,f] 0 = [[]] and the empty filterMaps give (fun _ => []) for the pres.
  simp only [List.length_nil, listChoices_zero]
  rw [show (Multiset.ofList ([[]] : List (List Bool)) : Multiset (List Bool)) =
          (([] : List Bool) ::ₘ 0) from rfl,
      Multiset.cons_bind, Multiset.zero_bind, add_zero,
      Multiset.cons_bind, Multiset.zero_bind, add_zero]
  -- Now both sides have iteratedQuadSum with possibly-different pres values.
  -- Show pres is equal: filter_t [] [] = filter_f [] [] = []. So all 4 buckets are [].
  congr 1
  funext bucket
  cases bucket <;> simp

/-- The headline planar identity AT THE MSFORM LEVEL. Iterated multi-graft
    equals the iterated bucket-sum form, modulo the multiset-of-multiset
    wrapping `Multiset.ofList ∘ List.map mk`.

    **CRITICAL**: this identity does NOT hold at the planar level (the
    LIST structure of outputs differs between LHS and RHS — different
    β-choices in LHS produce different planar arrangements that only
    coincide at the multiset level after host-Perm). The msform wrapping
    discards the planar-position information, making the identity hold.

    Proof status:
    - **Base case** `guests_C = []`: sorry-free. Both sides reduce to
      `(insertionForest host_A guests_B).map msform`.
    - **Sub-case** `guests_C ≠ []` with `guests_B = []`: sorry-free, via
      `assocBucketSum_nil_guests_B_aux` (helper proves
      `assocBucketSum host_A [] [] [] guests_C = insertionForest host_A guests_C`).
    - **Sub-case** `guests_C ≠ []`, `guests_B ≠ []`, `host_A = []`: sorry-free,
      via `assocBucketSum_nil_host_nonempty_guests_B_zero` (both sides are 0).
    - **Deepest case** `guests_C ≠ []`, `guests_B ≠ []`, `host_A ≠ []`:
      **deferred**. Requires the triple-bucket aggregator
      `iteratedTripleSum host_A guests_B pre_t pre_f remaining` paralleling
      `hostTripleSum`, plus bridges:
        - `iteratedTripleSum_eq_assocBucketSum`: shape parallel to
          `hostBucketSum_eq_hostTripleSum_aux`.
        - `iteratedTripleSum_eq_LHS_msform`: NEW bridge requiring host-Perm at
          msform level + guest-msform invariance.
      Estimated 200-400 LOC of additional substrate.

    The bijection between (β, γ) pairs (LHS) and (α, β', β'') tuples
    (RHS) is conceptually:
    - β = LHS B-assignment to host_A's vertices.
    - γ = LHS C-assignment to vertices of X = host_A-with-B-grafted.
    - α = RHS C-side decision (filter_t vs filter_f for each C-guest).
    - β' = RHS C-going-to-B assignment (filter_f-guests into guests_B's vertices).
    - β'' = RHS combined-forest assignment (X' ++ filter_t into host_A's vertices). -/
theorem assocBucketSum_eq_insertionForest_iterated_msform
    (host_A guests_B guests_C : List (Planar α)) :
    ((insertionForest host_A guests_B).bind
        (fun X => insertionForest X guests_C)).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    (assocBucketSum host_A guests_B [] [] guests_C).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- Strategy: handle the easy cases (guests_C = [] OR guests_B = [] OR host_A = [])
  -- via direct unfolding. The general case is the combinatorial heart and requires
  -- a triple-bucket aggregator (deferred).
  cases guests_C with
  | nil =>
    -- LHS: bind X => insertionForest X [] = bind X => {X} = identity
    have hLHS_inner : (fun X : List (Planar α) => insertionForest X []) =
        (fun X => ({X} : Multiset (List (Planar α)))) := by
      funext X
      exact insertionForest_nil_guests X
    rw [hLHS_inner]
    rw [show ((insertionForest host_A guests_B).bind
                  fun X : List (Planar α) => ({X} : Multiset (List (Planar α)))) =
              insertionForest host_A guests_B from by
          conv_lhs =>
            rw [show (fun X : List (Planar α) => ({X} : Multiset (List (Planar α)))) =
                    (fun X : List (Planar α) => (X ::ₘ 0)) from rfl]
          rw [show (fun X : List (Planar α) => (X ::ₘ 0 : Multiset (List (Planar α)))) =
                  (fun X : List (Planar α) => ({id X} : Multiset (List (Planar α)))) from rfl]
          rw [Multiset.bind_singleton (insertionForest host_A guests_B) id]
          exact Multiset.map_id _]
    -- RHS: assocBucketSum host_A guests_B [] [] [] = (insertionForest guests_B []).bind X' => insertionForest host_A (X' ++ [])
    rw [assocBucketSum_nil_remaining]
    rw [show (insertionForest guests_B ([] : List (Planar α)) : Multiset (List (Planar α))) =
            (guests_B ::ₘ 0) from by rw [insertionForest_nil_guests]; rfl]
    rw [Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [List.append_nil]
  | cons c rest =>
    -- General cons case (guests_C = c :: rest). Sub-case on guests_B.
    cases guests_B with
    | nil =>
      -- guests_B = []. LHS = (insertionForest host_A []).bind X => insertionForest X (c::rest)
      --                  = {host_A}.bind X => insertionForest X (c::rest)
      --                  = insertionForest host_A (c::rest).
      -- RHS = (assocBucketSum host_A [] [] [] (c::rest)).map msform.
      -- By assocBucketSum_nil_guests_B_aux: assocBucketSum host_A [] [] [] (c::rest)
      --                = (insertionForest [] []).bind X' => insertionForest host_A (X' ++ [] ++ (c::rest))
      --                = {[]}.bind X' => insertionForest host_A (X' ++ (c::rest))
      --                = insertionForest host_A (c :: rest). ✓
      rw [show (insertionForest host_A ([] : List (Planar α)) :
                Multiset (List (Planar α))) = (host_A ::ₘ 0) from by
            rw [insertionForest_nil_guests]; rfl]
      rw [Multiset.cons_bind, Multiset.zero_bind, add_zero]
      rw [assocBucketSum_nil_guests_B_aux host_A [] [] (c :: rest)]
      rw [show (insertionForest ([] : List (Planar α))
                ([] : List (Planar α)) : Multiset (List (Planar α))) =
              (([] : List (Planar α)) ::ₘ 0) from by
            rw [insertionForest_nil_nil]; rfl]
      rw [Multiset.cons_bind, Multiset.zero_bind, add_zero]
      rw [List.nil_append, List.nil_append]
    | cons b restB =>
      -- guests_B = b :: restB. Sub-case on host_A.
      cases host_A with
      | nil =>
        -- host_A = []. LHS = (insertionForest [] (b :: restB)).bind ... = 0.bind ... = 0.
        -- RHS = (assocBucketSum [] (b :: restB) [] [] (c :: rest)).map msform = 0.
        rw [insertionForest_empty_host_nonempty_guests]
        rw [Multiset.zero_bind, Multiset.map_zero]
        rw [assocBucketSum_nil_host_nonempty_guests_B_zero b restB (c :: rest)]
        rw [Multiset.map_zero]
      | cons T F_A =>
        -- host_A = T :: F_A, guests_B = b :: restB, guests_C = c :: rest.
        -- The deepest combinatorial case. The proof skeleton uses
        -- `assocBucketSum_assignment_rewrite` on the RHS to reorganize the
        -- triple bind, then bridges to the LHS via vertex-bucketing.
        --
        -- ## Detailed structure (after substrate exploration):
        --
        -- LHS expansion via `insertionForest_cons_cons` (twice):
        --   bind α_B (over [t,f]^|guests_B|): bind T_ins ∈ insertion T (filter_t α_B):
        --     bind F_ins ∈ insertionForest F_A (filter_f α_B):
        --       (insertionForest (T_ins :: F_ins) (c :: rest)).map msform
        --
        -- The inner `insertionForest (T_ins :: F_ins) (c :: rest)` re-expands
        -- via `insertionForest_cons_cons` to a γ-bind splitting c-guests
        -- across T_ins-bucket vs F_ins-bucket. After unfolding, we have a
        -- 4-fold nested bind structure (α_B × γ_C × T_ins × F_ins).
        --
        -- RHS expansion via `assocBucketSum_assignment_rewrite` then
        -- `insertionForest_cons_cons`:
        --   bind α_C: (insertionForest (b :: restB) (filter_f α_C)).bind X' =>
        --     bind β: (insertion T ((X' ++ filter_t α_C).filter_t β)).bind T'_R =>
        --     (insertionForest F_A ((X' ++ filter_t α_C).filter_f β)).map F'_R => T'_R :: F'_R
        --
        -- ## Bijection (LHS ↔ RHS at the (β, γ) ↔ (α, β', β'') level)
        --
        -- The X' enumeration on RHS captures: (filter_f α_C-guests grafted into
        -- guests_B's vertices) - this collects the c's that "go inside B".
        -- Each LHS (α_B, γ_C) configuration corresponds to:
        --   - α_C: derived from γ_C — for each c, true iff γ_C(c) is an
        --          A-original vertex of T_ins :: F_ins.
        --   - X': derived from (α_B, γ_C-restricted-to-B-side) — concretely, the
        --         B-trees with the filter_f α_C subset of γ_C grafted into them.
        --   - β: derived from α_B together with which side of T vs F_A each X'
        --        and filter_t α_C lands on.
        --
        -- The bijection is at the multiset level (after msform), not at the
        -- planar level — because LHS orders X = T_ins :: F_ins (T-side first)
        -- whereas RHS β-bucketing yields X'-trees in arbitrary planar order.
        -- The host-Perm + msform invariance (`insertionForest_perm_host_msform`,
        -- `insertionForest_msform_invariance_guests`) absorbs this.
        --
        -- ## Substrate gap — what's NOT yet built
        --
        -- 1. **`iteratedTripleSum`** — 5-bucket aggregator paralleling `hostTripleSum`:
        --    `iteratedTripleSum T F_A host_B pre_T_A pre_T_B pre_FA_A pre_FA_B pre_B remaining`
        --    where buckets are (γ_C → T-A-original, γ_C → T-B-grafted, γ_C → F_A-A-original,
        --    γ_C → F_A-B-grafted, plus α_B's split). ~100 LOC.
        --
        -- 2. **`iteratedTripleSum_eq_assocBucketSum`** — bridge to the RHS form
        --    via `hostBucketSum_eq_insertionForest`-style reasoning. ~80 LOC.
        --
        -- 3. **`iteratedTripleSum_eq_LHS_msform`** — bridge to the LHS form
        --    via host-Perm + guest-msform-invariance. ~150 LOC.
        --
        -- 4. **Final closure** — chaining the two bridges. ~30 LOC.
        --
        -- ## Why deferred
        --
        -- This is the combinatorial heart of Oudom-Guin Prop 2.7.v at the
        -- planar-list level. The substrate is mathlib-quality work
        -- (~360 LOC) — best done as a focused multi-day session rather
        -- than tacked onto an existing one. The IH-via-induction-on-`rest` /
        -- `restB` patterns don't trivially apply because the inductive case
        -- requires the same dichotomy on a smaller instance, and the IH
        -- doesn't see "X" as having vertex provenance information.
        --
        -- An alternative approach via `multiGraft`-level induction (deeper than
        -- `insertionForest_cons_cons`) might bypass the 5-bucket aggregator,
        -- but would require new substrate at the path-list level.
        --
        -- ## Downstream impact
        --
        -- This bridges to `Nonplanar.insertionMultiset_assoc` (currently sorry
        -- in `GrossmanLarsonAssoc.lean:455`). Closing the latter unblocks
        -- `insertion_assoc_shuffled` (Oudom-Guin Prop 2.7.v at the algebra
        -- level) and the GL-pre-Lie associativity chain.
        sorry

/-! ## §3: NIM-level lift to `Nonplanar.insertionMultiset_assoc`

Once the planar bridge `assocBucketSum_eq_insertionForest_iterated` lands,
the NIM-level theorem follows via:
1. Unfold NIM on both sides.
2. Apply guest-msform invariance (for the bind X => NIM X C step on LHS,
   need to show the planar X-list and the NIM-X-toList agree).
3. Apply host-Perm to align (X' + (C - C₁)).toList.map Q.out with
   X' ++ (C - C₁).toList.map Q.out.
4. Apply assocBucketSum bridge to convert iterated grafting to
   bucket form.
5. Apply powerset bridge to convert bind-over-assn to bind-over-C.powerset.

The skeleton is parallel to `Nonplanar.insertionMultiset_add_host` (Step 2)
but with a NESTED bind (NIM B C₁ inside the C.powerset.bind).

Deferred to a follow-up session — depends on the planar bridge above. -/

end Pathed

end Planar

end RootedTree
