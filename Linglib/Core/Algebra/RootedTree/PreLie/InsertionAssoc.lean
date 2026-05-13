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
