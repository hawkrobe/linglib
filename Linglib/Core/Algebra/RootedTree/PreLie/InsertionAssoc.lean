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

`[UPSTREAM]` candidate. Headline theorem
`assocBucketSum_eq_insertionForest_iterated_msform` is sorry-free MODULO
the substantive A3.3 bijection (`LHS_eq_iteratedQuadSum_msform`):

- **Closed** (sorry-free): all base/edge cases of the headline; A3.1
  `insertionForest_split_pair`; A3.2 `assocBucketSum_eq_iteratedQuadSum_outer`
  (specialized + generalized); A3.4 deep case (reduced to A3.3); base case
  (C = []) of A3.3.
- **Open** (1 sorry): the cons case of A3.3 — substantive per-c bijection at
  msform level that requires path-level substrate (`vertices_multiGraft_decomp`
  + `multiGraft_perm_pair`-style argument). ~300-500 LOC of
  mathlib-quality substrate work.

Closing A3.3 unblocks `Nonplanar.insertionMultiset_assoc` and downstream
`insertion_assoc_shuffled` (Oudom-Guin Prop 2.7.v).
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

/-- Length lemma for QuadIdx-listChoices: every element of
    `listChoices [T_orig, T_graft, FA_orig, FA_graft] n` has length exactly `n`.
    Wrapper around the polymorphic `mem_listChoices_length`; used by Phase 6.1
    of the A3.3 cons-case proof to derive the length hypothesis on the α-bind
    index from membership. -/
private theorem mem_listChoices_QuadIdx_length :
    ∀ (n : Nat) (a : List QuadIdx),
    a ∈ listChoices [QuadIdx.T_orig, QuadIdx.T_graft,
                      QuadIdx.FA_orig, QuadIdx.FA_graft] n →
    a.length = n :=
  mem_listChoices_length _

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

/-! ## §1.6: flat α-bind form for `iteratedQuadSum`

Composition of `iteratedQuadSum_eq_kBucketSum` with `kBucketSum_assignment_rewrite`
gives a flat single-bind enumeration over `QuadIdx`-assignments of `C`. The
recursive 4-way bind structure collapses to one outer bind over
`α : List QuadIdx` of length `C.length`, with the leaf consuming the per-bucket
slice of `C`.

This is the RHS-side substrate for Route C of the A3.3 proof plan
(`scratch/a33_cons_plan.md`): both LHS and RHS get the same outer
`bind α : QuadIdx^|C|` skeleton, so the bijection reduces to a per-α leaf
equality at msform level. -/

/-- Flat α-bind form for `iteratedQuadSum`. Each `α : List QuadIdx` of length
    `C.length` selects, per-c, which bucket consumes that c; the leaf form
    consumes the resulting per-bucket slice of `C`. Sorry-free composition of
    `iteratedQuadSum_eq_kBucketSum` and `kBucketSum_assignment_rewrite`. -/
private theorem iteratedQuadSum_eq_alphaBind
    (T : Planar α) (F_A pre_T_B pre_FA_B C : List (Planar α)) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B (fun _ => []) C =
      (Multiset.ofList (listChoices
          [QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft]
          C.length)).bind fun a =>
        iteratedQuadSum T F_A pre_T_B pre_FA_B
          (fun t => bucketSlice C a t) [] := by
  rw [iteratedQuadSum_eq_kBucketSum, kBucketSum_assignment_rewrite]
  refine Multiset.bind_congr fun a _ => ?_
  rw [iteratedQuadSum_nil_remaining]
  simp only [List.nil_append]

/-! ## §1.7: α-constrained vertex choices (Phase 4.2 substrate, Piece 1)

Per-c choice type for enumerating γ-assignments respecting α. For each
`c ∈ C` with `α(c) = bucket`, the choice records which vertex `c` lands at in
`V(T_ins :: F_ins)`, classified by `vertices_multiGraft_decomp`'s 3-class
partition (preserved+sourceSelf vs lifted) on each of T_ins and per-F_A-tree
F_ins[i].

| Bucket   | Choice constructor            | Underlying enumeration                                                             |
|----------|-------------------------------|------------------------------------------------------------------------------------|
| T_orig   | `.t_orig (v : Path)`          | `v ∈ vertices T` (preserved+sourceSelf of T_ins, transported via choice_pre_T_B)   |
| T_graft  | `.t_graft (k) (q : Path)`     | `k < pre_T_B.length`, `q ∈ vertices (pre_T_B[k])` (lifted via liftMulti)            |
| FA_orig  | `.fa_orig (i) (v : Path)`     | `i < F_A.length`, `v ∈ vertices (F_A[i])` (preserved+sourceSelf of F_ins[i])        |
| FA_graft | `.fa_graft (k) (q : Path)`    | `k < pre_FA_B.length`, `q ∈ vertices (pre_FA_B[k])` (lifted into the assigned F_A tree) |

Per `scratch/a33_phase4_2_plan.md` Piece 1. The actual path interpretation in
`T_ins :: F_ins` (Piece 2) requires explicit T-side and F-side multi-graft
data; these inductives + enumerators are the foundational substrate. -/

/-- Per-c α-respecting choice. Each constructor encodes one of the 4 buckets
    (T_orig/T_graft/FA_orig/FA_graft) along with data identifying the vertex
    within that bucket. -/
private inductive AlphaConstrainedChoice
    (F_A pre_T_B pre_FA_B : List (Planar α)) where
  | t_orig (v : Path) : AlphaConstrainedChoice F_A pre_T_B pre_FA_B
  | t_graft (k : Fin pre_T_B.length) (q : Path) :
      AlphaConstrainedChoice F_A pre_T_B pre_FA_B
  | fa_orig (i : Fin F_A.length) (v : Path) :
      AlphaConstrainedChoice F_A pre_T_B pre_FA_B
  | fa_graft (k : Fin pre_FA_B.length) (q : Path) :
      AlphaConstrainedChoice F_A pre_T_B pre_FA_B

/-- The `QuadIdx` bucket corresponding to a choice constructor. -/
private def AlphaConstrainedChoice.bucket
    {F_A pre_T_B pre_FA_B : List (Planar α)} :
    AlphaConstrainedChoice F_A pre_T_B pre_FA_B → QuadIdx
  | .t_orig _ => QuadIdx.T_orig
  | .t_graft _ _ => QuadIdx.T_graft
  | .fa_orig _ _ => QuadIdx.FA_orig
  | .fa_graft _ _ => QuadIdx.FA_graft

/-- Enumerate all `AlphaConstrainedChoice` values whose bucket matches `b`.
    The enumeration is over the relevant vertex source list. Per-tree
    enumerations for `T_graft`, `FA_orig`, `FA_graft` use `List.finRange` to
    iterate over the tree-index. -/
private def enumAlphaConstrainedChoice
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    QuadIdx → Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)
  | QuadIdx.T_orig =>
      Multiset.ofList ((vertices T).map AlphaConstrainedChoice.t_orig)
  | QuadIdx.T_graft =>
      (Multiset.ofList (List.finRange pre_T_B.length)).bind fun k =>
        Multiset.ofList
          ((vertices (pre_T_B[k.val])).map (AlphaConstrainedChoice.t_graft k))
  | QuadIdx.FA_orig =>
      (Multiset.ofList (List.finRange F_A.length)).bind fun i =>
        Multiset.ofList
          ((vertices (F_A[i.val])).map (AlphaConstrainedChoice.fa_orig i))
  | QuadIdx.FA_graft =>
      (Multiset.ofList (List.finRange pre_FA_B.length)).bind fun k =>
        Multiset.ofList
          ((vertices (pre_FA_B[k.val])).map (AlphaConstrainedChoice.fa_graft k))

/-- Membership characterization for `enumAlphaConstrainedChoice` at each
    bucket. The equality direction matches `List.mem_map`'s output. -/
private theorem mem_enumAlphaConstrainedChoice_T_orig
    {T : Planar α} {F_A pre_T_B pre_FA_B : List (Planar α)}
    {c : AlphaConstrainedChoice F_A pre_T_B pre_FA_B} :
    c ∈ enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.T_orig ↔
      ∃ v ∈ vertices T, AlphaConstrainedChoice.t_orig (F_A := F_A)
        (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) v = c := by
  unfold enumAlphaConstrainedChoice
  rw [Multiset.mem_coe, List.mem_map]

private theorem mem_enumAlphaConstrainedChoice_T_graft
    {T : Planar α} {F_A pre_T_B pre_FA_B : List (Planar α)}
    {c : AlphaConstrainedChoice F_A pre_T_B pre_FA_B} :
    c ∈ enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.T_graft ↔
      ∃ (k : Fin pre_T_B.length) (q : Path),
        q ∈ vertices (pre_T_B[k.val]) ∧
          AlphaConstrainedChoice.t_graft (F_A := F_A) (pre_FA_B := pre_FA_B) k q = c := by
  unfold enumAlphaConstrainedChoice
  simp only [Multiset.mem_bind, Multiset.mem_coe, List.mem_finRange,
             List.mem_map, true_and]

private theorem mem_enumAlphaConstrainedChoice_FA_orig
    {T : Planar α} {F_A pre_T_B pre_FA_B : List (Planar α)}
    {c : AlphaConstrainedChoice F_A pre_T_B pre_FA_B} :
    c ∈ enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.FA_orig ↔
      ∃ (i : Fin F_A.length) (v : Path),
        v ∈ vertices (F_A[i.val]) ∧
          AlphaConstrainedChoice.fa_orig (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i v = c := by
  unfold enumAlphaConstrainedChoice
  simp only [Multiset.mem_bind, Multiset.mem_coe, List.mem_finRange,
             List.mem_map, true_and]

private theorem mem_enumAlphaConstrainedChoice_FA_graft
    {T : Planar α} {F_A pre_T_B pre_FA_B : List (Planar α)}
    {c : AlphaConstrainedChoice F_A pre_T_B pre_FA_B} :
    c ∈ enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.FA_graft ↔
      ∃ (k : Fin pre_FA_B.length) (q : Path),
        q ∈ vertices (pre_FA_B[k.val]) ∧
          AlphaConstrainedChoice.fa_graft (F_A := F_A) (pre_T_B := pre_T_B) k q = c := by
  unfold enumAlphaConstrainedChoice
  simp only [Multiset.mem_bind, Multiset.mem_coe, List.mem_finRange,
             List.mem_map, true_and]

/-- Every choice in the bucket-`b` enumeration has bucket `b`. -/
private theorem enumAlphaConstrainedChoice_bucket
    {T : Planar α} {F_A pre_T_B pre_FA_B : List (Planar α)} {b : QuadIdx}
    {c : AlphaConstrainedChoice F_A pre_T_B pre_FA_B}
    (h : c ∈ enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B b) :
    c.bucket = b := by
  cases b
  · obtain ⟨_, _, rfl⟩ := mem_enumAlphaConstrainedChoice_T_orig.mp h; rfl
  · obtain ⟨_, _, _, rfl⟩ := mem_enumAlphaConstrainedChoice_T_graft.mp h; rfl
  · obtain ⟨_, _, _, rfl⟩ := mem_enumAlphaConstrainedChoice_FA_orig.mp h; rfl
  · obtain ⟨_, _, _, rfl⟩ := mem_enumAlphaConstrainedChoice_FA_graft.mp h; rfl

/-! ## §1.8: F-side explicit choice substrate (Phase 4.2 substrate, Piece 2 prerequisite)

The standard `insertionForest F_A pre_FA_B` is defined recursively, leaving the per-
pre_FA_B-element grafting target (which F_A tree, which vertex within that tree)
implicit. To bridge `insertionForest F_A pre_FA_B` to a per-tree multi-graft form
that exposes those choices explicitly — needed by `LHS_per_alpha_raw` for
α-bucket-respecting γ enumeration — we introduce:

* `perKFChoice F_A : List (Fin F_A.length × Path)` — per-pre_FA_B[k] choice
  alphabet: a tree index `i ∈ Fin F_A.length` and a vertex `v ∈ vertices F_A[i]`.
* `perTreePairsFromFChoice F_A pre_FA_B fdata i : List (Path × Planar α)` —
  the per-tree grafting pairs for tree `F_A[i]`, extracted from the fdata
  list.
* `buildFIns F_A pre_FA_B fdata : List (Planar α)` — the resulting forest
  with each F_A[i] multi-grafted by its per-tree pairs.

The bridge `insertionForest_eq_explicit : insertionForest F_A pre_FA_B =
(enumFChoices F_A pre_FA_B).map (buildFIns F_A pre_FA_B)` is sorry-fenced; its
proof requires induction on F_A interleaving with `insertionForest_cons_assignment`
and the per-α-step refactoring of (T-bucket vs F-bucket) into (Fin F_A.length).

Per `scratch/a33_phase4_2_plan.md` Piece 2 prerequisite (~80-150 LOC of new
substrate, deferred from session 2026-05-13). -/

/-- Per-pre_FA_B[k] choice alphabet for the F-side explicit-choice form: each
    element of the returned list is a pair `(i, v)` where `i : Fin F_A.length`
    identifies the F_A-tree the pre_FA_B[k] graft targets, and `v : Path` is
    the vertex within `F_A[i.val]`. -/
private def perKFChoice (F_A : List (Planar α)) : List (Fin F_A.length × Path) :=
  (List.finRange F_A.length).flatMap fun i =>
    (vertices F_A[i.val]).map fun v => (i, v)

/-- Per-tree multi-graft pairs extracted from explicit F-side choice data. For
    F_A-tree index `i`, collect the (vertex, pre_FA_B[k]) pairs where
    `fdata[k] = (i, vertex)`. The result is a `List (Path × Planar α)` ready
    for `multiGraft F_A[i.val]`. -/
private def perTreePairsFromFChoice
    (F_A pre_FA_B : List (Planar α))
    (fdata : List (Fin F_A.length × Path))
    (i : Fin F_A.length) : List (Path × Planar α) :=
  (fdata.zip pre_FA_B).filterMap fun p =>
    if p.fst.fst = i then some (p.fst.snd, p.snd) else none

/-- The forest result of multi-grafting `pre_FA_B` into `F_A` according to
    explicit choice data `fdata`. Each `F_A[i]` is multi-grafted with the
    per-tree pairs extracted from `fdata`. -/
private def buildFIns
    (F_A pre_FA_B : List (Planar α))
    (fdata : List (Fin F_A.length × Path)) : List (Planar α) :=
  (List.finRange F_A.length).map fun i =>
    multiGraft F_A[i.val] (perTreePairsFromFChoice F_A pre_FA_B fdata i)

/-- Multiset of all explicit F-side choice data: one per pre_FA_B element,
    drawn from `perKFChoice F_A`. -/
private def enumFChoices (F_A pre_FA_B : List (Planar α)) :
    Multiset (List (Fin F_A.length × Path)) :=
  Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)

/-- `perKFChoice` for an empty F_A is empty (no F_A-trees to pick a vertex from). -/
@[simp] private theorem perKFChoice_nil :
    perKFChoice ([] : List (Planar α)) = [] := rfl

/-- `enumFChoices F_A []` is the singleton `{[]}` (only the empty choice).
    Holds for any F_A since `listChoices xs 0 = [[]]`. -/
@[simp] private theorem enumFChoices_nil_pre_FA_B (F_A : List (Planar α)) :
    enumFChoices F_A ([] : List (Planar α)) =
      ({[]} : Multiset (List (Fin F_A.length × Path))) := by
  unfold enumFChoices
  rw [List.length_nil, listChoices_zero]
  rfl

/-- F-side explicit-choice bridge: `insertionForest F_A pre_FA_B` in standard
    form equals the explicit-choice enumeration `(enumFChoices F_A pre_FA_B).map
    (buildFIns F_A pre_FA_B)`. The bijection sends each `[true, false]`-tagged
    `(α₀, α₁, …)` recursive assignment to a single
    `List (Fin F_A.length × Path)` of length `pre_FA_B.length`.

    Proof outline (deferred):
    1. Induct on `F_A`. Base case `F_A = []`: both sides are
       `if pre_FA_B = [] then {[]} else 0` (0 because `perKFChoice [] = []` and
       `listChoices [] (n+1) = []`, while `insertionForest [] (_::_) = 0`).
    2. Cons case `F_A = T :: F_rest`: unfold LHS via
       `insertionForest_cons_assignment` to expose `bind α : listChoices [t,f]
       |pre_FA_B|: bind T' : insertion T (X-t-slice α): map F' : insertionForest
       F_rest (X-f-slice α): T' :: F'`. Apply IH to inner `insertionForest
       F_rest (X-f-slice α)` and `insertion_def` to inner `insertion T
       (X-t-slice α)`. Reorganize the resulting nested binds into a single bind
       over `listChoices (perKFChoice (T :: F_rest)) pre_FA_B.length` via the
       bijection `(α, choice_T, fdata_rest) ↔ data` where `data[k]` records
       which F_A tree (Fin (T :: F_rest).length) and which vertex within.

    Per `scratch/a33_phase4_2_plan.md` Piece 2 prerequisite; ~80-150 LOC. -/
private theorem insertionForest_eq_explicit
    (F_A pre_FA_B : List (Planar α)) :
    insertionForest F_A pre_FA_B =
      (enumFChoices F_A pre_FA_B).map (buildFIns F_A pre_FA_B) := by
  induction F_A with
  | nil =>
    -- F_A = []. Both sides depend on pre_FA_B emptiness.
    -- LHS: insertionForest [] pre_FA_B = if pre_FA_B = [] then {[]} else 0.
    -- RHS: enumFChoices [] pre_FA_B = Multiset.ofList (listChoices [] pre_FA_B.length)
    --      = if pre_FA_B = [] then {[]} else 0 (since perKFChoice [] = [] and
    --        listChoices [] (n+1) = []).
    --      buildFIns [] pre_FA_B [] = (List.finRange 0).map ... = [].
    cases pre_FA_B with
    | nil =>
      -- pre_FA_B = []. LHS = {[]}. RHS = {[]}.map buildFIns ... = {buildFIns [] [] []} = {[]}.
      rw [insertionForest_nil_nil, enumFChoices_nil_pre_FA_B,
          Multiset.map_singleton]
      -- buildFIns [] [] [] = (List.finRange 0).map _ = [], inlined here
      -- because the named lemma `buildFIns_nil_FA` is defined later in §1.8.1.
      unfold buildFIns
      rfl
    | cons g gs =>
      -- pre_FA_B = g :: gs. LHS = 0. RHS = 0.
      rw [insertionForest_empty_host_nonempty_guests]
      -- enumFChoices [] (g :: gs) = Multiset.ofList (listChoices [] (gs.length + 1)) = 0
      -- since listChoices [] (n+1) = [].flatMap ... = [].
      show 0 = (enumFChoices ([] : List (Planar α)) (g :: gs)).map _
      rw [show enumFChoices ([] : List (Planar α)) (g :: gs) = 0 from by
        unfold enumFChoices
        simp only [perKFChoice_nil, List.length_cons, listChoices_succ,
                   List.flatMap_nil]
        rfl]
      rfl
  | cons T F_rest ih =>
    -- TODO: Piece 2 prerequisite cons case. The (α, choice_T, fdata_rest) ↔ data
    -- bijection requires bridging insertionForest_cons_assignment + insertion_def
    -- + IH to the explicit form. ~80-130 LOC.
    sorry

/-! ### §1.8.1 buildFIns base properties

Sorry-free structural lemmas about `buildFIns`. These don't depend on
`insertionForest_eq_explicit` and provide the foundational reasoning surface
for downstream consumers. -/

/-- `buildFIns` over an empty `F_A` yields the empty forest, regardless of
    `pre_FA_B` and `fdata`. (The `(List.finRange 0).map _` = []`.) -/
@[simp] theorem buildFIns_nil_FA (pre_FA_B : List (Planar α))
    (fdata : List (Fin (0 : ℕ) × Path)) :
    buildFIns ([] : List (Planar α)) pre_FA_B fdata = [] := by
  unfold buildFIns
  rfl

/-- `buildFIns` with empty `pre_FA_B` and empty `fdata` reduces to `F_A`
    (no grafts applied). The per-tree pairs are all empty, and `multiGraft T []
    = T` reduces each tree to itself. -/
@[simp] theorem buildFIns_nil_pre_FA_B_nil_fdata (F_A : List (Planar α)) :
    buildFIns F_A ([] : List (Planar α)) ([] : List (Fin F_A.length × Path)) =
      F_A := by
  unfold buildFIns perTreePairsFromFChoice
  -- per-tree pairs: filterMap of empty zip = [], so multiGraft F_A[i] [] = F_A[i].
  -- Then (List.finRange F_A.length).map (fun i => F_A[i]) = F_A.
  conv_lhs =>
    rw [show (fun i : Fin F_A.length =>
            multiGraft F_A[i.val]
              ((([] : List (Fin F_A.length × Path)).zip
                 ([] : List (Planar α))).filterMap
                  fun p => if p.fst.fst = i then some (p.fst.snd, p.snd) else none)) =
          (fun i : Fin F_A.length => F_A[i.val]) from by
      funext i
      simp only [List.zip_nil_left, List.filterMap_nil, multiGraft_nil]]
  -- (List.finRange n).map (fun i => F_A[i.val]) = F_A
  exact List.map_getElem_finRange F_A

/-! ## §1.9: `LHS_per_alpha_raw` (Phase 4.2 substrate, Piece 2 — DEFERRED)

The per-α LHS-side slice. Operationally enumerates over (T-side choice, F-side
choice, α-respecting γ) tuples and computes the multi-graft of C into T_ins ::
F_ins. Defined so that:

1. `LHS = bind α : LHS_per_alpha_raw α C` (Piece 3, sorry-fenced).
2. `(LHS_per_alpha_raw α C).map msform = (iteratedQuadSum-leaf α-pres).map msform`
   (Piece 4, sorry-fenced).

The two together (composed via Piece 5) close the headline cons-case
`LHS_eq_iteratedQuadSum_msform_cons_alphaBind`.

**Why deferred this session.** A full operational definition requires bridging
the C-side γ enumeration (4-bucket V(T_ins :: F_ins) partition) to the explicit
T-side and F-side choice data. The bridging requires:

* T-side: `liftMulti (choice_T.zip pre_T_B) k q` for T_graft entries, with the
  Fin-indexing across `pre_T_B.length` vs `(choice_T.zip pre_T_B).length` requiring
  careful coercions.
* F-side: `liftMulti (perTreePairsFromFChoice F_A pre_FA_B fdata i) k' q'` for
  FA_graft entries, with `k'` derived from the source pre_FA_B[k]'s tree assignment.
* Forest-multi-graft helper: `multiGraftForest (T_ins :: F_ins) pairs` with
  tree-index-prefixed paths.

Each of these introduces ~50-100 LOC of helpers. The full definition + base
lemmas (`LHS_per_alpha_raw_nil_C`, `LHS_per_alpha_raw_cons_C`,
`LHS_per_alpha_raw_length`) is estimated ~80-120 LOC per the plan, but the
underlying helpers add another ~150-250 LOC.

**Recommended next-session attack**: design the helpers (forest multi-graft,
unified-Fin coercion, AlphaConstrainedChoice.toPath) before committing to the
LHS_per_alpha_raw form. The helpers should be substrate-quality (mathlib
candidates) so they're worth the LOC investment.

See `scratch/a33_phase4_2_plan.md` Piece 2 for the full design discussion. -/

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

/-! ### §2.14 `insertionForest` length preservation

Every element of `insertionForest host pre` has length `host.length` —
multi-graft preserves the host structure (each `host`-tree becomes a
modified version of itself in the output forest). Used in A3.2 base
case to bridge `bind α over |X' ++ pre_A|` with `bind asn over |host_B|`. -/

/-- Every output of `insertionForest host pre` has length `host.length`.
    Proof by induction on `host` (matching the function's termination measure). -/
private lemma insertionForest_mem_length :
    ∀ (host : List (Planar α)) (pre : List (Planar α)) (X : List (Planar α)),
    X ∈ insertionForest host pre → X.length = host.length := by
  intro host
  induction host with
  | nil =>
    intro pre X hX
    cases pre with
    | nil =>
      rw [insertionForest_nil_nil] at hX
      rw [Multiset.mem_singleton.mp hX]
    | cons p ps =>
      rw [insertionForest_empty_host_nonempty_guests] at hX
      exact absurd hX (Multiset.notMem_zero X)
  | cons h hs ih =>
    intro pre X hX
    cases pre with
    | nil =>
      rw [insertionForest_cons_host_nil_guests] at hX
      rw [Multiset.mem_singleton.mp hX]
    | cons p ps =>
      rw [insertionForest_cons_cons] at hX
      rcases Multiset.mem_bind.mp hX with ⟨α, _, hX2⟩
      rcases Multiset.mem_bind.mp hX2 with ⟨T', _, hX3⟩
      rcases Multiset.mem_map.mp hX3 with ⟨F', hF'_mem, hX_eq⟩
      rw [← hX_eq, List.length_cons]
      have h_F'_len : F'.length = hs.length := ih _ F' hF'_mem
      rw [h_F'_len]
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

/-! Bool-symmetry of `listChoices`: enumerating bit-vectors and applying `g`
    is invariant under flipping all bits via `List.map Bool.not`.

    Used in the `a=false` sub-case of `insertionForest_split_pair`: bool-flipping
    the outer `sub_B` swaps the role of the t-side and f-side, allowing the LHS
    to be brought into the `splitPairLHSform` shape so that `split_pair_aux_T`
    can bridge it to the RHS form. -/

/-- The multiset of length-`n` bit-vectors is invariant under bit-flip
    (i.e., applying `List.map Bool.not` to each). -/
private lemma listChoices_bool_invariant (n : Nat) :
    (Multiset.ofList (listChoices [true, false] n)).map (List.map Bool.not) =
      Multiset.ofList (listChoices [true, false] n) := by
  induction n with
  | zero =>
    simp [listChoices_zero]
  | succ n ih =>
    -- Express both sides as `(Multiset.ofList (lc n)).map (true :: ·) + (Multiset.ofList (lc n)).map (false :: ·)`.
    -- That gives us a uniform rewrite path.
    have rhs_form : (Multiset.ofList (listChoices [true, false] (n + 1)) : Multiset (List Bool)) =
        (Multiset.ofList (listChoices [true, false] n)).map (true :: ·) +
          (Multiset.ofList (listChoices [true, false] n)).map (false :: ·) := by
      rw [listChoices_succ]
      rw [show ([true, false].flatMap fun v => (listChoices [true, false] n).map (v :: ·)) =
              (listChoices [true, false] n).map (true :: ·) ++ (listChoices [true, false] n).map (false :: ·)
              from by simp [List.flatMap_cons, List.flatMap_nil]]
      rfl
    rw [rhs_form]
    rw [Multiset.map_add, Multiset.map_map, Multiset.map_map]
    -- LHS: (lc n).map ((List.map not) ∘ (true :: ·)) + (lc n).map ((List.map not) ∘ (false :: ·))
    have h1 : (List.map (Bool.not) ∘ (List.cons true) : List Bool → List Bool) =
              (List.cons false ∘ List.map Bool.not) := by
      funext a; simp
    have h2 : (List.map (Bool.not) ∘ (List.cons false) : List Bool → List Bool) =
              (List.cons true ∘ List.map Bool.not) := by
      funext a; simp
    rw [h1, h2]
    rw [← Multiset.map_map (List.cons false) (List.map Bool.not),
        ← Multiset.map_map (List.cons true) (List.map Bool.not)]
    rw [ih]
    rw [add_comm]

/-- Bool-symmetry of bind: substituting the bound variable with its bit-flip
    yields the same multiset. -/
private lemma listChoices_bool_symm_bind {γ : Type*} (n : Nat)
    (g : List Bool → Multiset γ) :
    (Multiset.ofList (listChoices [true, false] n)).bind g =
    (Multiset.ofList (listChoices [true, false] n)).bind (fun a => g (a.map Bool.not)) := by
  conv_lhs => rw [← listChoices_bool_invariant n]
  rw [Multiset.bind_map]

/-- `filter_t` under bool-flip = `filter_f` without flip. -/
private lemma filterMap_t_map_not (qs : List (Planar α)) (a : List Bool) :
    ((qs.zip (a.map Bool.not)).filterMap (fun p => if p.snd then some p.fst else none)) =
    ((qs.zip a).filterMap (fun p => if p.snd then none else some p.fst)) := by
  induction qs generalizing a with
  | nil => simp
  | cons q qs_rest ih =>
    cases a with
    | nil => simp
    | cons b a_rest =>
      simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons]
      cases b
      · simp [ih]
      · simp [ih]

/-- `filter_f` under bool-flip = `filter_t` without flip. -/
private lemma filterMap_f_map_not (qs : List (Planar α)) (a : List Bool) :
    ((qs.zip (a.map Bool.not)).filterMap (fun p => if p.snd then none else some p.fst)) =
    ((qs.zip a).filterMap (fun p => if p.snd then some p.fst else none)) := by
  induction qs generalizing a with
  | nil => simp
  | cons q qs_rest ih =>
    cases a with
    | nil => simp
    | cons b a_rest =>
      simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons]
      cases b
      · simp [ih]
      · simp [ih]

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
      - For a = false: same approach via Path B — bool-flip outer `sub_B`
        (using `listChoices_bool_symm_bind`) brings the LHS into the
        `splitPairLHSform` shape; apply `split_pair_aux_T`; bool-flip the
        inner `sub_B'` to align routings; then bind reorder via `Multiset.bind_bind`
        to match the RHS structure (after expanding RHS via
        `insertionForest_cons_assignment` + IH on `rest_h`).

    Sorry-free. -/
private theorem insertionForest_split_pair {ω : Type*} :
    ∀ (host_B : List (Planar α))
      (leaf : List (Planar α) → List (Planar α) → Multiset ω)
      (asn : List Bool) (_ : asn.length = host_B.length)
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
  intro host_B
  induction host_B with
  | nil =>
    intros leaf asn hasn pre_B
    -- asn = []
    obtain rfl : asn = [] := by
      cases asn
      · rfl
      · simp at hasn
    -- Reduce filter_t/f at host_B = [], asn = []: both = []
    simp only [List.filterMap_nil, List.zip_nil_right, List.zip_nil_left]
    -- Goal: bind sub_B: (insertionForest [] (filter_t pre_B sub_B)).bind X_T =>
    --                   (insertionForest [] (filter_f pre_B sub_B)).bind X_F => leaf X_T X_F
    --     = (insertionForest [] pre_B).bind X' => leaf [] []
    match pre_B with
    | [] =>
      -- pre_B = []: lc 0 = [[]], so sub_B = []; both sides = leaf [] []
      simp only [List.length_nil, listChoices_zero, List.zip_nil_right, List.filterMap_nil,
                 insertionForest_nil_nil, Multiset.coe_singleton, Multiset.singleton_bind]
    | c :: rest_pre =>
      -- pre_B = c :: rest_pre: insertionForest [] (c :: rest_pre) = 0; both sides = 0
      rw [insertionForest_empty_host_nonempty_guests, Multiset.zero_bind]
      -- LHS: each sub_B contributes 0 (sub_B has length ≥ 1, so filter_t or filter_f is non-empty,
      -- making (insertionForest [] non-empty) = 0).
      rw [show ((Multiset.ofList (listChoices [true, false] (c :: rest_pre).length)).bind (fun sub_B =>
                (insertionForest ([] : List (Planar α))
                    (((c :: rest_pre).zip sub_B).filterMap (fun p => if p.snd then some p.fst else none))).bind fun X_T =>
                  (insertionForest ([] : List (Planar α))
                      (((c :: rest_pre).zip sub_B).filterMap (fun p => if p.snd then none else some p.fst))).bind fun X_F =>
                    leaf X_T X_F)) =
              (Multiset.ofList (listChoices [true, false] (c :: rest_pre).length)).bind (fun _ => (0 : Multiset ω))
              from by
        refine Multiset.bind_congr fun sub_B hsub_B => ?_
        have hsub_B_len : sub_B.length = (c :: rest_pre).length := mem_listChoices_bool_length _ _ hsub_B
        cases sub_B with
        | nil => simp at hsub_B_len
        | cons b sub_B_rest =>
          cases b with
          | true =>
            simp only [List.zip_cons_cons, List.filterMap_cons, if_true]
            rw [insertionForest_empty_host_nonempty_guests, Multiset.zero_bind]
          | false =>
            simp only [List.zip_cons_cons, List.filterMap_cons,
                       if_neg (by decide : (false : Bool) ≠ true)]
            conv_lhs =>
              rhs; ext X_T
              rw [insertionForest_empty_host_nonempty_guests, Multiset.zero_bind]
            rw [Multiset.bind_zero]]
      rw [Multiset.bind_zero]
  | cons h rest_h ih =>
    intros leaf asn hasn pre_B
    cases asn with
    | nil =>
      simp [List.length_cons] at hasn
    | cons a asn_rest =>
      have hasn_rest : asn_rest.length = rest_h.length := by
        simpa [List.length_cons] using hasn
      cases a with
      | true =>
        -- a=true sub-case: h goes to T-side.
        --   filter_t (h :: rest_h) (true :: asn_rest) = h :: filter_t rest_h asn_rest
        --   filter_f (h :: rest_h) (true :: asn_rest) = filter_f rest_h asn_rest
        simp only [List.zip_cons_cons, List.filterMap_cons, if_true,
                   if_neg (by decide : (true : Bool) ≠ false)]
        -- Goal LHS: bind sub_B: (insertionForest (h :: filter_t rest_h asn_rest)
        --                          (filter_t pre_B sub_B)).bind X_T =>
        --             (insertionForest (filter_f rest_h asn_rest)
        --                 (filter_f pre_B sub_B)).bind X_F => leaf X_T X_F
        -- Goal RHS: (insertionForest (h :: rest_h) pre_B).bind X' =>
        --             leaf (filter_t X' (true :: asn_rest)) (filter_f X' (true :: asn_rest))
        --
        -- Step 1: Expand LHS's T-side via insertionForest_cons_assignment (T = h):
        conv_lhs =>
          rhs; ext sub_B
          rw [insertionForest_cons_assignment h
                ((rest_h.zip asn_rest).filterMap (fun p => if p.snd then some p.fst else none))
                ((pre_B.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none))]
        -- LHS: bind sub_B: (bind γ_T over |filter_t pre_B sub_B|:
        --                     (insertion h (filter_t (filter_t pre_B sub_B) γ_T)).bind T_h =>
        --                       (insertionForest (filter_t rest_h asn_rest)
        --                           (filter_f (filter_t pre_B sub_B) γ_T)).map (T_h :: ·)).bind X_T =>
        --                 (insertionForest (filter_f rest_h asn_rest) (filter_f pre_B sub_B)).bind X_F =>
        --                   leaf X_T X_F
        -- Step 2: Pull γ_T out via Multiset.bind_assoc (so γ_T is OUTSIDE the .bind X_T).
        conv_lhs =>
          rhs; ext sub_B
          rw [Multiset.bind_assoc]
        -- LHS: bind sub_B: bind γ_T: (insertion h ...).bind T_h =>
        --                              (insertionForest (filter_t rest_h asn_rest) ...).map (T_h :: ·).bind X_T =>
        --                                (insertionForest (filter_f rest_h asn_rest) ...).bind X_F =>
        --                                  leaf X_T X_F
        -- Step 3: Pull T_h further out via Multiset.bind_assoc.
        conv_lhs =>
          rhs; ext sub_B; rhs; ext γ_T
          rw [Multiset.bind_assoc]
        -- LHS: bind sub_B: bind γ_T: bind T_h: (insertionForest (filter_t rest_h asn_rest) ...).map (T_h :: ·).bind X_T =>
        --                                       (insertionForest (filter_f rest_h asn_rest) ...).bind X_F =>
        --                                         leaf X_T X_F
        -- Step 4: Convert .map (T_h :: ·).bind X_T => Z(X_T) via Multiset.map_bind:
        -- (M.map f).bind g = M.bind (g ∘ f). Here f = (T_h :: ·), g = X_T => Z(X_T).
        conv_lhs =>
          rhs; ext sub_B; rhs; ext γ_T; rhs; ext T_h
          rw [Multiset.bind_map]
        -- LHS: bind sub_B: bind γ_T: bind T_h:
        --        (insertionForest (filter_t rest_h asn_rest) ...).bind F'_T_rest =>
        --          (insertionForest (filter_f rest_h asn_rest) ...).bind X_F => leaf (T_h :: F'_T_rest) X_F
        --
        -- This is splitPairLHSform pre_B K_T where:
        -- K_T(A1, A2, A3) := (insertion h A1).bind T_h =>
        --                      (insertionForest (filter_t rest_h asn_rest) A2).bind F'_T_rest =>
        --                        (insertionForest (filter_f rest_h asn_rest) A3).bind X_F =>
        --                          leaf (T_h :: F'_T_rest) X_F
        --
        -- Step 5: Apply split_pair_aux_T to get splitPairRHSform pre_B K_T.
        rw [split_pair_aux_T pre_B (fun A1 A2 A3 =>
              (insertion h A1).bind fun T_h =>
                (insertionForest
                    ((rest_h.zip asn_rest).filterMap (fun p => if p.snd then some p.fst else none)) A2).bind
                  fun F'_T_rest =>
                    (insertionForest
                        ((rest_h.zip asn_rest).filterMap (fun p => if p.snd then none else some p.fst)) A3).bind
                      fun X_F => leaf (T_h :: F'_T_rest) X_F)]
        -- Step 6: Now the LHS is splitPairRHSform shape. Match with RHS by expanding RHS.
        --
        -- Expand RHS: (insertionForest (h :: rest_h) pre_B).bind X' => leaf (filter_t X' ...) (filter_f X' ...)
        -- via insertionForest_cons_assignment:
        rw [insertionForest_cons_assignment h rest_h pre_B]
        -- RHS: (bind α' over |pre_B|:
        --        (insertion h (filter_t pre_B α')).bind T_h =>
        --          (insertionForest rest_h (filter_f pre_B α')).map (T_h :: ·)).bind X' =>
        --      leaf (filter_t X' (true :: asn_rest)) (filter_f X' (true :: asn_rest))
        --
        -- Pull binds out: Multiset.bind_assoc twice; convert .map (T_h :: ·).bind X' via Multiset.bind_map.
        rw [Multiset.bind_assoc]
        conv_rhs =>
          rhs; ext α'
          rw [Multiset.bind_assoc]
        conv_rhs =>
          rhs; ext α'; rhs; ext T_h
          rw [Multiset.bind_map]
        -- RHS: bind α': bind T_h: bind F_rest ∈ (insertionForest rest_h (filter_f pre_B α')):
        --        leaf (filter_t (T_h :: F_rest) (true :: asn_rest)) (filter_f (T_h :: F_rest) (true :: asn_rest))
        --
        -- Reduce filter_t (T_h :: F_rest) (true :: asn_rest) = T_h :: filter_t F_rest asn_rest
        -- and filter_f (T_h :: F_rest) (true :: asn_rest) = filter_f F_rest asn_rest.
        conv_rhs =>
          rhs; ext α'; rhs; ext T_h; rhs; ext F_rest
          rw [show ((T_h :: F_rest).zip (true :: asn_rest)).filterMap
                  (fun p => if p.snd then some p.fst else none) =
                T_h :: (F_rest.zip asn_rest).filterMap (fun p => if p.snd then some p.fst else none) from by
              simp [List.zip_cons_cons, List.filterMap_cons]]
          rw [show ((T_h :: F_rest).zip (true :: asn_rest)).filterMap
                  (fun p => if p.snd then none else some p.fst) =
                (F_rest.zip asn_rest).filterMap (fun p => if p.snd then none else some p.fst) from by
              simp [List.zip_cons_cons, List.filterMap_cons]]
        -- RHS: bind α': bind T_h: bind F_rest:
        --        leaf (T_h :: filter_t F_rest asn_rest) (filter_f F_rest asn_rest)
        --
        -- Now apply IH on rest_h with leaf' Y1 Y2 = leaf (T_h :: Y1) Y2,
        -- asn := asn_rest, pre_B := filter_f pre_B α'.
        -- IH says: bind sub_B' over |filter_f pre_B α'|:
        --            (insertionForest (filter_t rest_h asn_rest) (filter_t (filter_f pre_B α') sub_B')).bind X_T' =>
        --              (insertionForest (filter_f rest_h asn_rest) (filter_f (filter_f pre_B α') sub_B')).bind X_F' =>
        --                leaf' X_T' X_F'
        --        = (insertionForest rest_h (filter_f pre_B α')).bind F_rest =>
        --            leaf' (filter_t F_rest asn_rest) (filter_f F_rest asn_rest)
        -- Use ← ih to rewrite the RHS expression in the form on the LHS of IH.
        conv_rhs =>
          rhs; ext α'; rhs; ext T_h
          rw [← ih (fun Y1 Y2 => leaf (T_h :: Y1) Y2) asn_rest hasn_rest
                ((pre_B.zip α').filterMap (fun p => if p.snd then none else some p.fst))]
        -- RHS: bind α': bind T_h: bind sub_B': bind X_T': bind X_F': leaf (T_h :: X_T') X_F'
        --
        -- Step 7: Match with LHS (splitPairRHSform pre_B K_T).
        -- LHS = bind α': bind sub_B':
        --         bind T_h ∈ (insertion h (filter_t pre_B α')):
        --           bind F'_T_rest ∈ (insertionForest (filter_t rest_h asn_rest) (filter_t (filter_f pre_B α') sub_B')):
        --             bind X_F ∈ (insertionForest (filter_f rest_h asn_rest) (filter_f (filter_f pre_B α') sub_B')):
        --               leaf (T_h :: F'_T_rest) X_F
        --
        -- RHS = bind α': bind T_h ∈ (insertion h (filter_t pre_B α')):
        --         bind sub_B': bind X_T' ∈ (insertionForest (filter_t rest_h asn_rest) ...):
        --           bind X_F' ∈ (insertionForest (filter_f rest_h asn_rest) ...): leaf (T_h :: X_T') X_F'
        --
        -- Differ only in bind order of T_h vs sub_B'. Swap via Multiset.bind_bind.
        refine Multiset.bind_congr fun α' _ => ?_
        rw [Multiset.bind_bind]
      | false =>
        -- a=false sub-case: h goes to F-side.
        --   filter_t (h :: rest_h) (false :: asn_rest) = filter_t rest_h asn_rest
        --   filter_f (h :: rest_h) (false :: asn_rest) = h :: filter_f rest_h asn_rest
        simp only [List.zip_cons_cons, List.filterMap_cons,
                   if_neg (by decide : (false : Bool) ≠ true), if_pos rfl]
        -- LHS: bind sub_B:
        --        (insertionForest (filter_t rest_h asn_rest) (filter_t pre_B sub_B)).bind X_T =>
        --          (insertionForest (h :: filter_f rest_h asn_rest) (filter_f pre_B sub_B)).bind X_F =>
        --            leaf X_T X_F
        -- RHS: (insertionForest (h :: rest_h) pre_B).bind X' =>
        --        leaf (filter_t X' (false :: asn_rest)) (filter_f X' (false :: asn_rest))
        --
        -- Path B: bool-flip outer sub_B to bring LHS into the splitPairLHSform shape,
        -- then split_pair_aux_T, then bool-flip inner sub_B' to match RHS.
        --
        -- Step 1: Bool-flip outer sub_B via listChoices_bool_symm_bind.
        rw [listChoices_bool_symm_bind pre_B.length]
        -- LHS: bind sub_B (with internal sub_B → map not sub_B substitution applied):
        --   ... uses (pre_B.zip (sub_B.map Bool.not)).filterMap ...
        --
        -- Use filterMap_t_map_not / filterMap_f_map_not to swap filter_t/f roles.
        conv_lhs =>
          rhs; ext sub_B
          rw [filterMap_t_map_not, filterMap_f_map_not]
        -- LHS: bind sub_B:
        --        (insertionForest (filter_t rest_h asn_rest) (filter_f pre_B sub_B)).bind X_T =>
        --          (insertionForest (h :: filter_f rest_h asn_rest) (filter_t pre_B sub_B)).bind X_F =>
        --            leaf X_T X_F
        --
        -- Step 2: Expand the F-side (still h :: ...) via insertionForest_cons_assignment:
        conv_lhs =>
          rhs; ext sub_B
          rhs; ext X_T
          rw [insertionForest_cons_assignment h
                ((rest_h.zip asn_rest).filterMap (fun p => if p.snd then none else some p.fst))
                ((pre_B.zip sub_B).filterMap (fun p => if p.snd then some p.fst else none))]
        -- LHS: bind sub_B: bind X_T:
        --        (bind γ over |filter_t pre_B sub_B|:
        --          (insertion h (filter_t (filter_t pre_B sub_B) γ)).bind X'_h =>
        --            (insertionForest (filter_f rest_h asn_rest) (filter_f (filter_t pre_B sub_B) γ)).map (X'_h :: ·)).bind X_F =>
        --        leaf X_T X_F
        -- Step 3: Pull γ out (past X_T and the inner binds) via Multiset.bind_assoc.
        conv_lhs =>
          rhs; ext sub_B; rhs; ext X_T
          rw [Multiset.bind_assoc]
        -- LHS: bind sub_B: bind X_T: bind γ:
        --        (insertion h ...).bind X'_h => (insertionForest ...).map (X'_h :: ·).bind X_F => leaf X_T X_F
        --
        -- Step 4: Swap order of X_T and γ binds via Multiset.bind_bind (γ doesn't depend on X_T).
        conv_lhs =>
          rhs; ext sub_B
          rw [Multiset.bind_bind]
        -- LHS: bind sub_B: bind γ: bind X_T:
        --        (insertion h ...).bind X'_h => (insertionForest ...).map (X'_h :: ·).bind X_F => leaf X_T X_F
        --
        -- Step 5: Pull X'_h out via bind_assoc, then convert .map.bind via Multiset.bind_map.
        conv_lhs =>
          rhs; ext sub_B; rhs; ext γ; rhs; ext X_T
          rw [Multiset.bind_assoc]
        conv_lhs =>
          rhs; ext sub_B; rhs; ext γ; rhs; ext X_T; rhs; ext X'_h
          rw [Multiset.bind_map]
        -- LHS: bind sub_B: bind γ: bind X_T: bind X'_h: bind F'_F_rest:
        --        leaf X_T (X'_h :: F'_F_rest)
        --
        -- This is splitPairLHSform pre_B K_F where:
        -- K_F(A1, A2, A3) := bind X_T ∈ (insertionForest (filter_t rest_h asn_rest) A3 [-- arg3 = filter_f sub_B = T_rest pre]):
        --                    Wait — let me re-check. After bool-flip, the args in K positions are:
        --                    arg1 (sub_B=t, γ=t) = filter_t (filter_t pre_B sub_B) γ → goes to insertion h → h-bucket
        --                    arg2 (sub_B=t, γ=f) = filter_f (filter_t pre_B sub_B) γ → goes to insertionForest (filter_f rest_h) → F_rest
        --                    arg3 (sub_B=f) = filter_f pre_B sub_B → goes to insertionForest (filter_t rest_h) → T_rest
        --
        -- So K_F(A1, A2, A3) = bind X_T ∈ (insertionForest (filter_t rest_h asn_rest) A3):
        --                        bind X'_h ∈ (insertion h A1):
        --                          bind F'_F_rest ∈ (insertionForest (filter_f rest_h asn_rest) A2):
        --                            leaf X_T (X'_h :: F'_F_rest)
        --
        -- Step 6: Apply split_pair_aux_T to get splitPairRHSform pre_B K_F.
        rw [split_pair_aux_T pre_B (fun A1 A2 A3 =>
              (insertionForest
                  ((rest_h.zip asn_rest).filterMap (fun p => if p.snd then some p.fst else none)) A3).bind
                fun X_T =>
                  (insertion h A1).bind fun X'_h =>
                    (insertionForest
                        ((rest_h.zip asn_rest).filterMap (fun p => if p.snd then none else some p.fst)) A2).bind
                      fun F'_F_rest => leaf X_T (X'_h :: F'_F_rest))]
        -- LHS now: bind α': bind sub_B':
        --   bind X_T ∈ (insertionForest (filter_t rest_h asn_rest) (filter_f (filter_f pre_B α') sub_B')):
        --     bind X'_h ∈ (insertion h (filter_t pre_B α')):
        --       bind F'_F_rest ∈ (insertionForest (filter_f rest_h asn_rest) (filter_t (filter_f pre_B α') sub_B')):
        --         leaf X_T (X'_h :: F'_F_rest)
        --
        -- Per-c routing:
        -- (α'=t): in (filter_t pre_B α') → h-bucket
        -- (α'=f, sub_B'=t): in (filter_t (filter_f pre_B α') sub_B') → F_rest-bucket  ← OPPOSITE of desired
        -- (α'=f, sub_B'=f): in (filter_f (filter_f pre_B α') sub_B') → T_rest-bucket  ← OPPOSITE of desired
        --
        -- Step 7: Expand RHS via insertionForest_cons_assignment + bind manipulations + IH.
        --
        -- RHS originally: (insertionForest (h :: rest_h) pre_B).bind X' =>
        --                   leaf (filter_t X' (false :: asn_rest)) (filter_f X' (false :: asn_rest))
        rw [insertionForest_cons_assignment h rest_h pre_B]
        rw [Multiset.bind_assoc]
        conv_rhs =>
          rhs; ext α'
          rw [Multiset.bind_assoc]
        conv_rhs =>
          rhs; ext α'; rhs; ext X'_h
          rw [Multiset.bind_map]
        -- RHS: bind α': bind X'_h: bind X'_rest ∈ (insertionForest rest_h (filter_f pre_B α')):
        --        leaf (filter_t (X'_h :: X'_rest) (false :: asn_rest)) (filter_f (X'_h :: X'_rest) (false :: asn_rest))
        --
        -- Reduce filter_t (X'_h :: X'_rest) (false :: asn_rest) = filter_t X'_rest asn_rest
        -- and filter_f (X'_h :: X'_rest) (false :: asn_rest) = X'_h :: filter_f X'_rest asn_rest.
        conv_rhs =>
          rhs; ext α'; rhs; ext X'_h; rhs; ext X'_rest
          rw [show ((X'_h :: X'_rest).zip (false :: asn_rest)).filterMap
                  (fun p => if p.snd then some p.fst else none) =
                (X'_rest.zip asn_rest).filterMap (fun p => if p.snd then some p.fst else none) from by
              simp [List.zip_cons_cons, List.filterMap_cons]]
          rw [show ((X'_h :: X'_rest).zip (false :: asn_rest)).filterMap
                  (fun p => if p.snd then none else some p.fst) =
                X'_h :: (X'_rest.zip asn_rest).filterMap (fun p => if p.snd then none else some p.fst) from by
              simp [List.zip_cons_cons, List.filterMap_cons]]
        -- RHS: bind α': bind X'_h: bind X'_rest:
        --        leaf (filter_t X'_rest asn_rest) (X'_h :: filter_f X'_rest asn_rest)
        --
        -- Apply IH on rest_h with leaf' Y1 Y2 = leaf Y1 (X'_h :: Y2),
        -- asn := asn_rest, pre_B := filter_f pre_B α'.
        conv_rhs =>
          rhs; ext α'; rhs; ext X'_h
          rw [← ih (fun Y1 Y2 => leaf Y1 (X'_h :: Y2)) asn_rest hasn_rest
                ((pre_B.zip α').filterMap (fun p => if p.snd then none else some p.fst))]
        -- RHS: bind α': bind X'_h: bind sub_B'': bind X_T'': bind X_F'':
        --        leaf X_T'' (X'_h :: X_F'')
        --
        -- Step 8: Bool-flip the inner sub_B' on LHS, then refine bind_congr on α' and bind reorder.
        refine Multiset.bind_congr fun α' _ => ?_
        rw [listChoices_bool_symm_bind ((pre_B.zip α').filterMap (fun p => if p.snd then none else some p.fst)).length]
        conv_lhs =>
          rhs; ext sub_B'
          rw [filterMap_t_map_not, filterMap_f_map_not]
        -- LHS-per-α': bind sub_B':
        --   bind X_T ∈ (insertionForest (filter_t rest_h asn_rest) (filter_t (filter_f pre_B α') sub_B')):
        --     bind X'_h ∈ (insertion h (filter_t pre_B α')):
        --       bind F'_F_rest ∈ (insertionForest (filter_f rest_h asn_rest) (filter_f (filter_f pre_B α') sub_B')):
        --         leaf X_T (X'_h :: F'_F_rest)
        --
        -- RHS-per-α': bind X'_h ∈ (insertion h (filter_t pre_B α')):
        --   bind sub_B'': bind X_T'' ∈ (insertionForest (filter_t rest_h asn_rest) (filter_t (filter_f pre_B α') sub_B'')):
        --     bind X_F'' ∈ (insertionForest (filter_f rest_h asn_rest) (filter_f (filter_f pre_B α') sub_B'')):
        --       leaf X_T'' (X'_h :: X_F'')
        --
        -- LHS-per-α': bind sub_B': bind X_T: bind X'_h: bind F'_F_rest: leaf X_T (X'_h :: F'_F_rest)
        -- RHS-per-α': bind X'_h: bind sub_B'': bind X_T'': bind X_F'': leaf X_T'' (X'_h :: X_F'')
        --
        -- Move LHS X'_h to outermost via two swaps using Multiset.bind_bind
        -- (each swap requires the inner multiset to be independent of the outer).
        --
        -- Step 9a: Swap X_T and X'_h (inside bind sub_B'). X'_h's multiset is `insertion h (filter_t pre_B α')`,
        --          which depends on α' but NOT on sub_B' or X_T. So swap is valid.
        conv_lhs =>
          rhs; ext sub_B'
          rw [Multiset.bind_bind]
        -- LHS-per-α': bind sub_B': bind X'_h: bind X_T: bind F'_F_rest: leaf ...
        --
        -- Step 9b: Swap sub_B' and X'_h (outermost two, per-α').
        rw [Multiset.bind_bind]
        -- LHS-per-α': bind X'_h: bind sub_B': bind X_T: bind F'_F_rest: leaf ...
        --
        -- Now LHS and RHS are α-equivalent. Both should be acceptable as identical (rfl-equivalent).


/-! ### §2.2 A3.2 — RHS bridge `assocBucketSum_eq_iteratedQuadSum_outer`

The planar bridge from the 4-bucket `iteratedQuadSum` (with an outer
`asn`-bind partitioning `host_B` into T-side and F_A-side) to the
2-bucket `assocBucketSum` form.

Generalized version with `pre_A`, `pre_B` arguments (and corresponding
`sub_A`, `sub_B` binds on the LHS) is proved by induction on `remaining`.
The base case (remaining = []) consumes the **host-routing split substrate**
`insertionForest_split_pair` (planar identity bridging
`bind sub_B: ifd pre_T_B (filter_t sub_B) ×ˢ ifd pre_FA_B (filter_f sub_B)`
to `(ifd host_B).map (fun X' => (filter_t asn X', filter_f asn X'))`),
combined with `insertionForest_cons_assignment` + `listChoices_append_bind`
on the RHS to align bind structures.
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
    -- Base case (remaining = []): bridge LHS and RHS via insertionForest_split_pair.
    -- Step 1: Reduce both sides to standard form.
    rw [assocBucketSum_nil_remaining]
    conv_lhs =>
      rhs; ext asn; rhs; ext sub_A; rhs; ext sub_B
      rw [iteratedQuadSum_nil_remaining]
    -- Step 2: LHS reorg — swap T' and pre_FA_B' binds.
    conv_lhs =>
      rhs; ext asn; rhs; ext sub_A; rhs; ext sub_B
      rhs; ext pre_T_B'
      rw [Multiset.bind_bind]
    -- LHS: bind asn: bind sub_A: bind sub_B:
    --        bind pre_T_B' ∈ (insertionForest (filter_t host_B asn) (filter_t pre_B sub_B)):
    --          bind pre_FA_B' ∈ (insertionForest (filter_f host_B asn) (filter_f pre_B sub_B)):
    --            bind T' ∈ insertion T (pre_T_B' ++ filter_t pre_A sub_A):
    --              (insertionForest F_A (pre_FA_B' ++ filter_f pre_A sub_A)).map (T' :: ·)
    --
    -- Step 3: Apply insertionForest_split_pair to absorb sub_B + pre_T_B' + pre_FA_B' into bind X'.
    -- Use a `have` to encode the equality at the per-(asn, sub_A) level, then chain via bind_congr.
    -- Define the leaf shape (per asn, sub_A):
    let leaf := fun (sub_A : List Bool) (pre_T_B' pre_FA_B' : List (Planar α)) =>
      (insertion T (pre_T_B' ++ ((pre_A.zip sub_A).filterMap fun p => if p.snd then some p.fst else none))).bind
        fun T' =>
          (insertionForest F_A
              (pre_FA_B' ++ ((pre_A.zip sub_A).filterMap fun p => if p.snd then none else some p.fst))).map
            fun F' => T' :: F'
    -- Apply insertionForest_split_pair per (asn, sub_A) via bind_congr.
    have step3 :
        (Multiset.ofList (listChoices [true, false] host_B.length)).bind (fun asn =>
          (Multiset.ofList (listChoices [true, false] pre_A.length)).bind fun sub_A =>
            (Multiset.ofList (listChoices [true, false] pre_B.length)).bind fun sub_B =>
              (insertionForest ((host_B.zip asn).filterMap fun p => if p.snd then some p.fst else none)
                  ((pre_B.zip sub_B).filterMap fun p => if p.snd then some p.fst else none)).bind fun pre_T_B' =>
                (insertionForest ((host_B.zip asn).filterMap fun p => if p.snd then none else some p.fst)
                    ((pre_B.zip sub_B).filterMap fun p => if p.snd then none else some p.fst)).bind fun pre_FA_B' =>
                  leaf sub_A pre_T_B' pre_FA_B') =
        (Multiset.ofList (listChoices [true, false] host_B.length)).bind fun asn =>
          (Multiset.ofList (listChoices [true, false] pre_A.length)).bind fun sub_A =>
            (insertionForest host_B pre_B).bind fun X' =>
              leaf sub_A
                ((X'.zip asn).filterMap fun p => if p.snd then some p.fst else none)
                ((X'.zip asn).filterMap fun p => if p.snd then none else some p.fst) := by
      refine Multiset.bind_congr fun asn hasn => ?_
      have hasn_len : asn.length = host_B.length := mem_listChoices_bool_length _ _ hasn
      refine Multiset.bind_congr fun sub_A _ => ?_
      exact insertionForest_split_pair host_B (leaf sub_A) asn hasn_len pre_B
    rw [step3]
    -- LHS now: bind asn: bind sub_A:
    --   (insertionForest host_B pre_B).bind X' => leaf sub_A (filter_t X' asn) (filter_f X' asn)
    --
    -- Step 4: Pull X' to outermost. X' independent of asn, sub_A. Two swaps via Multiset.bind_bind.
    -- Inside bind asn: swap bind sub_A and bind X':
    conv_lhs =>
      rhs; ext asn
      rw [Multiset.bind_bind]
    -- LHS: bind asn: bind X': bind sub_A: leaf sub_A (filter_t X' asn) (filter_f X' asn)
    -- Then swap bind asn and bind X':
    rw [Multiset.bind_bind]
    -- LHS: bind X': bind asn: bind sub_A: leaf sub_A (filter_t X' asn) (filter_f X' asn)
    --
    -- Step 5: Manipulate RHS: insertionForest_cons_assignment + listChoices_append_bind + filter decomposition.
    refine Multiset.bind_congr fun X' hX' => ?_
    have hX'_len : X'.length = host_B.length := insertionForest_mem_length host_B pre_B X' hX'
    -- Goal LHS-per-X': bind asn (over |host_B|): bind sub_A (over |pre_A|):
    --                    leaf sub_A (filter_t X' asn) (filter_f X' asn)
    -- Goal RHS-per-X': insertionForest (T :: F_A) (X' ++ pre_A)
    rw [insertionForest_cons_assignment T F_A (X' ++ pre_A)]
    -- RHS-per-X': bind α over |X' ++ pre_A|:
    --              (insertion T (filter_t (X' ++ pre_A) α)).bind T' =>
    --                (insertionForest F_A (filter_f (X' ++ pre_A) α)).map (T' :: ·)
    rw [show ((X' ++ pre_A).length : Nat) = host_B.length + pre_A.length from by
        rw [List.length_append, hX'_len]]
    rw [listChoices_append_bind host_B.length pre_A.length]
    -- RHS-per-X': bind a over |host_B|: bind b over |pre_A|:
    --              (insertion T (filter_t (X' ++ pre_A) (a ++ b))).bind T' =>
    --                (insertionForest F_A (filter_f (X' ++ pre_A) (a ++ b))).map (T' :: ·)
    -- Decompose filter via zip_append + filterMap_append.
    refine Multiset.bind_congr fun a ha => ?_
    have ha_len : a.length = host_B.length := mem_listChoices_bool_length _ _ ha
    refine Multiset.bind_congr fun b _ => ?_
    -- Goal: leaf b (filter_t X' a) (filter_f X' a) =
    --       (insertion T (filter_t (X' ++ pre_A) (a ++ b))).bind T' =>
    --         (insertionForest F_A (filter_f (X' ++ pre_A) (a ++ b))).map (T' :: ·)
    rw [show ((X' ++ pre_A).zip (a ++ b)) = X'.zip a ++ pre_A.zip b from
          List.zip_append (by omega : X'.length = a.length)]
    rw [List.filterMap_append, List.filterMap_append]
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

/-! ### §2.3 A3.3 — LHS bridge to `iteratedQuadSum` (per-asn1, msform level)

The substantive bridge from the iterated-grafting LHS form to the
4-bucket `iteratedQuadSum` aggregator, at the multiset-of-multiset
level. This is the combinatorial heart of Oudom-Guin Prop 2.7.v at
the planar-list level.

**Bijection statement.** For T, F_A, pre_T_B, pre_FA_B, C:

    bind T_ins ∈ insertion T pre_T_B:
      bind F_ins ∈ insertionForest F_A pre_FA_B:
        insertionForest (T_ins :: F_ins) C
    ≡ (msform)
    iteratedQuadSum T F_A pre_T_B pre_FA_B (fun _ => []) C

**Path-level bijection.** Each c ∈ C targets a vertex of T_ins :: F_ins.
By `vertices_multiGraft_decomp` (Graft.lean §9), V(T_ins) decomposes
into 3 classes (preserved/sourceSelf/lifted), with:
- preserved + sourceSelf = V(T) (modulo path-transport via grafting),
- lifted = V(pre_T_B-trees) (each tree's vertices, lifted into T_ins).

Similarly V(F_ins) decomposes into V(F_A) + V(pre_FA_B). So V(T_ins :: F_ins)
partitions into 4 classes:
- V(T) (T_orig bucket)
- V(pre_T_B, lifted) (T_graft bucket)
- V(F_A) (FA_orig bucket)
- V(pre_FA_B, lifted) (FA_graft bucket)

Each c independently picks a class (4-valued α(c) : QuadIdx) and a target
within that class. The 4-bucket sum-over-α form is `iteratedQuadSum`.

**Why msform.** At the planar level, the order of children at each vertex
matters; LHS produces a specific planar arrangement (T_ins's children in
B-then-C order at each grafted vertex). RHS's iteratedQuadSum produces a
DIFFERENT planar arrangement (B-trees pre-grafted, then C-trees added at
T's level). These differ at planar level but agree under
`Multiset.ofList ∘ List.map Nonplanar.mk` (msform) — msform discards the
planar order at each vertex via `Nonplanar.mk`'s `PlanarEquiv` quotient.

**Proof status.** Substantive substrate, deferred. The proof requires:
1. Apply `vertices_multiGraft_decomp` to V(T_ins) and V(F_ins).
2. Reorganize the C-targeting sum by α-bucket.
3. Show each per-α leaf form matches `iteratedQuadSum`'s leaf with
   appropriate pres-distribution.
4. Use `multiGraft_perm_pair` (PE-invariance under pair-list permutation)
   to absorb planar-order differences at msform level.

This is mathlib-quality work (~300-500 LOC of path-level substrate).
Unblocking it closes `assocBucketSum_eq_insertionForest_iterated_msform`
and downstream `Nonplanar.insertionMultiset_assoc`. -/

/-- A3.3 cons-case sorry-fence (Phase 4.2 of `scratch/a33_phase5_design.md`).
    States the LHS form equals the bind-α form of `iteratedQuadSum`-leaves
    (modulo msform). After this lemma, the headline `LHS_eq_iteratedQuadSum_msform`
    cons-case closes via a single `rw [iteratedQuadSum_eq_alphaBind]` (Phase 2.1)
    + `exact`. The proof of THIS sorry-fence is the substantive bijection
    (~280 LOC, Phases 5.1.A + 5.1.B + 4.2 from the design plan).

    Why this articulation? The original cons-case sorry was a single deeply-buried
    statement mixing bind reordering, vertex-class identification, and planar-equiv
    reasoning. This helper isolates the bind-α form alignment, with the per-α leaf
    bridge being the only remaining substrate gap. RHS-bind structure now matches
    Phase 2.1's `iteratedQuadSum_eq_alphaBind`, so consumers can rewrite once to
    expose the per-α structure on both sides.

    Substantive substrate gap: the LHS-side bind-α form (`LHS_split_by_alpha` in
    the design plan) requires `vertices_forest_eq_partition` (Phase 3.2,
    sorry-free) + path-level substrate `multiGraft_split_lifted_aux` (~60-80 LOC,
    optional baby compose lemma). -/
private theorem LHS_eq_iteratedQuadSum_msform_cons_alphaBind
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (c : Planar α) (rest : List (Planar α)) :
    ((insertion T pre_T_B).bind fun T_ins =>
        (insertionForest F_A pre_FA_B).bind fun F_ins =>
          insertionForest (T_ins :: F_ins) (c :: rest)).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((Multiset.ofList (listChoices
        [QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft]
        (c :: rest).length)).bind fun a =>
      iteratedQuadSum T F_A pre_T_B pre_FA_B
        (fun t => bucketSlice (c :: rest) a t) []).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- TODO (Phase 4.2 substantive): see scratch/a33_phase5_design.md.
  -- Strategy: unfold LHS via verticesAux_cons + vertices_forest_eq_partition
  -- to expose bind-α structure, then bind_congr per α + per-α leaf bijection
  -- using multiGraft_perm_pair + insertion_planarEquiv_guests.
  sorry

/-- A3.3: LHS-iteratedQuadSum bridge at msform level (per-asn1).
    Substantive bijection; the cons case closes via the sorry-fenced helper
    `LHS_eq_iteratedQuadSum_msform_cons_alphaBind` (Phase 4.2) composed with
    `iteratedQuadSum_eq_alphaBind` (Phase 2.1, sorry-free). -/
private theorem LHS_eq_iteratedQuadSum_msform
    (T : Planar α) (F_A pre_T_B pre_FA_B C : List (Planar α)) :
    ((insertion T pre_T_B).bind fun T_ins =>
        (insertionForest F_A pre_FA_B).bind fun F_ins =>
          insertionForest (T_ins :: F_ins) C).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    (iteratedQuadSum T F_A pre_T_B pre_FA_B (fun _ => []) C).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  cases C with
  | nil =>
    -- Base case C = []: both sides reduce to
    -- (insertion T pre_T_B).bind T_ins => (ifd F_A pre_FA_B).map (T_ins :: ·).
    -- LHS: ifd (T_ins :: F_ins) [] = {T_ins :: F_ins}, so the inner bind collapses
    --      to (ifd F_A pre_FA_B).map (T_ins :: ·) via Multiset.bind_singleton.
    -- RHS: iteratedQuadSum-leaf with pres = (fun _ => []) reduces:
    --      ({pre_T_B}).bind pre_T_B' => (insertion T pre_T_B').bind T' =>
    --        ({pre_FA_B}).bind pre_FA_B' => (ifd F_A pre_FA_B').map (T' :: ·)
    --   ⇒ (insertion T pre_T_B).bind T' => (ifd F_A pre_FA_B).map (T' :: ·)
    --   via two Multiset.singleton_bind reductions.
    rw [iteratedQuadSum_nil_remaining]
    simp only [insertionForest_nil_guests, List.append_nil, Multiset.singleton_bind,
               Multiset.bind_singleton]
  | cons c rest =>
    -- Cons case: Phase 6.1 closure. RHS rewritten via Phase 2.1, then the
    -- sorry-fenced cons-case helper closes the per-α leaf alignment.
    rw [iteratedQuadSum_eq_alphaBind]
    exact LHS_eq_iteratedQuadSum_msform_cons_alphaBind T F_A pre_T_B pre_FA_B c rest

/-- Helper: per-asn1 LHS rearrangement for the deep case.
    Bridges the iterated `(bind T_ins: ... map (T_ins :: ·)).bind X => ifd X C`
    form to the cleaner `(insertion T pre_T_B).bind T_ins => (ifd F_A pre_FA_B).bind F_ins => ifd (T_ins :: F_ins) C`
    form via `Multiset.bind_assoc` + `Multiset.bind_map`. -/
private lemma lhs_per_asn_rearrange
    (T : Planar α) (F_A pre_T_B pre_FA_B C : List (Planar α)) :
    ((insertion T pre_T_B).bind fun T_ins =>
        (insertionForest F_A pre_FA_B).map (T_ins :: ·)).bind
      (fun X => insertionForest X C) =
    (insertion T pre_T_B).bind fun T_ins =>
      (insertionForest F_A pre_FA_B).bind fun F_ins =>
        insertionForest (T_ins :: F_ins) C := by
  rw [Multiset.bind_assoc]
  refine Multiset.bind_congr fun T_ins _ => ?_
  rw [Multiset.bind_map]

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
      **reduced to A3.3**. Proof chain:
        - `assocBucketSum_eq_iteratedQuadSum_outer` (A3.2-spec, sorry-free)
          bridges RHS to the iteratedQuadSum-with-asn1-outer form.
        - Per-asn1 bind_congr + `lhs_per_asn_rearrange` (sorry-free)
          brings LHS to A3.3's input shape.
        - `LHS_eq_iteratedQuadSum_msform` (A3.3, **substantive bijection,
          currently sorry**) closes the per-asn1 bridge.
      A3.3 is the combinatorial heart of Oudom-Guin Prop 2.7.v at the
      planar-list level. Path-level substrate (~300-500 LOC) needed to
      close it via `vertices_multiGraft_decomp` + `multiGraft_perm_pair`.

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
        -- The deepest combinatorial case. Reduced to two substrate pieces:
        --   - `assocBucketSum_eq_iteratedQuadSum_outer` (A3.2-spec, sorry-free)
        --     bridges RHS to the iteratedQuadSum-with-asn1-outer form.
        --   - `LHS_eq_iteratedQuadSum_msform` (A3.3, substantive substrate)
        --     bridges per-asn1 LHS to iteratedQuadSum at msform level.
        --
        -- The proof: rewrite RHS via A3.2-spec, expand LHS via cons_assignment,
        -- pull msform through the binds, and refine bind_congr to the per-asn1
        -- bridge.
        --
        -- See the docstring of `LHS_eq_iteratedQuadSum_msform` (above) for
        -- the substantive substrate gap (~300-500 LOC of path-level work
        -- via `vertices_multiGraft_decomp` + `multiGraft_perm_pair`).
        --
        -- ## Downstream impact
        --
        -- Closes the planar bridge for `Nonplanar.insertionMultiset_assoc`
        -- (currently sorry in `GrossmanLarsonAssoc.lean:455`). Unblocks
        -- `insertion_assoc_shuffled` (Oudom-Guin Prop 2.7.v at the algebra
        -- level) and the GL-pre-Lie associativity chain.
        rw [← assocBucketSum_eq_iteratedQuadSum_outer T F_A (b :: restB) (c :: rest)]
        -- Goal: ((ifd (T :: F_A) (b :: restB)).bind X => ifd X (c :: rest)).map msform
        --     = (bind asn1: iteratedQuadSum T F_A (filter_t (b::restB) asn1)
        --                                  (filter_f (b::restB) asn1) (fun _ => []) (c :: rest)).map msform
        --
        -- Step 1: Expand LHS via insertionForest_cons_assignment T F_A (b :: restB).
        rw [insertionForest_cons_assignment T F_A (b :: restB)]
        -- LHS = ((bind asn1: bind T_ins ∈ insertion T (filter_t (b::restB) asn1):
        --          (ifd F_A (filter_f (b::restB) asn1)).map (T_ins :: ·)).bind X => ifd X (c :: rest)).map msform
        --
        -- Step 2: Push outer .bind X through the asn1-bind via Multiset.bind_assoc.
        rw [Multiset.bind_assoc]
        -- LHS = (bind asn1: ((bind T_ins: (ifd F_A ...).map (T_ins :: ·)).bind X => ifd X (c :: rest))).map msform
        --
        -- Step 3: Push .map msform through outer asn1-bind on both sides.
        rw [Multiset.map_bind]
        -- LHS = bind asn1: ((bind T_ins: (ifd F_A ...).map (T_ins :: ·)).bind X => ifd X (c :: rest)).map msform
        rw [Multiset.map_bind]
        -- RHS = bind asn1: (iteratedQuadSum T F_A ... (fun _ => []) (c :: rest)).map msform
        --
        -- Step 4: Per-asn1 bridge via bind_congr + lhs_per_asn_rearrange + A3.3.
        refine Multiset.bind_congr fun asn1 _ => ?_
        -- Per-asn1 goal: ((bind T_ins ∈ insertion T (filter_t (b::restB) asn1):
        --                   (ifd F_A (filter_f (b::restB) asn1)).map (T_ins :: ·)).bind X =>
        --                    ifd X (c :: rest)).map msform
        --              = (iteratedQuadSum T F_A (filter_t (b::restB) asn1) (filter_f (b::restB) asn1)
        --                                  (fun _ => []) (c :: rest)).map msform
        --
        -- Apply lhs_per_asn_rearrange to bring per-asn1 LHS to A3.3-LHS shape.
        rw [lhs_per_asn_rearrange T F_A
              (((b :: restB).zip asn1).filterMap (fun p => if p.snd then some p.fst else none))
              (((b :: restB).zip asn1).filterMap (fun p => if p.snd then none else some p.fst))
              (c :: rest)]
        -- Per-asn1 LHS now matches A3.3's LHS shape:
        --   ((insertion T pre_T_B).bind T_ins => (ifd F_A pre_FA_B).bind F_ins =>
        --      ifd (T_ins :: F_ins) (c :: rest)).map msform
        --
        -- Apply A3.3 (LHS_eq_iteratedQuadSum_msform).
        exact LHS_eq_iteratedQuadSum_msform T F_A
          (((b :: restB).zip asn1).filterMap (fun p => if p.snd then some p.fst else none))
          (((b :: restB).zip asn1).filterMap (fun p => if p.snd then none else some p.fst))
          (c :: rest)

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
