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
  (C = []) of A3.3; canonical-form skeleton (§1.9) including its C = []
  base case (`interpret_C_nil`, `enumGraftingData_zero`, `LHS_eq_canonical_C_nil`).
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

/-- Pres-generalized flat α-bind form for `iteratedQuadSum`. Each `α : List
    QuadIdx` of length `C.length` selects per-c which bucket consumes that c;
    the leaf form prepends `pres t` to the resulting per-bucket slice of `C`.

    Specializes to `iteratedQuadSum_eq_alphaBind` at `pres = (fun _ => [])`.
    Required for the cons-case of `RHS_eq_canonical_msform`: after
    `iteratedQuadSum_cons_remaining`, the inner pres is
    `Function.update (fun _ => []) first [c]`, so the more general form is
    needed to expose the α-bind on the inner-pres iteratedQuadSum-leaf. -/
private theorem iteratedQuadSum_eq_alphaBind_general
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (pres : QuadIdx → List (Planar α)) (C : List (Planar α)) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B pres C =
      (Multiset.ofList (listChoices
          [QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft]
          C.length)).bind fun a =>
        iteratedQuadSum T F_A pre_T_B pre_FA_B
          (fun t => pres t ++ bucketSlice C a t) [] := by
  rw [iteratedQuadSum_eq_kBucketSum, kBucketSum_assignment_rewrite]
  refine Multiset.bind_congr fun a _ => ?_
  rw [iteratedQuadSum_nil_remaining]

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

/-! ### §1.8.0 mergeData + decomposition substrate (cons-case scaffolding)

Substrate for the cons case of `insertionForest_eq_explicit`. Given a Boolean
assignment `α` of length `pre_FA_B.length` (`true` = goes to T, `false` = goes
to F_rest), a per-T-position choice list `c_T : List Path`, and a per-F_rest-
position choice list `fdata : List (Fin F_rest.length × Path)`, we interleave
to a single `data : List (Fin (F_rest.length + 1) × Path)` of the same length
as `α`. -/

/-- Interleave a Boolean assignment with per-bucket data. Walks `α` left-to-
    right; consumes one entry of `c_T` per `true` bit (emitting `(0, v)`) and
    one entry of `fdata` per `false` bit (emitting `(j.succ, v)`). Truncates
    if a list runs out (defensive). -/
private def mergeData {n : Nat} :
    List Bool → List Path → List (Fin n × Path) → List (Fin (n + 1) × Path)
  | [], _, _ => []
  | true :: α', c_T, fdata =>
      match c_T with
      | [] => []
      | v :: c_T' => ((0 : Fin (n + 1)), v) :: mergeData α' c_T' fdata
  | false :: α', c_T, fdata =>
      match fdata with
      | [] => []
      | p :: fdata' => (p.fst.succ, p.snd) :: mergeData α' c_T fdata'

@[simp] private theorem mergeData_nil {n : Nat}
    (c_T : List Path) (fdata : List (Fin n × Path)) :
    mergeData [] c_T fdata = [] := rfl

@[simp] private theorem mergeData_true_cons_nil {n : Nat}
    (α' : List Bool) (fdata : List (Fin n × Path)) :
    mergeData (true :: α') [] fdata = [] := rfl

@[simp] private theorem mergeData_true_cons_cons {n : Nat}
    (α' : List Bool) (v : Path) (c_T' : List Path)
    (fdata : List (Fin n × Path)) :
    mergeData (true :: α') (v :: c_T') fdata =
      ((0 : Fin (n + 1)), v) :: mergeData α' c_T' fdata := rfl

@[simp] private theorem mergeData_false_cons_nil {n : Nat}
    (α' : List Bool) (c_T : List Path) :
    mergeData (n := n) (false :: α') c_T [] = [] := rfl

@[simp] private theorem mergeData_false_cons_cons {n : Nat}
    (α' : List Bool) (c_T : List Path)
    (p : Fin n × Path) (fdata' : List (Fin n × Path)) :
    mergeData (false :: α') c_T (p :: fdata') =
      (p.fst.succ, p.snd) :: mergeData α' c_T fdata' := rfl

/-- Length lemma: `filter_t pre_FA_B α` has length `α.count true` (when lengths match). -/
private theorem filter_t_length (pre_FA_B : List (Planar α)) (α_assn : List Bool)
    (h : pre_FA_B.length = α_assn.length) :
    ((pre_FA_B.zip α_assn).filterMap (fun p => if p.snd then some p.fst else none)).length =
      α_assn.count true := by
  induction α_assn generalizing pre_FA_B with
  | nil =>
    have hpf : pre_FA_B = [] := List.length_eq_zero_iff.mp (by rw [h]; rfl)
    subst hpf; rfl
  | cons a α' ih =>
    cases pre_FA_B with
    | nil => simp at h
    | cons g rest =>
      have hrest : rest.length = α'.length := by
        rw [List.length_cons, List.length_cons] at h; omega
      rw [List.zip_cons_cons, List.filterMap_cons]
      cases a with
      | true =>
        rw [if_pos rfl, List.length_cons, ih rest hrest, List.count_cons_self]
      | false =>
        rw [if_neg (by decide : ¬ (false : Bool) = true), ih rest hrest,
            show (false :: α').count true = α'.count true from by
              simp only [List.count_cons]; rfl]

/-- Length lemma: `filter_f pre_FA_B α` has length `α.count false` (when lengths match). -/
private theorem filter_f_length (pre_FA_B : List (Planar α)) (α_assn : List Bool)
    (h : pre_FA_B.length = α_assn.length) :
    ((pre_FA_B.zip α_assn).filterMap (fun p => if p.snd then none else some p.fst)).length =
      α_assn.count false := by
  induction α_assn generalizing pre_FA_B with
  | nil =>
    have hpf : pre_FA_B = [] := List.length_eq_zero_iff.mp (by rw [h]; rfl)
    subst hpf; rfl
  | cons a α' ih =>
    cases pre_FA_B with
    | nil => simp at h
    | cons g rest =>
      have hrest : rest.length = α'.length := by
        rw [List.length_cons, List.length_cons] at h; omega
      rw [List.zip_cons_cons, List.filterMap_cons]
      cases a with
      | true =>
        rw [if_pos rfl, ih rest hrest,
            show (true :: α').count false = α'.count false from by
              simp only [List.count_cons]; rfl]
      | false =>
        rw [if_neg (by decide : ¬ (false : Bool) = true), List.length_cons,
            ih rest hrest, List.count_cons_self]

/-- Atomic reduction: `perTreePairsFromFChoice` on `(0, v) :: data` at index `0`
    extracts `(v, g)` then recurses. -/
private theorem perTreePairsFromFChoice_cons_zero_at_zero
    (T : Planar α) (F_rest : List (Planar α))
    (data : List (Fin (F_rest.length + 1) × Path)) (g : Planar α)
    (pre_FA_B : List (Planar α)) (v : Path) :
    perTreePairsFromFChoice (T :: F_rest) (g :: pre_FA_B)
        (((0 : Fin (F_rest.length + 1)), v) :: data)
        (0 : Fin (F_rest.length + 1)) =
      (v, g) :: perTreePairsFromFChoice (T :: F_rest) pre_FA_B data
        (0 : Fin (F_rest.length + 1)) := by
  unfold perTreePairsFromFChoice
  rw [List.zip_cons_cons, List.filterMap_cons]
  dsimp only
  rw [if_pos rfl]

/-- Atomic reduction: `perTreePairsFromFChoice` on `(0, v) :: data` at index `j.succ`
    drops the head (since `0 ≠ j.succ`). -/
private theorem perTreePairsFromFChoice_cons_zero_at_succ
    (T : Planar α) (F_rest : List (Planar α))
    (data : List (Fin (F_rest.length + 1) × Path)) (g : Planar α)
    (pre_FA_B : List (Planar α)) (v : Path) (j : Fin F_rest.length) :
    perTreePairsFromFChoice (T :: F_rest) (g :: pre_FA_B)
        (((0 : Fin (F_rest.length + 1)), v) :: data) j.succ =
      perTreePairsFromFChoice (T :: F_rest) pre_FA_B data j.succ := by
  unfold perTreePairsFromFChoice
  rw [List.zip_cons_cons, List.filterMap_cons]
  dsimp only
  rw [if_neg (fun h => Fin.succ_ne_zero j h.symm)]

/-- Atomic reduction: `perTreePairsFromFChoice` on `(p.fst.succ, p.snd) :: data` at
    index `0` drops the head (since `p.fst.succ ≠ 0`). -/
private theorem perTreePairsFromFChoice_cons_succ_at_zero
    (T : Planar α) (F_rest : List (Planar α))
    (data : List (Fin (F_rest.length + 1) × Path)) (g : Planar α)
    (pre_FA_B : List (Planar α)) (p : Fin F_rest.length × Path) :
    perTreePairsFromFChoice (T :: F_rest) (g :: pre_FA_B)
        ((p.fst.succ, p.snd) :: data)
        (0 : Fin (F_rest.length + 1)) =
      perTreePairsFromFChoice (T :: F_rest) pre_FA_B data
        (0 : Fin (F_rest.length + 1)) := by
  unfold perTreePairsFromFChoice
  rw [List.zip_cons_cons, List.filterMap_cons]
  dsimp only
  rw [if_neg (Fin.succ_ne_zero p.fst)]

/-- Atomic reduction (matching case): `perTreePairsFromFChoice` on `(p.fst.succ,
    p.snd) :: data` at `j.succ` when `p.fst = j` extracts `(p.snd, g)` and recurses. -/
private theorem perTreePairsFromFChoice_cons_succ_at_succ_eq
    (T : Planar α) (F_rest : List (Planar α))
    (data : List (Fin (F_rest.length + 1) × Path)) (g : Planar α)
    (pre_FA_B : List (Planar α)) (p : Fin F_rest.length × Path)
    (j : Fin F_rest.length) (hpj : p.fst = j) :
    perTreePairsFromFChoice (T :: F_rest) (g :: pre_FA_B)
        ((p.fst.succ, p.snd) :: data) j.succ =
      (p.snd, g) :: perTreePairsFromFChoice (T :: F_rest) pre_FA_B data j.succ := by
  unfold perTreePairsFromFChoice
  rw [List.zip_cons_cons, List.filterMap_cons]
  dsimp only
  rw [if_pos (show p.fst.succ = j.succ from by rw [hpj])]

/-- Atomic reduction (non-matching case): drops the head when `p.fst ≠ j`. -/
private theorem perTreePairsFromFChoice_cons_succ_at_succ_neq
    (T : Planar α) (F_rest : List (Planar α))
    (data : List (Fin (F_rest.length + 1) × Path)) (g : Planar α)
    (pre_FA_B : List (Planar α)) (p : Fin F_rest.length × Path)
    (j : Fin F_rest.length) (hpj : p.fst ≠ j) :
    perTreePairsFromFChoice (T :: F_rest) (g :: pre_FA_B)
        ((p.fst.succ, p.snd) :: data) j.succ =
      perTreePairsFromFChoice (T :: F_rest) pre_FA_B data j.succ := by
  unfold perTreePairsFromFChoice
  rw [List.zip_cons_cons, List.filterMap_cons]
  dsimp only
  rw [if_neg (fun h => hpj (by
    have hval : p.fst.succ.val = j.succ.val := congrArg Fin.val h
    simp only [Fin.val_succ] at hval
    exact Fin.ext (Nat.succ_inj.mp hval)))]

/-- Atomic reduction (matching case): per-F_rest pair extraction on `p :: pf_data`
    at index `j` when `p.fst = j` extracts `(p.snd, g)` and recurses. -/
private theorem perTreePairsFromFChoice_F_cons_eq
    (F_rest : List (Planar α))
    (data : List (Fin F_rest.length × Path)) (g : Planar α)
    (pre_FA_B : List (Planar α)) (p : Fin F_rest.length × Path)
    (j : Fin F_rest.length) (hpj : p.fst = j) :
    perTreePairsFromFChoice F_rest (g :: pre_FA_B) (p :: data) j =
      (p.snd, g) :: perTreePairsFromFChoice F_rest pre_FA_B data j := by
  unfold perTreePairsFromFChoice
  rw [List.zip_cons_cons, List.filterMap_cons]
  dsimp only
  rw [if_pos hpj]

/-- Atomic reduction (non-matching case): drops the head when `p.fst ≠ j`. -/
private theorem perTreePairsFromFChoice_F_cons_neq
    (F_rest : List (Planar α))
    (data : List (Fin F_rest.length × Path)) (g : Planar α)
    (pre_FA_B : List (Planar α)) (p : Fin F_rest.length × Path)
    (j : Fin F_rest.length) (hpj : p.fst ≠ j) :
    perTreePairsFromFChoice F_rest (g :: pre_FA_B) (p :: data) j =
      perTreePairsFromFChoice F_rest pre_FA_B data j := by
  unfold perTreePairsFromFChoice
  rw [List.zip_cons_cons, List.filterMap_cons]
  dsimp only
  rw [if_neg hpj]

/-- For pairs targeting `T = (T :: F_rest)[0]`: the per-tree pairs extracted from
    `mergeData α c_T fdata` reduce to `c_T.zip (filter_t pre_FA_B α)`. -/
private theorem perTreePairsFromFChoice_mergeData_zero
    (T : Planar α) (F_rest : List (Planar α)) (pre_FA_B : List (Planar α))
    (α_assn : List Bool) (c_T : List Path)
    (fdata : List (Fin F_rest.length × Path))
    (hpf : pre_FA_B.length = α_assn.length)
    (hc : c_T.length = α_assn.count true)
    (hf : fdata.length = α_assn.count false) :
    perTreePairsFromFChoice (T :: F_rest) pre_FA_B
        (mergeData α_assn c_T fdata) (0 : Fin (F_rest.length + 1)) =
      c_T.zip ((pre_FA_B.zip α_assn).filterMap
        (fun p => if p.snd then some p.fst else none)) := by
  induction α_assn generalizing pre_FA_B c_T fdata with
  | nil =>
    have hc_zero : c_T = [] := by
      apply List.length_eq_zero_iff.mp
      have : ([] : List Bool).count true = 0 := rfl
      omega
    have hpf_nil : pre_FA_B = [] := by
      apply List.length_eq_zero_iff.mp
      omega
    subst hc_zero; subst hpf_nil
    rfl
  | cons a α' ih =>
    cases pre_FA_B with
    | nil => simp at hpf
    | cons g rest =>
      have hrest_len : rest.length = α'.length := by
        simp only [List.length_cons] at hpf; omega
      cases a with
      | true =>
        have hc_pos : c_T.length = α'.count true + 1 := by
          rw [hc, List.count_cons_self]
        cases c_T with
        | nil => simp at hc_pos
        | cons v c_T' =>
          rw [mergeData_true_cons_cons]
          rw [perTreePairsFromFChoice_cons_zero_at_zero]
          have hc' : c_T'.length = α'.count true := by
            simp only [List.length_cons] at hc_pos; omega
          have hf' : fdata.length = α'.count false := by
            rw [hf]; simp only [List.count_cons]; rfl
          have ih_eq := ih rest c_T' fdata hrest_len hc' hf'
          -- Goal: (v, g) :: perTreePairsFromFChoice ... rest (mergeData α' c_T' fdata) 0
          --     = (v :: c_T').zip ((g :: rest).zip (true :: α').filterMap ...)
          -- RHS: (g :: rest).zip (true :: α') = (g, true) :: rest.zip α'
          --     filterMap of (g, true) :: ... = g :: filterMap rest
          --     (v :: c_T').zip (g :: filter_t rest α') = (v, g) :: c_T'.zip (filter_t rest α')
          rw [List.zip_cons_cons, List.filterMap_cons]
          dsimp only
          rw [if_pos rfl]
          rw [List.zip_cons_cons]
          rw [ih_eq]
      | false =>
        have hf_pos : fdata.length = α'.count false + 1 := by
          rw [hf, List.count_cons_self]
        cases fdata with
        | nil => simp at hf_pos
        | cons p fdata' =>
          rw [mergeData_false_cons_cons]
          rw [perTreePairsFromFChoice_cons_succ_at_zero]
          have hc' : c_T.length = α'.count true := by
            rw [hc]; simp only [List.count_cons]; rfl
          have hf' : fdata'.length = α'.count false := by
            simp only [List.length_cons] at hf_pos; omega
          have ih_eq := ih rest c_T fdata' hrest_len hc' hf'
          -- Goal: perTreePairsFromFChoice ... rest (mergeData α' c_T fdata') 0
          --     = c_T.zip ((g :: rest).zip (false :: α').filterMap ...)
          -- RHS: (g :: rest).zip (false :: α') = (g, false) :: rest.zip α'
          --     filterMap drops (g, false) → none. Result: filter_t rest α'.
          rw [List.zip_cons_cons, List.filterMap_cons]
          dsimp only
          rw [if_neg (by decide : ¬ (false : Bool) = true)]
          exact ih_eq

/-- For pairs targeting `F_rest[j] = (T :: F_rest)[j.succ.val]`. -/
private theorem perTreePairsFromFChoice_mergeData_succ
    (T : Planar α) (F_rest : List (Planar α)) (pre_FA_B : List (Planar α))
    (α_assn : List Bool) (c_T : List Path)
    (fdata : List (Fin F_rest.length × Path)) (j : Fin F_rest.length)
    (hpf : pre_FA_B.length = α_assn.length)
    (hc : c_T.length = α_assn.count true)
    (hf : fdata.length = α_assn.count false) :
    perTreePairsFromFChoice (T :: F_rest) pre_FA_B
        (mergeData α_assn c_T fdata) j.succ =
      perTreePairsFromFChoice F_rest
        ((pre_FA_B.zip α_assn).filterMap
          (fun p => if p.snd then none else some p.fst)) fdata j := by
  induction α_assn generalizing pre_FA_B c_T fdata with
  | nil =>
    have hf_zero : fdata = [] := by
      apply List.length_eq_zero_iff.mp
      have : ([] : List Bool).count false = 0 := rfl
      omega
    have hpf_nil : pre_FA_B = [] := by
      apply List.length_eq_zero_iff.mp
      omega
    subst hf_zero; subst hpf_nil
    rfl
  | cons a α' ih =>
    cases pre_FA_B with
    | nil => simp at hpf
    | cons g rest =>
      have hrest_len : rest.length = α'.length := by
        simp only [List.length_cons] at hpf; omega
      cases a with
      | true =>
        have hc_pos : c_T.length = α'.count true + 1 := by
          rw [hc, List.count_cons_self]
        cases c_T with
        | nil => simp at hc_pos
        | cons v c_T' =>
          rw [mergeData_true_cons_cons]
          rw [perTreePairsFromFChoice_cons_zero_at_succ]
          have hc' : c_T'.length = α'.count true := by
            simp only [List.length_cons] at hc_pos; omega
          have hf' : fdata.length = α'.count false := by
            rw [hf]; simp only [List.count_cons]; rfl
          have ih_eq := ih rest c_T' fdata hrest_len hc' hf'
          rw [List.zip_cons_cons, List.filterMap_cons]
          dsimp only
          rw [if_pos rfl]
          exact ih_eq
      | false =>
        have hf_pos : fdata.length = α'.count false + 1 := by
          rw [hf, List.count_cons_self]
        cases fdata with
        | nil => simp at hf_pos
        | cons p fdata' =>
          rw [mergeData_false_cons_cons]
          have hc' : c_T.length = α'.count true := by
            rw [hc]; simp only [List.count_cons]; rfl
          have hf' : fdata'.length = α'.count false := by
            simp only [List.length_cons] at hf_pos; omega
          have ih_eq := ih rest c_T fdata' hrest_len hc' hf'
          rw [List.zip_cons_cons, List.filterMap_cons]
          dsimp only
          rw [if_neg (by decide : ¬ (false : Bool) = true)]
          by_cases hpj : p.fst = j
          · rw [perTreePairsFromFChoice_cons_succ_at_succ_eq T F_rest _ g rest p j hpj]
            rw [perTreePairsFromFChoice_F_cons_eq F_rest fdata' g _ p j hpj]
            rw [ih_eq]
          · rw [perTreePairsFromFChoice_cons_succ_at_succ_neq T F_rest _ g rest p j hpj]
            rw [perTreePairsFromFChoice_F_cons_neq F_rest fdata' g _ p j hpj]
            exact ih_eq

/-- The cons-case decomposition of `buildFIns`: builds the (T :: F_rest) output from
    the (α, c_T, fdata) triple as `multiGraft T (c_T.zip (filter_t pre_FA_B α)) ::
    buildFIns F_rest (filter_f pre_FA_B α) fdata`. Composes the two
    `perTreePairsFromFChoice_mergeData_*` lemmas. -/
private theorem buildFIns_cons_decompose
    (T : Planar α) (F_rest : List (Planar α)) (pre_FA_B : List (Planar α))
    (α_assn : List Bool) (c_T : List Path)
    (fdata : List (Fin F_rest.length × Path))
    (hpf : pre_FA_B.length = α_assn.length)
    (hc : c_T.length = α_assn.count true)
    (hf : fdata.length = α_assn.count false) :
    buildFIns (T :: F_rest) pre_FA_B (mergeData α_assn c_T fdata) =
      multiGraft T
        (c_T.zip ((pre_FA_B.zip α_assn).filterMap
          (fun p => if p.snd then some p.fst else none))) ::
      buildFIns F_rest
        ((pre_FA_B.zip α_assn).filterMap
          (fun p => if p.snd then none else some p.fst)) fdata := by
  show (List.finRange (F_rest.length + 1)).map
        (fun i : Fin (F_rest.length + 1) =>
          multiGraft ((T :: F_rest)[i.val])
            (perTreePairsFromFChoice (T :: F_rest) pre_FA_B
              (mergeData α_assn c_T fdata) i)) = _
  rw [List.finRange_succ, List.map_cons]
  -- Head: index 0. (T :: F_rest)[0] = T.
  -- Tail: ((List.finRange F_rest.length).map Fin.succ).map (...)
  congr 1
  · -- Head case: multiGraft T (perTreePairsFromFChoice ... 0) = multiGraft T (c_T.zip ...)
    show multiGraft T (perTreePairsFromFChoice (T :: F_rest) pre_FA_B
            (mergeData α_assn c_T fdata) (0 : Fin (F_rest.length + 1))) = _
    rw [perTreePairsFromFChoice_mergeData_zero T F_rest pre_FA_B α_assn c_T fdata
        hpf hc hf]
  · -- Tail case
    show ((List.finRange F_rest.length).map Fin.succ).map
          (fun i : Fin (F_rest.length + 1) =>
            multiGraft ((T :: F_rest)[i.val])
              (perTreePairsFromFChoice (T :: F_rest) pre_FA_B
                (mergeData α_assn c_T fdata) i)) =
        (List.finRange F_rest.length).map (fun j : Fin F_rest.length =>
          multiGraft F_rest[j.val]
            (perTreePairsFromFChoice F_rest
              ((pre_FA_B.zip α_assn).filterMap
                (fun p => if p.snd then none else some p.fst))
              fdata j))
    rw [List.map_map]
    refine List.map_congr_left fun j _ => ?_
    show multiGraft (F_rest[j.val])
          (perTreePairsFromFChoice (T :: F_rest) pre_FA_B
            (mergeData α_assn c_T fdata) j.succ) = _
    rw [perTreePairsFromFChoice_mergeData_succ T F_rest pre_FA_B α_assn c_T fdata
        j hpf hc hf]

/-- Alphabet decomposition: per-vertex choice for a `T :: F_rest` forest splits
    into the T's vertices (paired with index `0`) and the F_rest forest's own
    choice (lifted via `Fin.succ`). -/
private theorem perKFChoice_cons (T : Planar α) (F_rest : List (Planar α)) :
    perKFChoice (T :: F_rest) =
      (vertices T).map (fun v => ((0 : Fin (F_rest.length + 1)), v)) ++
      (perKFChoice F_rest).map (fun p => (p.fst.succ, p.snd)) := by
  show (List.finRange (F_rest.length + 1)).flatMap
        (fun i : Fin (F_rest.length + 1) =>
          (vertices ((T :: F_rest)[i.val])).map (fun v => (i, v))) = _
  rw [List.finRange_succ, List.flatMap_cons]
  show ((vertices T).map (fun v => ((0 : Fin (F_rest.length + 1)), v))) ++
        ((List.finRange F_rest.length).map Fin.succ).flatMap
          (fun i : Fin (F_rest.length + 1) =>
            (vertices ((T :: F_rest)[i.val])).map (fun v => (i, v))) =
      (vertices T).map (fun v => ((0 : Fin (F_rest.length + 1)), v)) ++
      (perKFChoice F_rest).map (fun p => (p.fst.succ, p.snd))
  congr 1
  rw [List.flatMap_map]
  show (List.finRange F_rest.length).flatMap
        (fun j : Fin F_rest.length =>
          (vertices F_rest[j.val]).map (fun v => (Fin.succ j, v))) = _
  unfold perKFChoice
  rw [List.map_flatMap]
  refine List.flatMap_congr fun j _ => ?_
  rw [List.map_map]
  rfl

/-- Multiset-level decomposition of `listChoices (perKFChoice (T :: F_rest)) n`
    into a nested bind over (α : Bool^n, c_T : T-vertices^(α.count true), fdata :
    perKFChoice F_rest^(α.count false)) via `mergeData`.

    Proof by induction on `n`. Base case `n = 0`: both sides are `{[]}`. Step
    case: peel one element on both sides; on LHS use `perKFChoice_cons`, on RHS
    use `listChoices_succ` for the `[true, false]` bind; match per-bit using IH. -/
private theorem listChoices_perKFChoice_cons_decompose
    (T : Planar α) (F_rest : List (Planar α)) (n : Nat) :
    Multiset.ofList (listChoices (perKFChoice (T :: F_rest)) n) =
      (Multiset.ofList (listChoices [true, false] n)).bind fun α_assn =>
        (Multiset.ofList (listChoices (vertices T) (α_assn.count true))).bind fun c_T =>
          (Multiset.ofList
              (listChoices (perKFChoice F_rest) (α_assn.count false))).map fun fdata =>
            mergeData α_assn c_T fdata := by
  induction n with
  | zero =>
    -- LHS = ofList [[]]. RHS = singleton-bind chain reduces to {[]}.
    rw [listChoices_zero]
    show (Multiset.ofList ([[]] : List (List (Fin (F_rest.length + 1) × Path))) :
            Multiset _) = _
    rw [show (Multiset.ofList ([[]] :
            List (List (Fin (F_rest.length + 1) × Path))) : Multiset _) =
          (([] : List (Fin (F_rest.length + 1) × Path)) ::ₘ 0) from rfl]
    rw [show Multiset.ofList (listChoices [true, false] 0) =
          (([] : List Bool) ::ₘ 0) from by rw [listChoices_zero]; rfl]
    rw [Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [show ([] : List Bool).count true = 0 from rfl]
    rw [show Multiset.ofList (listChoices (vertices T) 0) =
          (([] : List Path) ::ₘ 0) from by rw [listChoices_zero]; rfl]
    rw [Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [show ([] : List Bool).count false = 0 from rfl]
    rw [show Multiset.ofList (listChoices (perKFChoice F_rest) 0) =
          (([] : List (Fin F_rest.length × Path)) ::ₘ 0) from by
          rw [listChoices_zero]; rfl]
    rw [Multiset.map_cons, Multiset.map_zero]
    rfl
  | succ k ih =>
    -- Convert LHS via listChoices_succ into bind, then apply IH inside.
    have lhs_rw :
        Multiset.ofList (listChoices (perKFChoice (T :: F_rest)) (k + 1)) =
          (Multiset.ofList (perKFChoice (T :: F_rest))).bind fun v =>
            (Multiset.ofList (listChoices (perKFChoice (T :: F_rest)) k)).map (v :: ·) := by
      rw [listChoices_succ, ← Multiset.coe_bind]
      rfl
    rw [lhs_rw]
    conv_lhs => rhs; ext v; rw [ih]
    rw [perKFChoice_cons T F_rest]
    rw [show (Multiset.ofList (((vertices T).map fun v => ((0 : Fin (F_rest.length + 1)), v)) ++
              (perKFChoice F_rest).map fun p => (p.fst.succ, p.snd)) : Multiset _) =
          (Multiset.ofList ((vertices T).map fun v => ((0 : Fin (F_rest.length + 1)), v))) +
          (Multiset.ofList ((perKFChoice F_rest).map fun p => (p.fst.succ, p.snd)))
        from by rw [← Multiset.coe_add]]
    rw [Multiset.add_bind]
    rw [show (Multiset.ofList ((vertices T).map fun v =>
              ((0 : Fin (F_rest.length + 1)), v)) : Multiset _) =
          (Multiset.ofList (vertices T)).map (fun v => ((0 : Fin (F_rest.length + 1)), v))
        from rfl]
    rw [show (Multiset.ofList ((perKFChoice F_rest).map fun p =>
              (p.fst.succ, p.snd)) : Multiset _) =
          (Multiset.ofList (perKFChoice F_rest)).map (fun p => (p.fst.succ, p.snd))
        from rfl]
    rw [Multiset.bind_map, Multiset.bind_map]
    -- LHS = bind v_T : vertices T: (RHS_for_k).map ((0, v_T) :: ·)
    --     + bind p : perKFChoice F_rest: (RHS_for_k).map ((p.fst.succ, p.snd) :: ·)
    -- Where RHS_for_k = bind α'' [t,f]^k: bind c_T (α''.count true): map fdata: mergeData α'' c_T fdata.
    -- Decompose RHS via listChoices_succ on [t,f]:
    have rhs_rw :
        (Multiset.ofList (listChoices [true, false] (k + 1))).bind (fun α_assn =>
          (Multiset.ofList (listChoices (vertices T) (α_assn.count true))).bind fun c_T =>
            (Multiset.ofList (listChoices (perKFChoice F_rest) (α_assn.count false))).map
              fun fdata => mergeData α_assn c_T fdata) =
          (Multiset.ofList (listChoices [true, false] k)).bind (fun α'' =>
            (Multiset.ofList (listChoices (vertices T) ((true :: α'').count true))).bind fun c_T =>
              (Multiset.ofList (listChoices (perKFChoice F_rest) ((true :: α'').count false))).map
                fun fdata => mergeData (true :: α'') c_T fdata) +
          (Multiset.ofList (listChoices [true, false] k)).bind (fun α'' =>
            (Multiset.ofList (listChoices (vertices T) ((false :: α'').count true))).bind fun c_T =>
              (Multiset.ofList (listChoices (perKFChoice F_rest) ((false :: α'').count false))).map
                fun fdata => mergeData (false :: α'') c_T fdata) := by
      rw [listChoices_succ]
      rw [show ([true, false].flatMap fun v => (listChoices [true, false] k).map (v :: ·)) =
            (listChoices [true, false] k).map (true :: ·) ++
            (listChoices [true, false] k).map (false :: ·)
          from by simp [List.flatMap_cons, List.flatMap_nil]]
      rw [show (Multiset.ofList ((listChoices [true, false] k).map (true :: ·) ++
                (listChoices [true, false] k).map (false :: ·)) : Multiset _) =
            Multiset.ofList ((listChoices [true, false] k).map (true :: ·)) +
            Multiset.ofList ((listChoices [true, false] k).map (false :: ·))
          from by rw [← Multiset.coe_add]]
      rw [Multiset.add_bind]
      rw [show (Multiset.ofList ((listChoices [true, false] k).map (true :: ·)) :
                Multiset (List Bool)) =
            (Multiset.ofList (listChoices [true, false] k)).map (true :: ·) from rfl]
      rw [show (Multiset.ofList ((listChoices [true, false] k).map (false :: ·)) :
                Multiset (List Bool)) =
            (Multiset.ofList (listChoices [true, false] k)).map (false :: ·) from rfl]
      rw [Multiset.bind_map, Multiset.bind_map]
    rw [rhs_rw]
    congr 1
    · -- True-bit piece: LHS_T = RHS_true.
      -- LHS_T: bind v_T : vertices T: (RHS_for_k).map ((0, v_T) :: ·)
      -- RHS_true: bind α'': bind c_T (α''.count true + 1): map fdata: mergeData (true :: α'') c_T fdata
      -- Strategy: rewrite RHS_true to match LHS_T using bind algebra.
      conv_rhs =>
        rhs; ext α''
        rw [show (true :: α'').count true = α''.count true + 1 from
              List.count_cons_self]
        rw [show (true :: α'').count false = α''.count false from by
              simp only [List.count_cons]; rfl]
        rw [show (Multiset.ofList (listChoices (vertices T) (α''.count true + 1)) :
              Multiset _) =
              (Multiset.ofList (vertices T)).bind fun v =>
                (Multiset.ofList (listChoices (vertices T) (α''.count true))).map (v :: ·)
            from by rw [listChoices_succ, ← Multiset.coe_bind]; rfl]
        rw [Multiset.bind_assoc]
        rhs; ext v_T
        rw [Multiset.bind_map]
        rhs; ext c_T'
        rw [show mergeData (true :: α'') (v_T :: c_T') = fun fdata =>
              ((0 : Fin (F_rest.length + 1)), v_T) :: mergeData α'' c_T' fdata
            from rfl]
        rw [show ((Multiset.ofList (listChoices (perKFChoice F_rest) (α''.count false))).map
              (fun fdata => ((0 : Fin (F_rest.length + 1)), v_T) :: mergeData α'' c_T' fdata)) =
              ((Multiset.ofList (listChoices (perKFChoice F_rest) (α''.count false))).map
                (mergeData α'' c_T')).map (((0 : Fin (F_rest.length + 1)), v_T) :: ·)
            from by rw [Multiset.map_map]; rfl]
      -- Goal RHS now: bind α'': bind v_T: bind c_T': ((map fdata: mergeData α'' c_T' fdata)).map ((0, v_T) :: ·)
      -- Swap α'' and v_T binds via Multiset.bind_bind.
      rw [Multiset.bind_bind]
      -- Now: bind v_T: bind α'': bind c_T': ((map ...).map ((0, v_T) :: ·))
      refine Multiset.bind_congr fun v_T _ => ?_
      -- Pull .map outside the bind α''/c_T' structure.
      rw [show ((Multiset.ofList (listChoices [true, false] k)).bind fun α'' =>
              (Multiset.ofList (listChoices (vertices T) (α''.count true))).bind fun c_T' =>
                ((Multiset.ofList (listChoices (perKFChoice F_rest) (α''.count false))).map
                  (mergeData α'' c_T')).map (((0 : Fin (F_rest.length + 1)), v_T) :: ·)) =
            ((Multiset.ofList (listChoices [true, false] k)).bind fun α'' =>
              (Multiset.ofList (listChoices (vertices T) (α''.count true))).bind fun c_T' =>
                (Multiset.ofList (listChoices (perKFChoice F_rest) (α''.count false))).map
                  (mergeData α'' c_T')).map (((0 : Fin (F_rest.length + 1)), v_T) :: ·)
          from by
            rw [Multiset.map_bind]
            refine Multiset.bind_congr fun α'' _ => ?_
            rw [Multiset.map_bind]]
      rfl
    · -- False-bit piece: LHS_F = RHS_false. Symmetric.
      conv_rhs =>
        rhs; ext α''
        rw [show (false :: α'').count true = α''.count true from by
              simp only [List.count_cons]; rfl]
        rw [show (false :: α'').count false = α''.count false + 1 from
              List.count_cons_self]
        rhs; ext c_T
        rw [show (Multiset.ofList (listChoices (perKFChoice F_rest) (α''.count false + 1)) :
              Multiset _) =
              (Multiset.ofList (perKFChoice F_rest)).bind fun p =>
                (Multiset.ofList (listChoices (perKFChoice F_rest) (α''.count false))).map
                  (p :: ·)
            from by rw [listChoices_succ, ← Multiset.coe_bind]; rfl]
        -- Now: Multiset.map (mergeData (false :: α'') c_T) ((perKFChoice F_rest).bind ...)
        -- Push the outer Multiset.map inside via Multiset.map_bind:
        rw [Multiset.map_bind]
        rhs; ext p
        rw [Multiset.map_map]
        rw [show ((fun fdata => mergeData (false :: α'') c_T fdata) ∘ fun x => p :: x) =
              fun fdata' => (p.fst.succ, p.snd) :: mergeData α'' c_T fdata'
            from rfl]
        rw [show ((Multiset.ofList (listChoices (perKFChoice F_rest) (α''.count false))).map
              (fun fdata' => (p.fst.succ, p.snd) :: mergeData α'' c_T fdata')) =
              ((Multiset.ofList (listChoices (perKFChoice F_rest) (α''.count false))).map
                (mergeData α'' c_T)).map ((p.fst.succ, p.snd) :: ·)
            from by rw [Multiset.map_map]; rfl]
      -- Goal RHS: bind α'': bind c_T: bind p: ((map fdata': mergeData α'' c_T fdata').map ((p.fst.succ, p.snd) :: ·))
      -- Pull p out: swap c_T and p (innermost), then swap α'' and p (outermost).
      conv_rhs =>
        rhs; ext α''
        rw [Multiset.bind_bind]
      rw [Multiset.bind_bind]
      refine Multiset.bind_congr fun p _ => ?_
      -- Inner: bind α'': bind c_T: ((map fdata': mergeData α'' c_T fdata').map ((p.fst.succ, p.snd) :: ·))
      -- = (bind α'': bind c_T: map fdata': mergeData α'' c_T fdata').map ((p.fst.succ, p.snd) :: ·)
      rw [show ((Multiset.ofList (listChoices [true, false] k)).bind fun α'' =>
              (Multiset.ofList (listChoices (vertices T) (α''.count true))).bind fun c_T =>
                ((Multiset.ofList (listChoices (perKFChoice F_rest) (α''.count false))).map
                  (mergeData α'' c_T)).map ((p.fst.succ, p.snd) :: ·)) =
            ((Multiset.ofList (listChoices [true, false] k)).bind fun α'' =>
              (Multiset.ofList (listChoices (vertices T) (α''.count true))).bind fun c_T =>
                (Multiset.ofList (listChoices (perKFChoice F_rest) (α''.count false))).map
                  (mergeData α'' c_T)).map ((p.fst.succ, p.snd) :: ·)
          from by
            rw [Multiset.map_bind]
            refine Multiset.bind_congr fun α'' _ => ?_
            rw [Multiset.map_bind]]
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
  induction F_A generalizing pre_FA_B with
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
    -- LHS: insertionForest (T :: F_rest) pre_FA_B
    -- Step A: unfold via insertionForest_cons_assignment.
    rw [insertionForest_cons_assignment T F_rest pre_FA_B]
    -- LHS = bind α : ofList (listChoices [t,f] |pre_FA_B|):
    --         bind T' : insertion T (filter_t pre_FA_B α):
    --           map F' : insertionForest F_rest (filter_f pre_FA_B α): T' :: F'
    -- Step B: apply insertion_def to inner insertion T (filter_t α).
    -- Step C: apply IH to inner insertionForest F_rest (filter_f α).
    -- Step D: simplify each leaf via buildFIns_cons_decompose.
    -- Step E: bridge via listChoices_perKFChoice_cons_decompose to RHS form.
    -- RHS: (enumFChoices (T :: F_rest) pre_FA_B).map (buildFIns (T :: F_rest) pre_FA_B)
    -- Unfold RHS:
    show ((Multiset.ofList (listChoices [true, false] pre_FA_B.length)).bind fun α =>
            (insertion T ((pre_FA_B.zip α).filterMap
              (fun p => if p.snd then some p.fst else none))).bind fun T' =>
              (insertionForest F_rest ((pre_FA_B.zip α).filterMap
                (fun p => if p.snd then none else some p.fst))).map fun F' => T' :: F') =
        (enumFChoices (T :: F_rest) pre_FA_B).map (buildFIns (T :: F_rest) pre_FA_B)
    -- Apply IH to inner insertionForest F_rest, insertion_def to inner insertion T.
    conv_lhs =>
      rhs; ext α
      rw [insertion_def T]
      rhs; ext T'
      rw [ih]
    -- LHS now: bind α: bind T' : ofList ((listChoices (vertices T) ...).map ...):
    --           map F' : (enumFChoices F_rest (filter_f α)).map (buildFIns F_rest (filter_f α)): T' :: F'
    -- Push the .map outside the ofList wrapper:
    conv_lhs =>
      rhs; ext α
      rw [show (Multiset.ofList ((listChoices (vertices T)
              (((pre_FA_B.zip α).filterMap (fun p => if p.snd then some p.fst else none)).length)).map
              fun choice => multiGraft T (choice.zip
                ((pre_FA_B.zip α).filterMap (fun p => if p.snd then some p.fst else none)))) :
              Multiset _) =
            (Multiset.ofList (listChoices (vertices T)
              (((pre_FA_B.zip α).filterMap (fun p => if p.snd then some p.fst else none)).length))).map
              fun choice => multiGraft T (choice.zip
                ((pre_FA_B.zip α).filterMap (fun p => if p.snd then some p.fst else none)))
          from rfl]
      rw [Multiset.bind_map]
      -- Now: bind c_T : ofList (listChoices (vertices T) ...): map F' : (enumFChoices F_rest (filter_f α)).map ...: ...
      rhs; ext c_T
      rw [Multiset.map_map]
      -- Goal: ofList (enumFChoices F_rest (filter_f α)).map (buildFIns F_rest (filter_f α) ∘ ((multiGraft T (c_T.zip (filter_t α))) :: ·))
    -- LHS now: bind α: bind c_T : ofList (listChoices (vertices T) (filter_t α).length):
    --           (enumFChoices F_rest (filter_f α)).map ((·) ∘ ...) where (·) builds the cons.
    -- Need to align α-driven choices with RHS's enumFChoices (T :: F_rest).
    -- Use buildFIns_cons_decompose: each leaf builds the cons form.
    -- Then use listChoices_perKFChoice_cons_decompose.
    --
    -- RHS unfolding: (enumFChoices (T :: F_rest) pre_FA_B).map (buildFIns (T :: F_rest) pre_FA_B)
    -- = (ofList (listChoices (perKFChoice (T :: F_rest)) pre_FA_B.length)).map (buildFIns (T :: F_rest) pre_FA_B)
    -- By listChoices_perKFChoice_cons_decompose:
    -- = (bind α: bind c_T (α.count true): map fdata (α.count false): mergeData α c_T fdata).map (buildFIns ...)
    -- = bind α: bind c_T: map fdata: buildFIns (T :: F_rest) pre_FA_B (mergeData α c_T fdata)
    -- By buildFIns_cons_decompose: each leaf = multiGraft T (c_T.zip (filter_t α)) :: buildFIns F_rest (filter_f α) fdata
    rw [show (enumFChoices (T :: F_rest) pre_FA_B) =
          Multiset.ofList (listChoices (perKFChoice (T :: F_rest)) pre_FA_B.length)
        from rfl]
    rw [listChoices_perKFChoice_cons_decompose T F_rest pre_FA_B.length]
    rw [Multiset.map_bind]
    -- RHS = bind α : ofList (listChoices [t,f] pre_FA_B.length):
    --         (bind c_T (α.count true): map fdata (α.count false): mergeData α c_T fdata).map (buildFIns (T :: F_rest) pre_FA_B)
    refine Multiset.bind_congr fun α hα => ?_
    -- Get lengths.
    have hα_len : α.length = pre_FA_B.length :=
      (mem_listChoices_length [true, false] _ _ (Multiset.mem_coe.mp hα))
    have hpf : pre_FA_B.length = α.length := hα_len.symm
    have hft : ((pre_FA_B.zip α).filterMap (fun p => if p.snd then some p.fst else none)).length =
        α.count true := filter_t_length pre_FA_B α hpf
    have hff : ((pre_FA_B.zip α).filterMap (fun p => if p.snd then none else some p.fst)).length =
        α.count false := filter_f_length pre_FA_B α hpf
    -- Rewrite both sides' inner length-conditions to use α.count true/false.
    rw [hft]
    rw [Multiset.map_bind]
    refine Multiset.bind_congr fun c_T hc_T => ?_
    have hc_len : c_T.length = α.count true := by
      have := mem_listChoices_length (vertices T) (α.count true) c_T
        (Multiset.mem_coe.mp hc_T)
      exact this
    -- Now goal: (enumFChoices F_rest (filter_f α)).map ((multiGraft T (c_T.zip (filter_t α)) :: ·) ∘ buildFIns F_rest (filter_f α))
    --        = (ofList (listChoices (perKFChoice F_rest) (α.count false))).map
    --            ((buildFIns (T :: F_rest) pre_FA_B) ∘ mergeData α c_T)
    -- Rewrite enumFChoices and buildFIns_cons_decompose application.
    rw [show enumFChoices F_rest ((pre_FA_B.zip α).filterMap
            (fun p => if p.snd then none else some p.fst)) =
          Multiset.ofList (listChoices (perKFChoice F_rest)
            (((pre_FA_B.zip α).filterMap (fun p => if p.snd then none else some p.fst)).length))
        from rfl]
    rw [hff]
    -- LHS is map over (ofList (listChoices ... (α.count false))).
    -- RHS has nested map: map (buildFIns ...) (map (mergeData ...) (ofList ...)). Merge via map_map.
    rw [Multiset.map_map]
    -- Both sides are .map over Multiset.ofList (listChoices (perKFChoice F_rest) (α.count false)).
    refine Multiset.map_congr rfl fun fdata hfdata => ?_
    have hf_len : fdata.length = α.count false := by
      have := mem_listChoices_length (perKFChoice F_rest) (α.count false) fdata
        (Multiset.mem_coe.mp hfdata)
      exact this
    -- Goal: ((multiGraft T (c_T.zip (filter_t α)) :: ·) ∘ buildFIns F_rest (filter_f α)) fdata
    --     = ((buildFIns (T :: F_rest) pre_FA_B) ∘ mergeData α c_T) fdata
    -- After unfolding the composition:
    -- LHS: multiGraft T (c_T.zip (filter_t α)) :: buildFIns F_rest (filter_f α) fdata
    -- RHS: buildFIns (T :: F_rest) pre_FA_B (mergeData α c_T fdata)
    -- This is exactly buildFIns_cons_decompose, used in reverse.
    show multiGraft T (c_T.zip ((pre_FA_B.zip α).filterMap
            (fun p => if p.snd then some p.fst else none))) ::
        buildFIns F_rest ((pre_FA_B.zip α).filterMap
            (fun p => if p.snd then none else some p.fst)) fdata =
        buildFIns (T :: F_rest) pre_FA_B (mergeData α c_T fdata)
    exact (buildFIns_cons_decompose T F_rest pre_FA_B α c_T fdata hpf hc_len hf_len).symm

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

/-! ## §1.9: Canonical labeled grafting form (mathlib-style architecture)

The architectural pivot for closing `LHS_eq_iteratedQuadSum_msform_cons_alphaBind`.
Both sides of the bijection enumerate the same `GraftingData` objects with
different organizations; each bridging proof becomes a *structural unfolding*
rather than an *iterated bijection*.

### Why this organization

The original Piece 3/4 plan (`scratch/a33_phase4_2_plan.md`) defines a partial
LHS-side form (`LHS_per_alpha_raw α`) and bridges it to both sides. The bridge
to RHS (Piece 4) hits a **path-shift compositional issue**: iterating
`multiGraft_split_lifted_aux` for multiple T_graft-bucket c's targeting the same
`pre_T_B[k]` requires path-arithmetic across modified subtrees.

The mathlib idiom: define a *canonical form* (`GraftingData`) that records
EVERYTHING in terms of the ORIGINAL trees (T, pre_T_B, F_A, pre_FA_B), and a
*single-pass* `interpret` function that does all grafting in closed form. The
path-arithmetic is then localized in `interpret` (computed once per
`GraftingData`), not iterated across bridge proofs.

### Architecture

* **`GraftingData F_A pre_T_B pre_FA_B`** — one canonical labeled grafting:
  - `pre_T_B_choice : List Path` (per-pre_T_B[k] graft position in V(T))
  - `pre_FA_B_choice : List (Fin F_A.length × Path)` (per-pre_FA_B[k]: which
    F_A tree, vertex within)
  - `C_targets : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)`
    (per-c bucket-classified target — reuses the §1.7 inductive)

* **`interpret T gd C : List (Planar α)`** — produces the resulting forest by
  combining all grafts in a single pass:
  - Builds `pre_T_B'` = pre_T_B with T_graft-bucket c's inserted per-tree.
  - Builds `T'` = `multiGraft T (choice_T.zip pre_T_B' ++ T_orig_pairs)`.
  - Symmetrically for F-side.

* **`enumGraftingData T F_A pre_T_B pre_FA_B C_length`** — enumerates all
  valid `GraftingData` with appropriate lengths.

### The two bridge proofs (future sessions)

After this skeleton lands:

1. **`LHS_eq_canonical`** (Piece 3 analog, ~150-200 LOC):
   ```
   LHS = (enumGraftingData T F_A pre_T_B pre_FA_B C.length).map (interpret T · C)
   ```
   Proof: unfold LHS via `insertion_def`, `insertionForest_eq_explicit`,
   `insertionForest_cons_assignment`; use `vertices_forest_eq_partition` to
   decompose γ into bucket-classified targets.

2. **`RHS_eq_canonical_msform`** (Piece 4 analog, ~100-150 LOC):
   ```
   bind α : iteratedQuadSum-leaf α-pres
     = (enumGraftingData T F_A pre_T_B pre_FA_B C.length).map (interpret T · C) (modulo msform)
   ```
   Proof: unfold `iteratedQuadSum-leaf`; absorb per-bucket grafts into the
   canonical form via `multiGraft_perm_pair` (msform absorbs planar order
   differences across bucket layouts).

### Substrate placement

This entire section is `private` and scoped to the A3.3 cons-case proof. If
future work needs the canonical form for related theorems (Δ^c coassoc, GL
mul_assoc), promote to a top-level `[UPSTREAM]` substrate. -/

/-- Per-bucket vertex source list (one entry per (bucket, valid vertex)).
    Concrete enumeration of `AlphaConstrainedChoice` values: V(T) for T_orig,
    `Σ k, V(pre_T_B[k])` for T_graft, etc. Used as the source alphabet for
    `C_targets` enumeration via `listChoices`. -/
private def allAlphaConstrainedChoiceList
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B) :=
  ((vertices T).map AlphaConstrainedChoice.t_orig) ++
  ((List.finRange pre_T_B.length).flatMap fun k =>
    (vertices pre_T_B[k.val]).map (AlphaConstrainedChoice.t_graft k)) ++
  ((List.finRange F_A.length).flatMap fun i =>
    (vertices F_A[i.val]).map (AlphaConstrainedChoice.fa_orig i)) ++
  ((List.finRange pre_FA_B.length).flatMap fun k =>
    (vertices pre_FA_B[k.val]).map (AlphaConstrainedChoice.fa_graft k))

/-- Canonical labeled grafting data. One `GraftingData` corresponds to a
    completely-determined choice of:

    - per-pre_T_B[k] graft position in `V(T)` (`pre_T_B_choice`),
    - per-pre_FA_B[k] graft position (which F_A tree + vertex within)
      (`pre_FA_B_choice`),
    - per-c target classified by `QuadIdx` bucket (`C_targets`).

    Length validity is enforced by the enumerator (`enumGraftingData`) rather
    than the structure itself, keeping the type definition simple. -/
private structure GraftingData (F_A pre_T_B pre_FA_B : List (Planar α)) where
  /-- Per-pre_T_B[k] graft position in V(T). Expected length `pre_T_B.length`. -/
  pre_T_B_choice  : List Path
  /-- Per-pre_FA_B[k] graft position: which F_A tree + vertex within.
      Expected length `pre_FA_B.length`. -/
  pre_FA_B_choice : List (Fin F_A.length × Path)
  /-- Per-c bucket-classified target. Expected length matches consumer's `C.length`. -/
  C_targets       : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)

/-! ### §1.9.1: Per-bucket extractor helpers

These helpers extract per-bucket `(Path, Planar α)` pairs from a list of
`(AlphaConstrainedChoice, Planar α)` pairs. Used by `interpret` to compute the
grafting pairs per bucket. Sorry-free by structure. -/

/-- Extract `(vertex, c)` pairs from C_paired where the choice is `t_orig`. -/
private def extractTOrigPairs
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (C_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α)) :
    List (Path × Planar α) :=
  C_paired.filterMap fun p =>
    match p.fst with
    | .t_orig v => some (v, p.snd)
    | _ => none

/-- Extract `(vertex, c)` pairs from C_paired where the choice is `t_graft k _`
    for the given `k`. -/
private def extractTGraftPairsAt
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (C_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (k : Fin pre_T_B.length) : List (Path × Planar α) :=
  C_paired.filterMap fun p =>
    match p.fst with
    | .t_graft k' q => if k' = k then some (q, p.snd) else none
    | _ => none

/-- Extract `(vertex, c)` pairs from C_paired where the choice is `fa_orig i _`
    for the given `i`. -/
private def extractFAOrigPairsAt
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (C_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (i : Fin F_A.length) : List (Path × Planar α) :=
  C_paired.filterMap fun p =>
    match p.fst with
    | .fa_orig i' v => if i' = i then some (v, p.snd) else none
    | _ => none

/-- Extract `(vertex, c)` pairs from C_paired where the choice is `fa_graft k _`
    for the given `k`. -/
private def extractFAGraftPairsAt
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (C_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (k : Fin pre_FA_B.length) : List (Path × Planar α) :=
  C_paired.filterMap fun p =>
    match p.fst with
    | .fa_graft k' q => if k' = k then some (q, p.snd) else none
    | _ => none

/-! ### §1.9.2: `interpret` — single-pass grafting from `GraftingData`

The path-arithmetic-heavy function. Combines all per-bucket grafts in one pass:

1. T-side: build `pre_T_B'[k] = multiGraft pre_T_B[k] (T_graft pairs at k)`.
2. T-side: combine `T_orig` pairs and `pre_T_B'` grafts into `T_pairs`, compute
   `T' = multiGraft T T_pairs`.
3. F-side: build `pre_FA_B'[k] = multiGraft pre_FA_B[k] (FA_graft pairs at k)`.
4. F-side: per F_A[i], combine `pre_FA_B'` grafts targeting i with `FA_orig`
   pairs at i, compute `F'[i] = multiGraft F_A[i] (combined pairs)`.
5. Result: `T' :: F'`.

No iteration of `multiGraft_split_lifted_aux`. All grafts done relative to
ORIGINAL trees with closed-form pair lists. -/

/-- Single-pass interpretation of a `GraftingData` into the resulting forest.

    Semantically: `interpret T gd C` is the planar-list result obtained by
    grafting `pre_T_B`, `pre_FA_B`, and `C` (per `gd`'s choices) into
    `T :: F_A` in a SINGLE multi-graft per host tree.

    Path-arithmetic localized here. Bridge proofs (LHS_eq_canonical,
    RHS_eq_canonical_msform) consume this without inducting on `gd`'s C_targets. -/
private def interpret
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (gd : GraftingData F_A pre_T_B pre_FA_B)
    (C : List (Planar α)) : List (Planar α) :=
  let C_paired := gd.C_targets.zip C
  let T_orig_pairs := extractTOrigPairs C_paired
  let pre_T_B' : List (Planar α) :=
    (List.finRange pre_T_B.length).map fun k =>
      multiGraft pre_T_B[k.val] (extractTGraftPairsAt C_paired k)
  let T' : Planar α :=
    multiGraft T (gd.pre_T_B_choice.zip pre_T_B' ++ T_orig_pairs)
  let pre_FA_B' : List (Planar α) :=
    (List.finRange pre_FA_B.length).map fun k =>
      multiGraft pre_FA_B[k.val] (extractFAGraftPairsAt C_paired k)
  let F' : List (Planar α) :=
    (List.finRange F_A.length).map fun i =>
      let pre_FA_B'_for_i : List (Path × Planar α) :=
        (gd.pre_FA_B_choice.zip pre_FA_B').filterMap fun p =>
          if p.fst.fst = i then some (p.fst.snd, p.snd) else none
      multiGraft F_A[i.val] (pre_FA_B'_for_i ++ extractFAOrigPairsAt C_paired i)
  T' :: F'

/-! ### §1.9.3: `enumGraftingData` — canonical enumeration

Enumerates all `GraftingData` with appropriate lengths matching `pre_T_B`,
`pre_FA_B`, and the consumer-supplied `C_length`. Uses `listChoices` for the
three nested enumerations. -/

/-- Multiset of all valid `GraftingData` for given `T`, `F_A`, `pre_T_B`,
    `pre_FA_B`, and target `C_length`.

    Each entry has:
    - `pre_T_B_choice.length = pre_T_B.length`
    - `pre_FA_B_choice.length = pre_FA_B.length`
    - `C_targets.length = C_length`

    These length invariants follow from `listChoices`'s length lemma at
    consumption sites. -/
private def enumGraftingData
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (C_length : Nat) : Multiset (GraftingData F_A pre_T_B pre_FA_B) :=
  Multiset.ofList <|
    (listChoices (vertices T) pre_T_B.length).flatMap fun choice_T =>
      (listChoices (perKFChoice F_A) pre_FA_B.length).flatMap fun fdata =>
        (listChoices (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B) C_length).map
          fun targets =>
            { pre_T_B_choice := choice_T
              pre_FA_B_choice := fdata
              C_targets := targets }

/-! ### §1.9.4: Base-case lemmas (C = [])

Sorry-free reductions for the C = [] subcase of the bridge theorems. These
serve two purposes:

1. **Sanity check** for the canonical-form approach: confirm that `interpret`
   and `enumGraftingData` reduce correctly when `C = []`, before tackling the
   recursive cons case.
2. **Substrate** for the eventual full bridge proofs (§1.9.5 future work):
   the base case can be cited via `interpret_C_nil` + `enumGraftingData_zero`
   + `LHS_eq_canonical_C_nil` instead of re-derived inline.

These do NOT close `LHS_eq_iteratedQuadSum_msform_cons_alphaBind` (which is a
cons-case theorem, never invoked at C = []). They just verify that §1.9.1-3
substrate is well-founded. -/

/-- Reducing `interpret T gd []` (the C = [] case) to a closed form: the T-side
    becomes `multiGraft T (gd.pre_T_B_choice.zip pre_T_B)` (no T_orig grafts,
    pre_T_B' = pre_T_B), and the F-side becomes `buildFIns F_A pre_FA_B
    gd.pre_FA_B_choice` (no FA_graft pairs reduce pre_FA_B' to pre_FA_B; no
    FA_orig grafts; per-tree pairs match `perTreePairsFromFChoice`).

    Sanity check for `LHS_eq_canonical_C_nil` and the eventual full bridge. -/
private theorem interpret_C_nil
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (gd : GraftingData F_A pre_T_B pre_FA_B) :
    interpret T gd ([] : List (Planar α)) =
      multiGraft T (gd.pre_T_B_choice.zip pre_T_B) ::
        buildFIns F_A pre_FA_B gd.pre_FA_B_choice := by
  -- Reduce `interpret` and `buildFIns` while inlining the let-bindings via
  -- `simp only`. The extractors on `[]` are `rfl`-equal to `[]`; multiGraft on
  -- `[]` is identity; the `(finRange l.length).map (l[·.val])` reduces to `l`.
  simp only [interpret, buildFIns,
             show gd.C_targets.zip ([] : List (Planar α)) = [] from
               List.zip_nil_right (l := gd.C_targets),
             extractTOrigPairs, extractTGraftPairsAt,
             extractFAOrigPairsAt, extractFAGraftPairsAt,
             List.filterMap_nil, multiGraft_nil, List.append_nil,
             perTreePairsFromFChoice]
  -- After simp: both sides differ only in the inner `(finRange _).map _`
  -- needing `List.map_getElem_finRange` to collapse to the original list.
  congr 1
  · -- T-side: gd.pre_T_B_choice.zip ((finRange _).map (pre_T_B[·.val])) = gd.pre_T_B_choice.zip pre_T_B
    rw [List.map_getElem_finRange]
  · -- F-side: per-i, the (gd.pre_FA_B_choice.zip ((finRange _).map (pre_FA_B[·.val])))
    --   reduces to (gd.pre_FA_B_choice.zip pre_FA_B).
    apply List.map_congr_left
    intro i _
    congr 1
    rw [List.map_getElem_finRange]

/-- The C_length = 0 specialization of `enumGraftingData`: the per-c targets
    enumeration `listChoices _ 0 = [[]]` collapses, leaving a flat enumeration
    over `(choice_T, fdata)` with `C_targets = []`. -/
private theorem enumGraftingData_zero
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    enumGraftingData T F_A pre_T_B pre_FA_B 0 =
      (Multiset.ofList
        ((listChoices (vertices T) pre_T_B.length).flatMap fun choice_T =>
          (listChoices (perKFChoice F_A) pre_FA_B.length).map fun fdata =>
            ({ pre_T_B_choice := choice_T
               pre_FA_B_choice := fdata
               C_targets := ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
             } : GraftingData F_A pre_T_B pre_FA_B))) := by
  unfold enumGraftingData
  congr 1
  apply List.flatMap_congr
  intro choice_T _
  -- Inner per-fdata: (listChoices ... 0).map (fun targets => ⟨..., targets⟩)
  -- = [[]].map ... = [⟨..., []⟩] (singleton list).
  -- Then outer flatMap over fdata of this singleton matches `← map_eq_flatMap`.
  rw [show listChoices (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B) 0 =
            ([[]] : List (List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))) from
        listChoices_zero _]
  simp only [List.map_singleton, ← List.map_eq_flatMap]

/-- LHS-side base case: when `C = []`, the iterated grafting LHS form equals
    the canonical-form RHS. The bind chain
    `(insertion T pre_T_B).bind T_ins => (insertionForest F_A pre_FA_B).bind F_ins =>
       insertionForest (T_ins :: F_ins) []`
    collapses to `(insertion T pre_T_B).bind T_ins => (insertionForest F_A pre_FA_B).map (T_ins :: ·)`,
    which after unfolding via `insertion_def` and `insertionForest_eq_explicit` matches
    the canonical-form `(enumGraftingData T F_A pre_T_B pre_FA_B 0).map (interpret T · [])`. -/
private theorem LHS_eq_canonical_C_nil
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    ((insertion T pre_T_B).bind fun T_ins =>
        (insertionForest F_A pre_FA_B).bind fun F_ins =>
          insertionForest (T_ins :: F_ins) ([] : List (Planar α))) =
      (enumGraftingData T F_A pre_T_B pre_FA_B 0).map
        (fun gd => interpret T gd ([] : List (Planar α))) := by
  -- Step 0: rewrite RHS interpret to its explicit C-nil form via interpret_C_nil.
  rw [show (fun gd : GraftingData F_A pre_T_B pre_FA_B =>
            interpret T gd ([] : List (Planar α))) =
          (fun gd : GraftingData F_A pre_T_B pre_FA_B =>
            multiGraft T (gd.pre_T_B_choice.zip pre_T_B) ::
              buildFIns F_A pre_FA_B gd.pre_FA_B_choice) from by
        funext gd; exact interpret_C_nil T gd]
  -- Step 1: rewrite enumGraftingData_zero to expose flatMap structure.
  rw [enumGraftingData_zero]
  -- Step 2: collapse insertionForest (T_ins :: F_ins) [] = {T_ins :: F_ins}.
  conv_lhs =>
    rhs; ext T_ins
    rhs; ext F_ins
    rw [insertionForest_cons_host_nil_guests]
  -- Step 3: pull singleton bind through to map via Multiset.bind_singleton.
  simp only [Multiset.bind_singleton]
  -- Step 4: Unfold insertion T pre_T_B and insertionForest F_A pre_FA_B explicitly.
  rw [insertion_def T]
  rw [show (insertionForest F_A pre_FA_B) =
          (enumFChoices F_A pre_FA_B).map (buildFIns F_A pre_FA_B) from
        insertionForest_eq_explicit F_A pre_FA_B]
  -- Step 5: push the List.map → Multiset.ofList through bind/map structure.
  -- LHS: (↑(listChoices vT pre_T_B.length).map (multiGraft T · pre_T_B)).bind
  --        fun T_ins => ↑((enumFChoices F_A pre_FA_B).map (buildFIns ...)).map (T_ins :: ·)
  -- RHS: ↑((listChoices vT pre_T_B.length).flatMap fun choice_T =>
  --        (listChoices (perKFChoice F_A) pre_FA_B.length).map fun fdata =>
  --          ⟨choice_T, fdata, []⟩) .map (fun gd => multiGraft T (gd.1.zip pre_T_B) :: buildFIns _ _ gd.2)
  -- Convert both sides to the same flat coerced form.
  show ((Multiset.ofList
            ((listChoices (vertices T) pre_T_B.length).map
              fun choice => multiGraft T (choice.zip pre_T_B))).bind
          fun T_ins =>
            ((Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).map
              (buildFIns F_A pre_FA_B)).map (T_ins :: ·)) =
        (Multiset.ofList
          ((listChoices (vertices T) pre_T_B.length).flatMap fun choice_T =>
            (listChoices (perKFChoice F_A) pre_FA_B.length).map fun fdata =>
              ({ pre_T_B_choice := choice_T
                 pre_FA_B_choice := fdata
                 C_targets := ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
               } : GraftingData F_A pre_T_B pre_FA_B))).map
          fun gd => multiGraft T (gd.pre_T_B_choice.zip pre_T_B) ::
            buildFIns F_A pre_FA_B gd.pre_FA_B_choice
  -- Convert LHS: ↑listmap.bind → ↑list.bind (g ∘ multiGraft); ↑listmap → ↑(list.map g) → ...
  rw [show (Multiset.ofList
            ((listChoices (vertices T) pre_T_B.length).map
              fun choice => multiGraft T (choice.zip pre_T_B)) :
              Multiset (Planar α)) =
          (Multiset.ofList (listChoices (vertices T) pre_T_B.length)).map
            (fun choice => multiGraft T (choice.zip pre_T_B)) from rfl]
  rw [Multiset.bind_map]  -- ((m.map f).bind g) = m.bind (g ∘ f)
  -- LHS now: (↑listChoices vT _).bind fun choice_T =>
  --            ((↑listChoices (perKFChoice F_A) _).map (buildFIns _ _)).map (multiGraft T (choice_T.zip pre_T_B) :: ·)
  -- Push inner .map through .map (Multiset.map_map).
  conv_lhs =>
    rhs; ext choice_T
    rw [Multiset.map_map]
  -- Convert RHS: ↑(list.flatMap _).map _ → (↑list).bind (Multiset.ofList ∘ _)
  rw [show Multiset.ofList ((listChoices (vertices T) pre_T_B.length).flatMap fun choice_T =>
            (listChoices (perKFChoice F_A) pre_FA_B.length).map fun fdata =>
              ({ pre_T_B_choice := choice_T
                 pre_FA_B_choice := fdata
                 C_targets := ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
               } : GraftingData F_A pre_T_B pre_FA_B)) =
          (Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
            Multiset.ofList ((listChoices (perKFChoice F_A) pre_FA_B.length).map fun fdata =>
              ({ pre_T_B_choice := choice_T
                 pre_FA_B_choice := fdata
                 C_targets := ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
               } : GraftingData F_A pre_T_B pre_FA_B)) from by
        rw [← Multiset.coe_bind]]
  rw [Multiset.map_bind]
  -- Both sides now: (↑listChoices vT _).bind fun choice_T => ... .
  refine Multiset.bind_congr fun choice_T _ => ?_
  -- Per-choice_T: align the inner map.
  -- LHS inner: ((↑listChoices (perKFChoice _) _).map (buildFIns _ _)).map
  --              (fun fdata => multiGraft T (choice_T.zip pre_T_B) :: buildFIns _ _ fdata)
  --   wait, after Multiset.map_map: (↑listChoices ...).map ((multiGraft T (choice_T.zip pre_T_B) :: ·) ∘ buildFIns _ _)
  -- RHS inner: (↑((listChoices ...).map (fun fdata => ⟨choice_T, fdata, []⟩))).map
  --              (fun gd => multiGraft T (gd.1.zip pre_T_B) :: buildFIns _ _ gd.2)
  rw [show (Multiset.ofList ((listChoices (perKFChoice F_A) pre_FA_B.length).map
            fun fdata => ({ pre_T_B_choice := choice_T
                            pre_FA_B_choice := fdata
                            C_targets := ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
                          } : GraftingData F_A pre_T_B pre_FA_B)) :
            Multiset (GraftingData F_A pre_T_B pre_FA_B)) =
          (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).map
            fun fdata => ({ pre_T_B_choice := choice_T
                            pre_FA_B_choice := fdata
                            C_targets := ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
                          } : GraftingData F_A pre_T_B pre_FA_B) from rfl]
  rw [Multiset.map_map]
  -- Now both sides are .map over the same multiset; close via map_congr + rfl.
  refine Multiset.map_congr rfl fun fdata _ => ?_
  rfl

/-! ### §1.9.4.1: msform-wrapped C-nil base case

Trivial corollary of `LHS_eq_canonical_C_nil` (planar-level): wrapping both
sides in `(·).map (fun L => Multiset.ofList (L.map Nonplanar.mk))` preserves
the equality. This is the genuine base case for the `LHS_eq_canonical_msform`
induction (the planar-level base case `LHS_eq_canonical_C_nil` does not
directly suffice because the cons-case bridge requires msform absorption). -/

/-- The msform-wrapped form of `LHS_eq_canonical_C_nil`. Direct corollary via
    `congrArg (·.map _)`; the C = [] case has no T_orig-c's competing with
    pre_T_B grafts, so msform is not strictly needed but is included for
    uniformity with the cons-case statement. -/
private theorem LHS_eq_canonical_msform_C_nil
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    ((insertion T pre_T_B).bind fun T_ins =>
        (insertionForest F_A pre_FA_B).bind fun F_ins =>
          insertionForest (T_ins :: F_ins) ([] : List (Planar α))).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((enumGraftingData T F_A pre_T_B pre_FA_B 0).map
        (fun gd => interpret T gd ([] : List (Planar α)))).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) :=
  congrArg (Multiset.map _) (LHS_eq_canonical_C_nil T F_A pre_T_B pre_FA_B)

/-! ### §1.9.6: Cons-case structural decomposition of `enumGraftingData`

Structural lemma exposing the cons-of-C_targets pattern in `enumGraftingData`.
Peels one element off the front of the C_targets enumeration, leaving the
`(choice_T, fdata)` outer enumeration intact.

This is a building block for any future cons-case proof of
`LHS_eq_canonical_msform` or `RHS_eq_canonical_msform`: it converts an
induction on C-length into an induction with a clean `bind first :
allAlphaChoiceList: ...` outer pattern. The inner enumeration is `enumGraftingData
T F_A pre_T_B pre_FA_B n` (one length less), with the resulting C_targets
prepended by `first`.

Proof: unfolds both sides to a list-flatMap form, applies `listChoices_succ`
on the inner C_targets enumeration, and aligns via `List.map_flatMap` /
`List.map_map`. Sorry-free, ~30 LOC. -/

/-- Cons-case decomposition of `enumGraftingData` (peels one C_target off the
    front). The outer `(choice_T, fdata)` enumeration is preserved; the inner
    C_targets enumeration `(listChoices ... (n+1))` is decomposed via
    `listChoices_succ` into `flatMap first => map (first :: ·)`. -/
private theorem enumGraftingData_succ
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (n : Nat) :
    enumGraftingData T F_A pre_T_B pre_FA_B (n + 1) =
      (Multiset.ofList
        ((listChoices (vertices T) pre_T_B.length).flatMap fun choice_T =>
          (listChoices (perKFChoice F_A) pre_FA_B.length).flatMap fun fdata =>
            (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B).flatMap fun first =>
              (listChoices (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B) n).map
                fun rest_targets =>
                  ({ pre_T_B_choice := choice_T
                     pre_FA_B_choice := fdata
                     C_targets := first :: rest_targets }
                   : GraftingData F_A pre_T_B pre_FA_B)) :
        Multiset (GraftingData F_A pre_T_B pre_FA_B)) := by
  unfold enumGraftingData
  congr 1
  apply List.flatMap_congr
  intro choice_T _
  apply List.flatMap_congr
  intro fdata _
  -- Inner: (listChoices allAlpha (n + 1)).map (fun t => ⟨choice_T, fdata, t⟩)
  --        = allAlpha.flatMap fun first => (listChoices allAlpha n).map fun r => ⟨choice_T, fdata, first :: r⟩
  rw [listChoices_succ, List.map_flatMap]
  apply List.flatMap_congr
  intro first _
  rw [List.map_map]
  rfl

/-! ### §1.9.7: Per-bucket extractor cons-decomposition

The four `extract{Bucket}Pairs{At?}` extractors all have a common structural
pattern: each is a `List.filterMap` selecting pairs whose `fst` matches the
target bucket constructor (with index in the indexed cases). Their cons
behavior on `(first, c) :: rest_paired` reduces to:

- **Head matches**: prepend `(path, c)` and recurse.
- **Head does not match**: drop and recurse.

These 8 lemmas (4 buckets × 2 outcomes) are direct `rfl` reductions, useful
for any cons-case bridge proof. -/

@[simp] private theorem extractTOrigPairs_cons_t_orig
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (v : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α)) :
    extractTOrigPairs
        (((AlphaConstrainedChoice.t_orig v
            (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B)), c)
          :: rest_paired) =
      (v, c) :: extractTOrigPairs rest_paired := rfl

@[simp] private theorem extractTOrigPairs_cons_t_graft
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (k : Fin pre_T_B.length) (q : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α)) :
    extractTOrigPairs
        (((AlphaConstrainedChoice.t_graft (F_A := F_A) (pre_FA_B := pre_FA_B) k q), c)
          :: rest_paired) =
      extractTOrigPairs rest_paired := rfl

@[simp] private theorem extractTOrigPairs_cons_fa_orig
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (i : Fin F_A.length) (v : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α)) :
    extractTOrigPairs
        (((AlphaConstrainedChoice.fa_orig (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i v), c)
          :: rest_paired) =
      extractTOrigPairs rest_paired := rfl

@[simp] private theorem extractTOrigPairs_cons_fa_graft
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (k : Fin pre_FA_B.length) (q : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α)) :
    extractTOrigPairs
        (((AlphaConstrainedChoice.fa_graft (F_A := F_A) (pre_T_B := pre_T_B) k q), c)
          :: rest_paired) =
      extractTOrigPairs rest_paired := rfl

@[simp] private theorem extractTGraftPairsAt_cons_t_orig
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (v : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (k : Fin pre_T_B.length) :
    extractTGraftPairsAt
        (((AlphaConstrainedChoice.t_orig v
            (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B)), c)
          :: rest_paired) k =
      extractTGraftPairsAt rest_paired k := rfl

private theorem extractTGraftPairsAt_cons_t_graft_eq
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (k k' : Fin pre_T_B.length) (q : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (h : k' = k) :
    extractTGraftPairsAt
        (((AlphaConstrainedChoice.t_graft (F_A := F_A) (pre_FA_B := pre_FA_B) k' q), c)
          :: rest_paired) k =
      (q, c) :: extractTGraftPairsAt rest_paired k := by
  unfold extractTGraftPairsAt
  rw [List.filterMap_cons]
  dsimp only
  rw [if_pos h]

private theorem extractTGraftPairsAt_cons_t_graft_neq
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (k k' : Fin pre_T_B.length) (q : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (h : k' ≠ k) :
    extractTGraftPairsAt
        (((AlphaConstrainedChoice.t_graft (F_A := F_A) (pre_FA_B := pre_FA_B) k' q), c)
          :: rest_paired) k =
      extractTGraftPairsAt rest_paired k := by
  unfold extractTGraftPairsAt
  rw [List.filterMap_cons]
  dsimp only
  rw [if_neg h]

@[simp] private theorem extractTGraftPairsAt_cons_fa_orig
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (i : Fin F_A.length) (v : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (k : Fin pre_T_B.length) :
    extractTGraftPairsAt
        (((AlphaConstrainedChoice.fa_orig (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i v), c)
          :: rest_paired) k =
      extractTGraftPairsAt rest_paired k := rfl

@[simp] private theorem extractTGraftPairsAt_cons_fa_graft
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (k' : Fin pre_FA_B.length) (q : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (k : Fin pre_T_B.length) :
    extractTGraftPairsAt
        (((AlphaConstrainedChoice.fa_graft (F_A := F_A) (pre_T_B := pre_T_B) k' q), c)
          :: rest_paired) k =
      extractTGraftPairsAt rest_paired k := rfl

@[simp] private theorem extractFAOrigPairsAt_cons_t_orig
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (v : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (i : Fin F_A.length) :
    extractFAOrigPairsAt
        (((AlphaConstrainedChoice.t_orig v
            (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B)), c)
          :: rest_paired) i =
      extractFAOrigPairsAt rest_paired i := rfl

@[simp] private theorem extractFAOrigPairsAt_cons_t_graft
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (k : Fin pre_T_B.length) (q : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (i : Fin F_A.length) :
    extractFAOrigPairsAt
        (((AlphaConstrainedChoice.t_graft (F_A := F_A) (pre_FA_B := pre_FA_B) k q), c)
          :: rest_paired) i =
      extractFAOrigPairsAt rest_paired i := rfl

private theorem extractFAOrigPairsAt_cons_fa_orig_eq
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (i i' : Fin F_A.length) (v : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (h : i' = i) :
    extractFAOrigPairsAt
        (((AlphaConstrainedChoice.fa_orig (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i' v), c)
          :: rest_paired) i =
      (v, c) :: extractFAOrigPairsAt rest_paired i := by
  unfold extractFAOrigPairsAt
  rw [List.filterMap_cons]
  dsimp only
  rw [if_pos h]

private theorem extractFAOrigPairsAt_cons_fa_orig_neq
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (i i' : Fin F_A.length) (v : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (h : i' ≠ i) :
    extractFAOrigPairsAt
        (((AlphaConstrainedChoice.fa_orig (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i' v), c)
          :: rest_paired) i =
      extractFAOrigPairsAt rest_paired i := by
  unfold extractFAOrigPairsAt
  rw [List.filterMap_cons]
  dsimp only
  rw [if_neg h]

@[simp] private theorem extractFAOrigPairsAt_cons_fa_graft
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (k : Fin pre_FA_B.length) (q : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (i : Fin F_A.length) :
    extractFAOrigPairsAt
        (((AlphaConstrainedChoice.fa_graft (F_A := F_A) (pre_T_B := pre_T_B) k q), c)
          :: rest_paired) i =
      extractFAOrigPairsAt rest_paired i := rfl

@[simp] private theorem extractFAGraftPairsAt_cons_t_orig
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (v : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (k : Fin pre_FA_B.length) :
    extractFAGraftPairsAt
        (((AlphaConstrainedChoice.t_orig v
            (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B)), c)
          :: rest_paired) k =
      extractFAGraftPairsAt rest_paired k := rfl

@[simp] private theorem extractFAGraftPairsAt_cons_t_graft
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (k' : Fin pre_T_B.length) (q : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (k : Fin pre_FA_B.length) :
    extractFAGraftPairsAt
        (((AlphaConstrainedChoice.t_graft (F_A := F_A) (pre_FA_B := pre_FA_B) k' q), c)
          :: rest_paired) k =
      extractFAGraftPairsAt rest_paired k := rfl

@[simp] private theorem extractFAGraftPairsAt_cons_fa_orig
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (i : Fin F_A.length) (v : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (k : Fin pre_FA_B.length) :
    extractFAGraftPairsAt
        (((AlphaConstrainedChoice.fa_orig (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i v), c)
          :: rest_paired) k =
      extractFAGraftPairsAt rest_paired k := rfl

private theorem extractFAGraftPairsAt_cons_fa_graft_eq
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (k k' : Fin pre_FA_B.length) (q : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (h : k' = k) :
    extractFAGraftPairsAt
        (((AlphaConstrainedChoice.fa_graft (F_A := F_A) (pre_T_B := pre_T_B) k' q), c)
          :: rest_paired) k =
      (q, c) :: extractFAGraftPairsAt rest_paired k := by
  unfold extractFAGraftPairsAt
  rw [List.filterMap_cons]
  dsimp only
  rw [if_pos h]

private theorem extractFAGraftPairsAt_cons_fa_graft_neq
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (k k' : Fin pre_FA_B.length) (q : Path) (c : Planar α)
    (rest_paired : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α))
    (h : k' ≠ k) :
    extractFAGraftPairsAt
        (((AlphaConstrainedChoice.fa_graft (F_A := F_A) (pre_T_B := pre_T_B) k' q), c)
          :: rest_paired) k =
      extractFAGraftPairsAt rest_paired k := by
  unfold extractFAGraftPairsAt
  rw [List.filterMap_cons]
  dsimp only
  rw [if_neg h]

/-! ### §1.10: msform-wrapped C-nil base case for the RHS bridge

The C = [] base case of `RHS_eq_canonical_msform`. With α = [] (the only
length-0 QuadIdx-list), the iteratedQuadSum-leaf collapses (all `bucketSlice [] []`
buckets are empty) to `(insertion T pre_T_B).bind T' => (insertionForest F_A pre_FA_B).map (T' :: ·)`.
This matches the LHS of `LHS_eq_canonical_msform_C_nil` after `bind`-ing back to
`insertionForest (T_ins :: F_ins) []`. -/

/-- **C-nil base case** for `RHS_eq_canonical_msform`. The α-bind on the LHS
    collapses to a singleton (only α = [] has length 0); the iteratedQuadSum-leaf
    with empty pres reduces via `singleton_bind`s to
    `(insertion T pre_T_B).bind T' => (insertionForest F_A pre_FA_B).map (T' :: ·)`.
    Bridged to the canonical-form RHS via `LHS_eq_canonical_msform_C_nil` after
    re-binding the inner `.map (T' :: ·)` to `.bind F_ins => insertionForest
    (T' :: F_ins) []`. -/
private theorem RHS_eq_canonical_msform_C_nil
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    ((Multiset.ofList (listChoices
        [QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft] 0)).bind
      fun a =>
        iteratedQuadSum T F_A pre_T_B pre_FA_B
          (fun t => bucketSlice ([] : List (Planar α)) a t) []).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((enumGraftingData T F_A pre_T_B pre_FA_B 0).map
        (fun gd => interpret T gd ([] : List (Planar α)))).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- Step 1: collapse listChoices [...] 0 to {[]} and singleton-bind to the leaf.
  rw [show listChoices [QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft] 0 =
          [[]] from rfl]
  rw [show (Multiset.ofList ([[]] : List (List QuadIdx)) : Multiset _) =
          ({([] : List QuadIdx)} : Multiset _) from rfl]
  rw [Multiset.singleton_bind]
  -- Step 2: reduce iteratedQuadSum-leaf with α = []. All bucketSlice [] [] _ = [].
  rw [iteratedQuadSum_nil_remaining]
  simp only [bucketSlice_nil_left, insertionForest_nil_guests, List.append_nil,
             Multiset.singleton_bind]
  -- LHS now: ((insertion T pre_T_B).bind T' => (insertionForest F_A pre_FA_B).map (T' :: ·)).map msform
  -- Step 3: convert inner .map (T' :: ·) to .bind F_ins => insertionForest (T' :: F_ins) [].
  rw [show ((insertion T pre_T_B).bind fun T' : Planar α =>
              (insertionForest F_A pre_FA_B).map (fun F' : List (Planar α) => T' :: F')) =
          ((insertion T pre_T_B).bind fun T_ins : Planar α =>
              (insertionForest F_A pre_FA_B).bind fun F_ins : List (Planar α) =>
                insertionForest (T_ins :: F_ins) ([] : List (Planar α))) from by
        refine Multiset.bind_congr fun T_ins _ => ?_
        rw [show (fun F_ins : List (Planar α) =>
                    insertionForest (T_ins :: F_ins) ([] : List (Planar α))) =
                (fun F_ins : List (Planar α) =>
                  ({T_ins :: F_ins} : Multiset (List (Planar α)))) from by
              funext F_ins
              exact insertionForest_cons_host_nil_guests T_ins F_ins]
        exact (Multiset.bind_singleton (insertionForest F_A pre_FA_B) (T_ins :: ·)).symm]
  -- Step 4: apply LHS_eq_canonical_msform_C_nil.
  exact LHS_eq_canonical_msform_C_nil T F_A pre_T_B pre_FA_B

/-! ### §1.10.1: Head decomposition substrate

Substrate for the cons-case bridge of `RHS_eq_canonical_msform`. The
`enumGraftingData_succ` (§1.9.6) exposes the per-target structure
`(allAlphaConstrainedChoiceList).bind first => ...`. To match the LHS's per-α
structure (where `α : List QuadIdx` selects a bucket per c), we need to factor
the `first` enumeration by bucket.

The head decomposition lemma `allAlphaConstrainedChoiceList_bind_decompose`
splits `(allAlphaConstrainedChoiceList).bind H` into a sum of 4 per-bucket
binds, each ranging over `enumAlphaConstrainedChoice b`. This is the key
substrate for the cons-case proof. -/

/-- Each bucket's source list (as a Multiset) equals the corresponding
    `enumAlphaConstrainedChoice` value. T_orig is `rfl`; the indexed buckets
    use `Multiset.coe_bind` to convert flatMap to bind. -/
private theorem ofList_T_orig_eq_enumAlpha
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    (Multiset.ofList ((vertices T).map AlphaConstrainedChoice.t_orig) :
      Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
    enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.T_orig := rfl

private theorem ofList_T_graft_eq_enumAlpha
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    (Multiset.ofList ((List.finRange pre_T_B.length).flatMap fun k =>
        (vertices pre_T_B[k.val]).map (AlphaConstrainedChoice.t_graft k)) :
      Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
    enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.T_graft := by
  unfold enumAlphaConstrainedChoice
  rw [← Multiset.coe_bind]

private theorem ofList_FA_orig_eq_enumAlpha
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    (Multiset.ofList ((List.finRange F_A.length).flatMap fun i =>
        (vertices F_A[i.val]).map (AlphaConstrainedChoice.fa_orig i)) :
      Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
    enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.FA_orig := by
  unfold enumAlphaConstrainedChoice
  rw [← Multiset.coe_bind]

private theorem ofList_FA_graft_eq_enumAlpha
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    (Multiset.ofList ((List.finRange pre_FA_B.length).flatMap fun k =>
        (vertices pre_FA_B[k.val]).map (AlphaConstrainedChoice.fa_graft k)) :
      Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
    enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.FA_graft := by
  unfold enumAlphaConstrainedChoice
  rw [← Multiset.coe_bind]

/-- The Multiset-of-allAlphaConstrainedChoiceList equals the sum of 4 per-bucket
    `enumAlphaConstrainedChoice`. Helper for the head decomposition. -/
private theorem allAlphaConstrainedChoiceList_eq_sum
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) :
    (Multiset.ofList (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B) :
      Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
    enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.T_orig +
    enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.T_graft +
    enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.FA_orig +
    enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.FA_graft := by
  -- LHS: Multiset.ofList of (a ++ b ++ c ++ d) where each is per-bucket source list.
  -- Distribute Multiset.ofList over ++ via ← Multiset.coe_add (3 times).
  -- Then convert each ofList to enumAlpha via the bucket-equalities.
  show (Multiset.ofList (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B) :
        Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) = _
  unfold allAlphaConstrainedChoiceList
  rw [← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add]
  rw [ofList_T_orig_eq_enumAlpha, ofList_T_graft_eq_enumAlpha,
      ofList_FA_orig_eq_enumAlpha, ofList_FA_graft_eq_enumAlpha]

/-- **Head decomposition** for `allAlphaConstrainedChoiceList`. The bind over
    the full source list factors as the sum of 4 per-bucket binds, each over
    the corresponding `enumAlphaConstrainedChoice` value. Sorry-free composition
    of `allAlphaConstrainedChoiceList_eq_sum` + `Multiset.add_bind`. -/
private theorem allAlphaConstrainedChoiceList_bind_decompose
    {γ : Type*}
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (H : AlphaConstrainedChoice F_A pre_T_B pre_FA_B → Multiset γ) :
    (Multiset.ofList (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B)).bind H =
      (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.T_orig).bind H +
      (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.T_graft).bind H +
      (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.FA_orig).bind H +
      (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.FA_graft).bind H := by
  rw [allAlphaConstrainedChoiceList_eq_sum]
  rw [Multiset.add_bind, Multiset.add_bind, Multiset.add_bind]

/-- Variant of `allAlphaConstrainedChoiceList_bind_decompose` in the
    `[4 buckets].bind` form. The outer bind ranges over QuadIdx (the bucket
    sequence), and the inner bind ranges over per-bucket valid targets.

    This form aligns directly with the LHS's α-bind structure in the cons
    case: LHS's `(listChoices [4 buckets] (n+1)).bind α => ...` factors via
    `listChoices_succ` into `[4 buckets].bind first_b => (listChoices [4 buckets] n).bind rest_α => ...`,
    whose first-level bind matches RHS's `[4 buckets].bind first_b => ...`. -/
private theorem allAlphaConstrainedChoiceList_bind_eq_bucketList_bind
    {γ : Type*}
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (H : AlphaConstrainedChoice F_A pre_T_B pre_FA_B → Multiset γ) :
    (Multiset.ofList (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B)).bind H =
      (([QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft] :
          Multiset QuadIdx).bind fun b =>
        (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B b).bind H) := by
  rw [allAlphaConstrainedChoiceList_bind_decompose]
  -- RHS: (T_orig ::ₘ T_graft ::ₘ FA_orig ::ₘ FA_graft ::ₘ 0).bind G
  -- = G T_orig + (G T_graft + (G FA_orig + (G FA_graft + 0)))
  rw [show ([QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft] :
            Multiset QuadIdx) =
        QuadIdx.T_orig ::ₘ QuadIdx.T_graft ::ₘ QuadIdx.FA_orig ::ₘ QuadIdx.FA_graft ::ₘ 0 from rfl]
  rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.cons_bind, Multiset.cons_bind,
      Multiset.zero_bind, add_zero]
  -- Both sides: (enum T_orig).bind H + (enum T_graft).bind H + ... + (enum FA_graft).bind H
  -- LHS is left-assoc; RHS after cons_bind is right-assoc. Use add_assoc.
  rw [add_assoc, add_assoc]

/-- **Factored cons-case decomposition** for `enumGraftingData`. Combines
    `enumGraftingData_succ` with `allAlphaConstrainedChoiceList_bind_eq_bucketList_bind`
    to expose the `[4 buckets].bind` structure on the `first` enumeration.

    This form aligns with the LHS's `(listChoices [4 buckets] (n+1)).bind` form
    after `listChoices_succ`. The cons-case bridge proof case-splits on the
    first bucket, then per first_b matches LHS leaf with RHS leaf. -/
private theorem enumGraftingData_succ_factored
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (n : Nat) :
    enumGraftingData T F_A pre_T_B pre_FA_B (n + 1) =
      (Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
        (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind fun fdata =>
          (([QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft] :
              Multiset QuadIdx).bind fun first_b =>
            (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B first_b).bind fun first_target =>
              (Multiset.ofList
                (listChoices (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B) n)).map
                fun rest_targets =>
                  ({ pre_T_B_choice := choice_T
                     pre_FA_B_choice := fdata
                     C_targets := first_target :: rest_targets }
                   : GraftingData F_A pre_T_B pre_FA_B)) := by
  rw [enumGraftingData_succ]
  -- Convert nested flatMaps to nested binds via ← Multiset.coe_bind, interleaved
  -- with bind_congr to enter binder bodies (rw doesn't recurse into lambdas).
  rw [← Multiset.coe_bind]
  refine Multiset.bind_congr fun choice_T _ => ?_
  rw [← Multiset.coe_bind]
  refine Multiset.bind_congr fun fdata _ => ?_
  rw [← Multiset.coe_bind]
  -- Apply head decomp on the inner `(Multiset.ofList allAlpha).bind first => ...`.
  rw [allAlphaConstrainedChoiceList_bind_eq_bucketList_bind]
  -- The remaining goal differs only in `↑(List.map f xs)` vs `Multiset.map f ↑xs`,
  -- which are defeq via Multiset.map's definition on coerced lists.
  rfl

/-! ### §1.10.1.1: F-side append-singleton substrate

Substrate for the singleton FA_orig case bridge: relates
`buildFIns F_A (pre_FA_B ++ [c]) (fdata ++ [(i₀, v)])` (which arises from
applying `insertionForest_eq_explicit` to `insertionForest F_A (pre_FA_B ++ [c])`
followed by `listChoices_split_bind`) to the per-`i'` modified form (which
arises from the canonical-form RHS via `interpret`'s F-side computation).

Used by `RHS_eq_canonical_msform_singleton_FA_orig`. -/

/-- `perTreePairsFromFChoice` splits over an append-singleton on the data and
    pre_FA_B sides, with the singleton contributing `[(v, c)]` only when its
    bucket index `i₀` matches the queried index `i'`. -/
private theorem perTreePairsFromFChoice_append_singleton
    (F_A pre_FA_B : List (Planar α))
    (fdata : List (Fin F_A.length × Path)) (i₀ : Fin F_A.length) (v : Path)
    (c : Planar α) (hlen : fdata.length = pre_FA_B.length)
    (i' : Fin F_A.length) :
    perTreePairsFromFChoice F_A (pre_FA_B ++ [c]) (fdata ++ [(i₀, v)]) i' =
      perTreePairsFromFChoice F_A pre_FA_B fdata i' ++
        (if i₀ = i' then [(v, c)] else []) := by
  unfold perTreePairsFromFChoice
  rw [List.zip_append hlen, List.filterMap_append]
  congr 1
  show (List.filterMap _ ([((i₀, v), c)] :
          List ((Fin F_A.length × Path) × Planar α))) = _
  rw [List.filterMap_cons, List.filterMap_nil]
  by_cases h : i₀ = i'
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- Companion to `perTreePairsFromFChoice_append_singleton`: `buildFIns` over
    append-singleton equals the per-`i'` modified form, where each F_A[i'] is
    multi-grafted with the original per-tree pairs plus the singleton's
    `(v, c)` contribution at the matching index. -/
private theorem buildFIns_append_singleton
    (F_A pre_FA_B : List (Planar α))
    (fdata : List (Fin F_A.length × Path)) (i₀ : Fin F_A.length) (v : Path)
    (c : Planar α) (hlen : fdata.length = pre_FA_B.length) :
    buildFIns F_A (pre_FA_B ++ [c]) (fdata ++ [(i₀, v)]) =
      (List.finRange F_A.length).map fun i' =>
        multiGraft F_A[i'.val]
          (perTreePairsFromFChoice F_A pre_FA_B fdata i' ++
           (if i₀ = i' then [(v, c)] else [])) := by
  unfold buildFIns
  refine List.map_congr_left fun i' _ => ?_
  rw [perTreePairsFromFChoice_append_singleton F_A pre_FA_B fdata i₀ v c hlen i']

/-! ### §1.10.1.2: Single-guest forest insertion decomposition

Decomposes `insertionForest pre_T_B [c]` (forest-side single-guest insertion)
into a sum over `(k, q)` where `k : Fin pre_T_B.length` selects which tree
in the forest receives `c` and `q ∈ vertices pre_T_B[k.val]` selects where
in that tree.

Used by `RHS_eq_canonical_msform_singleton_T_graft` and `_FA_graft` to bridge
the LHS forest-insertion form with the canonical-RHS per-(k, q) form. -/

/-- `insertion T []` is `{T}` (multi-graft with no pairs is the identity). -/
private theorem insertion_nil (T : Planar α) : insertion T [] = ({T} : Multiset _) := by
  rw [insertion_def]
  show Multiset.ofList ((listChoices (vertices T) 0).map fun choice =>
        multiGraft T (choice.zip [])) = _
  rw [listChoices_zero]
  show Multiset.ofList [multiGraft T (([] : List Path).zip [])] = _
  rw [show (([] : List Path).zip ([] : List (Planar α))) = [] from rfl,
      multiGraft_nil]
  rfl

/-- `insertion T [c]` enumerates over vertices of `T`. -/
private theorem insertion_singleton (T : Planar α) (c : Planar α) :
    insertion T [c] =
      (Multiset.ofList (vertices T)).map fun v => multiGraft T [(v, c)] := by
  rw [insertion_def]
  rw [show ([c] : List (Planar α)).length = 1 from rfl]
  rw [show listChoices (vertices T) 1 = (vertices T).map (fun v => [v]) from by
    show (vertices T).flatMap (fun v => (listChoices (vertices T) 0).map (v :: ·)) = _
    rw [listChoices_zero]
    induction vertices T with
    | nil => rfl
    | cons _ _ ih => rw [List.flatMap_cons]; rw [ih]; rfl]
  rw [List.map_map]
  rfl

/-- Cons-case decomposition: `insertionForest (T :: F) [c]` splits into the
    "[c] goes to T" case (giving `multiGraft T [(v, c)] :: F` for each
    `v ∈ vertices T`) and the "[c] goes to F" case (giving `T :: F'` for each
    `F' ∈ insertionForest F [c]`). -/
private theorem insertionForest_cons_singleton
    (T : Planar α) (F : List (Planar α)) (c : Planar α) :
    insertionForest (T :: F) [c] =
      (insertion T [c]).map (fun T' => T' :: F) +
      (insertionForest F [c]).map (fun F' => T :: F') := by
  rw [insertionForest_cons_cons]
  rw [show ([c] : List (Planar α)).length = 1 from rfl]
  rw [show (Multiset.ofList (listChoices [true, false] 1) : Multiset (List Bool)) =
        ([true] ::ₘ [false] ::ₘ 0) from rfl]
  rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  congr 1
  · -- True case: assignment = [true]; filter_t = [c], filter_f = []
    show (insertion T [c]).bind (fun T' => (insertionForest F []).map fun F' => T' :: F') = _
    rw [insertionForest_nil_guests]
    conv_lhs =>
      rhs; ext T'
      rw [show (({F} : Multiset (List (Planar α))).map (fun F' => T' :: F')) =
            ({(T' :: F)} : Multiset (List (Planar α))) from rfl]
    rw [Multiset.bind_singleton]
  · -- False case: assignment = [false]; filter_t = [], filter_f = [c]
    show (insertion T []).bind (fun T' => (insertionForest F [c]).map fun F' => T' :: F') = _
    rw [insertion_nil]
    rw [Multiset.singleton_bind]

/-- Single-guest forest insertion decomposes into the per-(k, q) form. The
    output `pre_T_B'` differs from `pre_T_B` exactly at index `k`, where it is
    `multiGraft pre_T_B[k] [(q, c)]`. The if/then/else form matches the
    canonical RHS produced by `interpret`'s T_graft (resp. FA_graft) bucket.

    Proof outline:
    - Base case `pre_T_B = []`: both sides are `0`.
    - Cons case `pre_T_B = T :: F`: LHS decomposes via `insertionForest_cons_singleton`
      into a head case (`[c]` goes to `T`) and tail case (`[c]` goes to `F`); RHS
      decomposes via `List.finRange_succ` into `k = 0` head and `k = Fin.succ k_F`
      tail. Match head-to-head and tail-to-tail by IH. -/
private theorem insertionForest_singleton_decomp
    (pre_T_B : List (Planar α)) (c : Planar α) :
    insertionForest pre_T_B [c] =
      (Multiset.ofList (List.finRange pre_T_B.length)).bind fun k =>
        (Multiset.ofList (vertices pre_T_B[k.val])).map fun q =>
          (List.finRange pre_T_B.length).map fun k' =>
            if k' = k then multiGraft pre_T_B[k.val] [(q, c)]
            else pre_T_B[k'.val] := by
  induction pre_T_B with
  | nil =>
    rw [insertionForest_empty_host_nonempty_guests]
    rfl
  | cons T F ih =>
    rw [insertionForest_cons_singleton, insertion_singleton, ih]
    change _ = (Multiset.ofList (List.finRange (F.length + 1))).bind fun k =>
        (Multiset.ofList (vertices ((T :: F)[k.val]))).map fun q =>
          (List.finRange (F.length + 1)).map fun k' =>
            if k' = k then multiGraft ((T :: F)[k.val]) [(q, c)]
            else (T :: F)[k'.val]
    rw [show List.finRange (F.length + 1) =
            (0 : Fin (F.length + 1)) :: (List.finRange F.length).map Fin.succ
        from List.finRange_succ]
    rw [show (Multiset.ofList ((0 : Fin (F.length + 1)) ::
              (List.finRange F.length).map Fin.succ) : Multiset _) =
          (0 : Fin (F.length + 1)) ::ₘ
            Multiset.ofList ((List.finRange F.length).map Fin.succ)
        from rfl]
    rw [Multiset.cons_bind]
    rw [← Multiset.map_coe (l := List.finRange F.length) (f := Fin.succ)]
    rw [Multiset.bind_map]
    congr 1
    · -- HEAD CASE k = 0
      rw [Multiset.map_map]
      have h0 : ((T :: F) : List (Planar α))[(0 : Fin (F.length + 1)).val] = T := rfl
      conv_rhs => rw [h0]
      refine Multiset.map_congr rfl fun v _ => ?_
      show multiGraft T [(v, c)] :: F = _
      rw [List.map_cons, if_pos rfl]
      congr 1
      rw [List.map_map]
      symm
      have hcomp : ((fun k' : Fin (F.length + 1) =>
                       if k' = (0 : Fin (F.length + 1)) then
                         multiGraft T [(v, c)] else (T :: F)[k'.val]) ∘ Fin.succ) =
                   (fun k_F : Fin F.length => F[k_F.val]) := by
        funext k_F
        simp only [Function.comp_apply]
        rw [if_neg (Fin.succ_ne_zero k_F)]
        exact List.getElem_cons_succ _ _ _ _
      rw [hcomp]
      exact List.map_getElem_finRange F
    · -- TAIL CASE
      rw [Multiset.map_bind]
      refine Multiset.bind_congr fun k_F _ => ?_
      have hkF : ((T :: F) : List (Planar α))[(Fin.succ k_F).val] = F[k_F.val] :=
        List.getElem_cons_succ _ _ _ _
      conv_rhs => rw [hkF]
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun q _ => ?_
      show T :: ((List.finRange F.length).map fun k' =>
               if k' = k_F then multiGraft F[k_F.val] [(q, c)] else F[k'.val]) = _
      rw [List.map_cons]
      rw [if_neg (by exact (Fin.succ_ne_zero k_F).symm :
                      (0 : Fin (F.length + 1)) ≠ k_F.succ)]
      show T :: _ = T :: _
      congr 1
      rw [List.map_map]
      refine List.map_congr_left fun k_F' _ => ?_
      simp only [Function.comp_apply]
      by_cases h : k_F' = k_F
      · rw [if_pos h, h, if_pos rfl]
      · rw [if_neg h]
        have hsucc : k_F'.succ ≠ k_F.succ := fun heq => h (by
          have := Fin.val_eq_of_eq heq
          simp [Fin.val_succ] at this
          exact Fin.ext this)
        rw [if_neg hsucc]
        exact (List.getElem_cons_succ _ _ _ _).symm

/-! ### §1.10.2: Singleton-case sub-lemmas for the RHS bridge

Per-`first_b` sub-cases for the singleton case (`C = [c]`) of
`RHS_eq_canonical_msform`. Each lemma bridges:

- LHS: the iteratedQuadSum-leaf with `pres = (fun t => if t = first_b then [c] else [])`
- RHS: the canonical-form RHS evaluated at the `first_b` sub-bucket of
  `enumGraftingData T F_A pre_T_B pre_FA_B 1`.

These compose into `RHS_eq_canonical_msform_singleton` (the full singleton case),
which serves as the structural test of substrate (without IH-recursion). -/

/-- **Singleton T_orig case**: bridges the LHS form (T_orig-bucket pres = [c],
    others = []) with the RHS canonical-form sub-bucket where
    `first_target = .t_orig v`. The proof:
    1. Reduce LHS via `insertionForest_nil_guests` and `Multiset.singleton_bind`
       (B-grafted forests collapse to singletons, append-nil simplifies).
    2. Push `.map msform` inside via `Multiset.map_bind`, then unfold `insertion_def`
       and convert `Multiset.ofList (xs.map f)` to `(Multiset.ofList xs).bind` via
       `← Multiset.map_coe` + `Multiset.bind_map`.
    3. Apply `listChoices_split_bind` to split the length-`(n+1)` choice list into
       (choice_T, choice_v) with `choice_v.length = 1`.
    4. Reduce `Multiset.ofList (listChoices xs 1)` to `(Multiset.ofList xs).bind
       (fun v => {[v]})` then absorb the singleton-bind via `Multiset.bind_assoc`
       + `Multiset.singleton_bind`.
    5. Push RHS's `.map msform` inside via two `Multiset.map_bind` rewrites and
       collapse the inner double-map via `Multiset.map_map`.
    6. Enter the choice_T bind via `Multiset.bind_congr`; derive
       `choice_T.length = pre_T_B.length` from `mem_listChoices_length`; rewrite
       `(choice_T ++ [v]).zip (pre_T_B ++ [c]) = choice_T.zip pre_T_B ++ [(v, c)]`
       via `List.zip_append`.
    7. Apply `insertionForest_eq_explicit` (F-side explicit choice structure),
       collapse `.map.map` chain via `Multiset.map_map` (two layers).
    8. Close via `Multiset.bind_map_comm` which swaps `(vertices T).bind v` with
       `(perKFChoice F_A) listChoices.map fdata` to match the RHS bind order. -/
private theorem RHS_eq_canonical_msform_singleton_T_orig
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (c : Planar α) :
    ((insertionForest pre_T_B ([] : List (Planar α))).bind fun pre_T_B' =>
        (insertion T (pre_T_B' ++ [c])).bind fun T' =>
          (insertionForest pre_FA_B ([] : List (Planar α))).bind fun pre_FA_B' =>
            (insertionForest F_A (pre_FA_B' ++ [])).map fun F' =>
              T' :: F').map (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
      (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind fun fdata =>
        (Multiset.ofList (vertices T)).map fun v =>
          multiGraft T (choice_T.zip pre_T_B ++ [(v, c)]) ::
            buildFIns F_A pre_FA_B fdata).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- Step 1: collapse the insertionForest_nil_guests singletons.
  simp only [insertionForest_nil_guests, List.append_nil, Multiset.singleton_bind]
  -- LHS: ((insertion T (pre_T_B ++ [c])).bind fun T' =>
  --        (insertionForest F_A pre_FA_B).map fun F' => T' :: F').map msform
  -- Step 2: push outer .map msform inside the insertion-bind via Multiset.map_bind,
  -- and Multiset.map_map collapses the inner double map.
  rw [Multiset.map_bind]
  -- LHS: (insertion T (pre_T_B ++ [c])).bind fun T' =>
  --        ((insertionForest F_A pre_FA_B).map fun F' => T' :: F').map msform
  -- Step 3: unfold insertion_def + convert ofList-map to bind via Multiset.bind_map.
  rw [insertion_def]
  rw [show (pre_T_B ++ [c]).length = pre_T_B.length + 1 from by
        rw [List.length_append, List.length_singleton]]
  rw [← Multiset.map_coe, Multiset.bind_map]
  -- LHS: (Multiset.ofList (listChoices (vertices T) (pre_T_B.length + 1))).bind fun choice =>
  --        ((insertionForest F_A pre_FA_B).map fun F' =>
  --          multiGraft T (choice.zip (pre_T_B ++ [c])) :: F').map msform
  -- Step 4: split choice via listChoices_split_bind.
  rw [listChoices_split_bind (vertices T) pre_T_B.length 1]
  -- LHS: (Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
  --        (Multiset.ofList (listChoices (vertices T) 1)).bind fun choice_v =>
  --          ((insertionForest F_A pre_FA_B).map fun F' =>
  --            multiGraft T ((choice_T ++ choice_v).zip (pre_T_B ++ [c])) :: F').map msform
  -- Step 5: reduce listChoices xs 1 to bind over xs giving singleton [v].
  rw [show (Multiset.ofList (listChoices (vertices T) 1) : Multiset (List Path)) =
        ↑((vertices T).flatMap (fun v => [[v]])) from by
      rw [show listChoices (vertices T) 1 =
              (vertices T).flatMap (fun v => (listChoices (vertices T) 0).map (v :: ·))
            from rfl, listChoices_zero]
      rfl]
  -- Convert flatMap to bind on multisets.
  rw [show (↑((vertices T).flatMap (fun v => [[v]])) : Multiset (List Path)) =
        (Multiset.ofList (vertices T)).bind (fun v => ({[v]} : Multiset (List Path))) from by
      rw [← Multiset.coe_bind]; rfl]
  -- Step 6: Use Multiset.bind_assoc + Multiset.singleton_bind to absorb the singleton.
  -- Pattern: ((M.bind f).bind g) = M.bind (fun x => (f x).bind g),
  -- and ({[v]}.bind g) = g [v].
  simp only [Multiset.bind_assoc, Multiset.singleton_bind]
  -- LHS: (Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
  --        (Multiset.ofList (vertices T)).bind fun v =>
  --          ((insertionForest F_A pre_FA_B).map fun F' =>
  --            multiGraft T ((choice_T ++ [v]).zip (pre_T_B ++ [c])) :: F').map msform
  -- RHS-side: push outer .map msform inside via Multiset.map_bind (twice), then
  -- the inner .map (Multiset.ofList ...) collapses via Multiset.map_map.
  conv_rhs => rw [Multiset.map_bind]
  conv_rhs =>
    rhs; ext choice_T
    rw [Multiset.map_bind]
  conv_rhs =>
    rhs; ext choice_T
    rhs; ext fdata
    rw [Multiset.map_map]
  -- RHS: (...).bind choice_T => (...).bind fdata => (...).map fun v =>
  --        msform (multiGraft T (...) :: buildFIns ... fdata)
  -- LHS-side: enter choice_T bind, simplify zip via length hypothesis, then enter
  -- v bind, apply insertionForest_eq_explicit, push msform inside, combine .map.map
  -- via Multiset.map_map, then swap binds via Multiset.bind_bind.
  refine Multiset.bind_congr fun choice_T hChoice_T => ?_
  -- Get length: choice_T ∈ listChoices (vertices T) pre_T_B.length ⇒ choice_T.length = pre_T_B.length.
  rw [Multiset.mem_coe] at hChoice_T
  have hlen : choice_T.length = pre_T_B.length := mem_listChoices_length _ _ _ hChoice_T
  -- Rewrite (choice_T ++ [v]).zip (pre_T_B ++ [c]) = choice_T.zip pre_T_B ++ [(v, c)].
  have hzip : ∀ v : Path, (choice_T ++ [v]).zip (pre_T_B ++ [c]) =
                choice_T.zip pre_T_B ++ [(v, c)] := by
    intro v
    rw [List.zip_append hlen]
    rfl
  -- Inside the choice_T bind, transform LHS step-by-step to match RHS shape.
  -- Step 8a: rewrite zip inside the v-bind body using simp_rw (recurses into binders).
  simp_rw [hzip]
  -- Step 8b: apply insertionForest_eq_explicit to expose F-side choice structure.
  rw [insertionForest_eq_explicit]
  unfold enumFChoices
  -- Step 8c: collapse the inner (.map (buildFIns)).map (multiGraft :: ·) via
  -- Multiset.map_map (twice) — once for the buildFIns/cons combination, once for
  -- pushing msform into the resulting fdata-form. Uses simp_rw to recurse into
  -- the v-bind body.
  simp_rw [Multiset.map_map]
  -- Step 8d: now LHS inside choice_T bind:
  -- (Multiset.ofList (vertices T)).bind fun v =>
  --   (Multiset.ofList listChoices').map fun fdata =>
  --     msform (multiGraft T (choice_T.zip pre_T_B ++ [(v, c)]) ::
  --              buildFIns F_A pre_FA_B fdata)
  -- RHS inside choice_T bind:
  -- (Multiset.ofList listChoices').bind fun fdata =>
  --   (Multiset.ofList (vertices T)).map fun v =>
  --     msform (multiGraft T (choice_T.zip pre_T_B ++ [(v, c)]) ::
  --              buildFIns F_A pre_FA_B fdata)
  -- Step 9: swap bind v ↔ bind fdata via Multiset.bind_map_comm.
  exact Multiset.bind_map_comm (Multiset.ofList (vertices T))
    (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length))

/-- **Singleton FA_orig case**: bridges the LHS form (FA_orig-bucket pres = [c],
    others = []) with the RHS canonical-form sub-bucket where
    `first_target = .fa_orig i v`. The proof:
    1. Reduce LHS via `insertionForest_nil_guests` and `Multiset.singleton_bind`.
    2. Push `.map msform` inside via `Multiset.map_bind`, unfold `insertion_def`.
    3. Apply `insertionForest_eq_explicit` to F-side `(pre_FA_B ++ [c])`,
       collapse the chain via `Multiset.map_map`.
    4. Convert `.map (buildFIns ...)` to `.bind (· => {buildFIns ...})` so we
       can apply `listChoices_split_bind` (which requires bind form).
    5. Apply `listChoices_split_bind` (m = pre_FA_B.length, n = 1) to split the
       choice into (fdata, iv_list).
    6. Reduce `listChoices xs 1` to bind over xs giving singleton `[(i, v)]`.
    7. Apply `buildFIns_append_singleton` to expose the per-`i'` modified form
       (uses `mem_listChoices_length` for length hypothesis).
    8. Match RHS structure: the LHS's `(perKFChoice F_A).bind` aligns with RHS's
       `(List.finRange F_A.length).bind fun i => (vertices F_A[i.val]).map fun v`
       via the perKFChoice unfolding. -/
private theorem RHS_eq_canonical_msform_singleton_FA_orig
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (c : Planar α) :
    ((insertionForest pre_T_B ([] : List (Planar α))).bind fun pre_T_B' =>
        (insertion T (pre_T_B' ++ [])).bind fun T' =>
          (insertionForest pre_FA_B ([] : List (Planar α))).bind fun pre_FA_B' =>
            (insertionForest F_A (pre_FA_B' ++ [c])).map fun F' =>
              T' :: F').map (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
      (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind fun fdata =>
        (Multiset.ofList (List.finRange F_A.length)).bind fun i =>
          (Multiset.ofList (vertices F_A[i.val])).map fun v =>
            multiGraft T (choice_T.zip pre_T_B) ::
              (List.finRange F_A.length).map fun i' =>
                multiGraft F_A[i'.val]
                  (perTreePairsFromFChoice F_A pre_FA_B fdata i' ++
                   (if i = i' then [(v, c)] else []))).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- Step 1: collapse insertionForest_nil_guests singletons + List.append_nil.
  simp only [insertionForest_nil_guests, List.append_nil, Multiset.singleton_bind]
  -- LHS: ((insertion T pre_T_B).bind fun T' =>
  --        (insertionForest F_A (pre_FA_B ++ [c])).map fun F' => T' :: F').map msform
  -- Step 2: push .map msform inside via Multiset.map_bind.
  rw [Multiset.map_bind]
  -- Step 3: unfold insertion_def + convert ofList-map to bind.
  rw [insertion_def, ← Multiset.map_coe, Multiset.bind_map]
  -- LHS: (Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
  --        ((insertionForest F_A (pre_FA_B ++ [c])).map fun F' =>
  --          multiGraft T (choice_T.zip pre_T_B) :: F').map msform
  -- Step 4: apply insertionForest_eq_explicit, then collapse map chain via Multiset.map_map.
  simp_rw [insertionForest_eq_explicit, Multiset.map_map]
  unfold enumFChoices
  -- Step 5: normalize (pre_FA_B ++ [c]).length = pre_FA_B.length + 1.
  rw [show (pre_FA_B ++ [c]).length = pre_FA_B.length + 1 from by
        rw [List.length_append, List.length_singleton]]
  -- LHS: (Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
  --        (Multiset.ofList (listChoices (perKFChoice F_A) (pre_FA_B.length + 1))).map
  --          fun fdata =>
  --            msform (multiGraft T (choice_T.zip pre_T_B) ::
  --                    buildFIns F_A (pre_FA_B ++ [c]) fdata)
  -- Step 6: convert .map to .bind {singleton}, apply listChoices_split_bind, convert back.
  simp_rw [← Multiset.bind_singleton, listChoices_split_bind]
  -- After listChoices_split_bind:
  -- LHS: ... bind choice_T => bind fdata over (perKFChoice (pre_FA_B.length)) =>
  --         bind iv_list over (perKFChoice 1) => {msform (... buildFIns ... (fdata ++ iv_list))}
  -- Step 7: reduce listChoices xs 1 to bind over xs giving singleton [(i, v)].
  rw [show (Multiset.ofList (listChoices (perKFChoice F_A) 1) :
            Multiset (List (Fin F_A.length × Path))) =
        ↑((perKFChoice F_A).flatMap (fun iv => [[iv]])) from by
      rw [show listChoices (perKFChoice F_A) 1 =
              (perKFChoice F_A).flatMap (fun iv =>
                (listChoices (perKFChoice F_A) 0).map (iv :: ·)) from rfl,
          listChoices_zero]
      rfl]
  rw [show (↑((perKFChoice F_A).flatMap (fun iv => [[iv]])) :
            Multiset (List (Fin F_A.length × Path))) =
        (Multiset.ofList (perKFChoice F_A)).bind
          (fun iv => ({[iv]} : Multiset (List (Fin F_A.length × Path)))) from by
      rw [← Multiset.coe_bind]; rfl]
  -- Step 8: absorb the singleton-bind via Multiset.bind_assoc + Multiset.singleton_bind.
  simp only [Multiset.bind_assoc, Multiset.singleton_bind]
  -- LHS: bind choice_T => bind fdata => bind iv => {msform (multiGraft T (choice_T.zip pre_T_B)
  --        :: buildFIns F_A (pre_FA_B ++ [c]) (fdata ++ [iv]))}
  -- Step 9: enter binds, apply buildFIns_append_singleton with length hypothesis.
  refine Multiset.bind_congr fun choice_T _ => ?_
  refine Multiset.bind_congr fun fdata hFdata => ?_
  rw [Multiset.mem_coe] at hFdata
  have hflen : fdata.length = pre_FA_B.length :=
    mem_listChoices_length _ _ _ hFdata
  -- Step 10: unfold the function composition so buildFIns is directly visible,
  -- then rewrite via append-singleton substrate (uses length hyp).
  simp_rw [Function.comp_apply]
  conv_lhs =>
    rhs; ext iv
    rw [show iv = (iv.fst, iv.snd) from rfl,
        buildFIns_append_singleton F_A pre_FA_B fdata iv.fst iv.snd c hflen]
  -- LHS now:
  -- (Multiset.ofList (perKFChoice F_A)).bind fun iv =>
  --   {msform (multiGraft T (choice_T.zip pre_T_B) ::
  --      (List.finRange F_A.length).map fun i' =>
  --        multiGraft F_A[i'.val] (perTreePairs F_A pre_FA_B fdata i' ++
  --                                (if iv.fst = i' then [(iv.snd, c)] else [])))}
  -- Step 11: expand (perKFChoice F_A) via its definition into nested bind/map.
  -- perKFChoice F_A = (finRange F_A.length).flatMap fun i => (vertices F_A[i.val]).map fun v => (i, v)
  rw [show (Multiset.ofList (perKFChoice F_A) : Multiset (Fin F_A.length × Path)) =
        (Multiset.ofList (List.finRange F_A.length)).bind fun i =>
          (Multiset.ofList (vertices F_A[i.val])).map fun v => (i, v) from by
      unfold perKFChoice
      rw [← Multiset.coe_bind]
      refine Multiset.bind_congr fun i _ => ?_
      rw [← Multiset.map_coe]]
  -- LHS: ((finRange).bind fun i => (vertices).map fun v => (i, v)).bind G
  --    = (finRange).bind fun i => ((vertices).map fun v => (i, v)).bind G  -- bind_assoc
  --    = (finRange).bind fun i => (vertices).bind fun v => G (i, v)         -- bind_map
  rw [Multiset.bind_assoc]
  simp_rw [Multiset.bind_map]
  -- After simp_rw [Multiset.bind_map], simp's reflexivity step often closes the
  -- whole goal because LHS's `bind v => {...}` and RHS's `map v => ...` reduce
  -- to the same normal form via Multiset.bind_singleton (which simp_rw applied
  -- in reverse direction to RHS during the rewrite chain).

/-- **Singleton T_graft case**: bridges the LHS form (T_graft-bucket pres = [c],
    others = []) with the RHS canonical-form sub-bucket where
    `first_target = .t_graft k q`. The proof:
    1. Reduce LHS via `insertionForest_nil_guests` and `Multiset.singleton_bind`
       (the empty FA buckets collapse).
    2. Push `.map msform` inside two layers of bind via `Multiset.map_bind` and
       collapse the inner double-map via `Multiset.map_map`.
    3. Apply `insertionForest_singleton_decomp` to expand `insertionForest pre_T_B [c]`
       into the per-(k, q) form.
    4. Apply `Multiset.bind_assoc` + `Multiset.bind_map` to lift the (k, q) bind
       outside `pre_T_B'` and absorb the `q` map into a bind.
    5. Apply `insertion_def` (with `pre_T_B'.length = pre_T_B.length` from
       the substrate's `(List.finRange pre_T_B.length).map ...` shape) and convert
       `Multiset.ofList ((listChoices ...).map ...) = (Multiset.ofList listChoices).bind`
       via `← Multiset.map_coe + Multiset.bind_map`.
    6. Apply `insertionForest_eq_explicit` to the F-side (`insertionForest F_A pre_FA_B`)
       and collapse the chain via `Multiset.map_map`.
    7. Push `.map msform` through to the inner cons-form.
    8. Reorder binds via `Multiset.bind_bind` (twice, to swap k-bind and q-bind
       outside choice_T-bind) and `Multiset.bind_map_comm` (to swap q-bind with
       fdata-map). -/
private theorem RHS_eq_canonical_msform_singleton_T_graft
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (c : Planar α) :
    ((insertionForest pre_T_B [c]).bind fun pre_T_B' =>
        (insertion T (pre_T_B' ++ [])).bind fun T' =>
          (insertionForest pre_FA_B ([] : List (Planar α))).bind fun pre_FA_B' =>
            (insertionForest F_A (pre_FA_B' ++ [])).map fun F' =>
              T' :: F').map (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
      (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind fun fdata =>
        (Multiset.ofList (List.finRange pre_T_B.length)).bind fun k =>
          (Multiset.ofList (vertices pre_T_B[k.val])).map fun q =>
            multiGraft T (choice_T.zip ((List.finRange pre_T_B.length).map fun k' =>
              if k' = k then multiGraft pre_T_B[k.val] [(q, c)]
              else pre_T_B[k'.val])) ::
              buildFIns F_A pre_FA_B fdata).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- Step 1: collapse the empty FA bucket binds + append-nil simplifications.
  simp only [insertionForest_nil_guests, List.append_nil, Multiset.singleton_bind]
  -- LHS: ((insertionForest pre_T_B [c]).bind fun pre_T_B' =>
  --        (insertion T pre_T_B').bind fun T' =>
  --          (insertionForest F_A pre_FA_B).map fun F' =>
  --            T' :: F').map msform
  -- Step 2: push .map msform inside two layers of bind, collapse inner double-map.
  rw [Multiset.map_bind]
  conv_lhs =>
    rhs; ext pre_T_B'
    rw [Multiset.map_bind]
  conv_lhs =>
    rhs; ext pre_T_B'
    rhs; ext T'
    rw [Multiset.map_map]
  -- LHS: (insertionForest pre_T_B [c]).bind fun pre_T_B' =>
  --        (insertion T pre_T_B').bind fun T' =>
  --          (insertionForest F_A pre_FA_B).map fun F' =>
  --            msform (T' :: F')
  -- Step 3: apply insertionForest_singleton_decomp.
  rw [insertionForest_singleton_decomp]
  -- Step 4: lift outer (k, q) bind/map outside pre_T_B' bind.
  rw [Multiset.bind_assoc]
  conv_lhs =>
    rhs; ext k
    rw [Multiset.bind_map]
  -- LHS: (Multiset.ofList (List.finRange pre_T_B.length)).bind fun k =>
  --        (Multiset.ofList (vertices pre_T_B[k.val])).bind fun q =>
  --          (insertion T pre_T_B'_kq).bind fun T' =>
  --            (insertionForest F_A pre_FA_B).map fun F' =>
  --              msform (T' :: F')
  -- where pre_T_B'_kq = (List.finRange pre_T_B.length).map fun k' =>
  --   if k' = k then multiGraft pre_T_B[k.val] [(q, c)] else pre_T_B[k'.val].
  -- Step 5: apply insertion_def. pre_T_B'_kq.length = pre_T_B.length.
  conv_lhs =>
    rhs; ext k
    rhs; ext q
    rw [insertion_def]
    rw [show ((List.finRange pre_T_B.length).map fun k' : Fin pre_T_B.length =>
              if k' = k then multiGraft pre_T_B[k.val] [(q, c)]
              else pre_T_B[k'.val]).length = pre_T_B.length from by
        rw [List.length_map, List.length_finRange]]
    rw [← Multiset.map_coe, Multiset.bind_map]
  -- Step 6: apply insertionForest_eq_explicit on F-side.
  conv_lhs =>
    rhs; ext k
    rhs; ext q
    rhs; ext choice_T
    rw [insertionForest_eq_explicit]
    rw [show enumFChoices F_A pre_FA_B =
            Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length) from rfl]
    rw [Multiset.map_map]
  -- LHS: (Multiset.ofList (List.finRange pre_T_B.length)).bind fun k =>
  --        (Multiset.ofList (vertices pre_T_B[k.val])).bind fun q =>
  --          (Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
  --            (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).map fun fdata =>
  --              msform (multiGraft T (choice_T.zip pre_T_B'_kq) ::
  --                       buildFIns F_A pre_FA_B fdata)
  -- Step 7: reorder binds. Current: k → q → choice_T → fdata (with fdata as map).
  -- Target: choice_T → fdata → k → q (with q as map).
  -- Inner reordering: swap (q bind, fdata map) → (fdata bind, q map) via bind_map_comm.
  -- Outer reordering: swap (k bind, q bind) with (choice_T bind, fdata bind) via bind_bind.
  -- Step 7a: swap q bind with choice_T bind via bind_bind.
  conv_lhs =>
    rhs; ext k
    rw [Multiset.bind_bind]
  -- LHS: (List.finRange ...).bind fun k =>
  --        (listChoices (vertices T) ...).bind fun choice_T =>
  --          (vertices pre_T_B[k.val]).bind fun q =>
  --            (listChoices (perKFChoice F_A) ...).map fun fdata => ...
  -- Step 7b: swap k bind with choice_T bind via bind_bind.
  rw [Multiset.bind_bind]
  -- LHS: (listChoices (vertices T) ...).bind fun choice_T =>
  --        (List.finRange ...).bind fun k =>
  --          (vertices pre_T_B[k.val]).bind fun q =>
  --            (listChoices (perKFChoice F_A) ...).map fun fdata => ...
  -- Step 7c: inside choice_T bind, swap (q bind, fdata map) → (fdata bind, q map).
  conv_lhs =>
    rhs; ext choice_T
    rhs; ext k
    rw [Multiset.bind_map_comm]
  -- LHS: (listChoices (vertices T) ...).bind fun choice_T =>
  --        (List.finRange ...).bind fun k =>
  --          (listChoices (perKFChoice F_A) ...).bind fun fdata =>
  --            (vertices pre_T_B[k.val]).map fun q => ...
  -- Step 7d: swap k bind with fdata bind via bind_bind.
  conv_lhs =>
    rhs; ext choice_T
    rw [Multiset.bind_bind]
  -- LHS: (listChoices (vertices T) ...).bind fun choice_T =>
  --        (listChoices (perKFChoice F_A) ...).bind fun fdata =>
  --          (List.finRange ...).bind fun k =>
  --            (vertices pre_T_B[k.val]).map fun q => ...
  -- Step 8: push RHS .map msform through. RHS has the same outer structure
  -- (choice_T → fdata → k → q with q as map).
  conv_rhs => rw [Multiset.map_bind]
  conv_rhs =>
    rhs; ext choice_T
    rw [Multiset.map_bind]
  conv_rhs =>
    rhs; ext choice_T
    rhs; ext fdata
    rw [Multiset.map_bind]
  conv_rhs =>
    rhs; ext choice_T
    rhs; ext fdata
    rhs; ext k
    rw [Multiset.map_map]
  -- Both sides now have: choice_T → fdata → k → q.map (msform of result).
  -- Step 9: close by rfl (α-equivalent up to bound variable names).
  rfl

/-- **Singleton FA_graft case**: bridges the LHS form (FA_graft-bucket pres = [c],
    others = []) with the RHS canonical-form sub-bucket where
    `first_target = .fa_graft k q`. The proof structurally mirrors `_T_graft`
    but on the F-side: the substrate `insertionForest_singleton_decomp` is
    applied to `insertionForest pre_FA_B [c]` (forest insertion of [c] into
    the F-side bucket), and `insertionForest_eq_explicit` is applied to the
    F_A-grafting step with the modified `pre_FA_B'_kq` as the second arg. -/
private theorem RHS_eq_canonical_msform_singleton_FA_graft
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (c : Planar α) :
    ((insertionForest pre_T_B ([] : List (Planar α))).bind fun pre_T_B' =>
        (insertion T (pre_T_B' ++ [])).bind fun T' =>
          (insertionForest pre_FA_B [c]).bind fun pre_FA_B' =>
            (insertionForest F_A (pre_FA_B' ++ [])).map fun F' =>
              T' :: F').map (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
      (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind fun fdata =>
        (Multiset.ofList (List.finRange pre_FA_B.length)).bind fun k =>
          (Multiset.ofList (vertices pre_FA_B[k.val])).map fun q =>
            multiGraft T (choice_T.zip pre_T_B) ::
              buildFIns F_A
                ((List.finRange pre_FA_B.length).map fun k' =>
                  if k' = k then multiGraft pre_FA_B[k.val] [(q, c)]
                  else pre_FA_B[k'.val])
                fdata).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- Step 1: collapse the empty T_graft bucket binds + append-nil simplifications.
  simp only [insertionForest_nil_guests, List.append_nil, Multiset.singleton_bind]
  -- LHS: ((insertion T pre_T_B).bind fun T' =>
  --        (insertionForest pre_FA_B [c]).bind fun pre_FA_B' =>
  --          (insertionForest F_A pre_FA_B').map fun F' =>
  --            T' :: F').map msform
  -- Step 2: push .map msform inside two layers of bind, collapse inner double-map.
  rw [Multiset.map_bind]
  conv_lhs =>
    rhs; ext T'
    rw [Multiset.map_bind]
  conv_lhs =>
    rhs; ext T'
    rhs; ext pre_FA_B'
    rw [Multiset.map_map]
  -- LHS: (insertion T pre_T_B).bind fun T' =>
  --        (insertionForest pre_FA_B [c]).bind fun pre_FA_B' =>
  --          (insertionForest F_A pre_FA_B').map fun F' =>
  --            msform (T' :: F')
  -- Step 3: apply insertionForest_singleton_decomp to F-side guest-insertion.
  conv_lhs =>
    rhs; ext T'
    rw [insertionForest_singleton_decomp]
  -- Step 4: lift outer (k, q) bind/map outside pre_FA_B' bind.
  conv_lhs =>
    rhs; ext T'
    rw [Multiset.bind_assoc]
  conv_lhs =>
    rhs; ext T'
    rhs; ext k
    rw [Multiset.bind_map]
  -- LHS: (insertion T pre_T_B).bind fun T' =>
  --        (Multiset.ofList (List.finRange pre_FA_B.length)).bind fun k =>
  --          (Multiset.ofList (vertices pre_FA_B[k.val])).bind fun q =>
  --            (insertionForest F_A pre_FA_B'_kq).map fun F' =>
  --              msform (T' :: F')
  -- Step 5: apply insertion_def to T-side, convert ofList-map to bind.
  rw [insertion_def]
  rw [← Multiset.map_coe, Multiset.bind_map]
  -- LHS: (Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
  --        (Multiset.ofList (List.finRange pre_FA_B.length)).bind fun k =>
  --          (Multiset.ofList (vertices pre_FA_B[k.val])).bind fun q =>
  --            (insertionForest F_A pre_FA_B'_kq).map fun F' =>
  --              msform (multiGraft T (choice_T.zip pre_T_B) :: F')
  -- Step 6: apply insertionForest_eq_explicit on F_A-side with pre_FA_B'_kq.
  -- Length: pre_FA_B'_kq.length = pre_FA_B.length.
  conv_lhs =>
    rhs; ext choice_T
    rhs; ext k
    rhs; ext q
    rw [insertionForest_eq_explicit]
    rw [show enumFChoices F_A
            ((List.finRange pre_FA_B.length).map fun k' : Fin pre_FA_B.length =>
              if k' = k then multiGraft pre_FA_B[k.val] [(q, c)]
              else pre_FA_B[k'.val]) =
          Multiset.ofList (listChoices (perKFChoice F_A)
            ((List.finRange pre_FA_B.length).map fun k' : Fin pre_FA_B.length =>
              if k' = k then multiGraft pre_FA_B[k.val] [(q, c)]
              else pre_FA_B[k'.val]).length) from rfl]
    rw [show ((List.finRange pre_FA_B.length).map fun k' : Fin pre_FA_B.length =>
              if k' = k then multiGraft pre_FA_B[k.val] [(q, c)]
              else pre_FA_B[k'.val]).length = pre_FA_B.length from by
        rw [List.length_map, List.length_finRange]]
    rw [Multiset.map_map]
  -- LHS: (listChoices (vertices T) ...).bind fun choice_T =>
  --        (List.finRange pre_FA_B.length).bind fun k =>
  --          (vertices pre_FA_B[k.val]).bind fun q =>
  --            (listChoices (perKFChoice F_A) pre_FA_B.length).map fun fdata =>
  --              msform (multiGraft T (...) :: buildFIns F_A pre_FA_B'_kq fdata)
  -- Step 7: reorder binds. Current: choice_T → k → q → fdata.map.
  -- Target: choice_T → fdata → k → q.map.
  -- Step 7a: swap (q bind, fdata map) → (fdata bind, q map) via bind_map_comm.
  conv_lhs =>
    rhs; ext choice_T
    rhs; ext k
    rw [Multiset.bind_map_comm]
  -- LHS: choice_T → k → fdata → q.map
  -- Step 7b: swap k and fdata via bind_bind.
  conv_lhs =>
    rhs; ext choice_T
    rw [Multiset.bind_bind]
  -- LHS: choice_T → fdata → k → q.map
  -- Step 8: push RHS .map msform inside.
  conv_rhs => rw [Multiset.map_bind]
  conv_rhs =>
    rhs; ext choice_T
    rw [Multiset.map_bind]
  conv_rhs =>
    rhs; ext choice_T
    rhs; ext fdata
    rw [Multiset.map_bind]
  conv_rhs =>
    rhs; ext choice_T
    rhs; ext fdata
    rhs; ext k
    rw [Multiset.map_map]
  -- Both sides now have: choice_T → fdata → k → q.map (msform of result).
  -- Step 9: close by rfl (α-equivalent up to bound variable names).
  rfl

/-! ### §1.10.3: Per-bucket interpret reductions (singleton C-targets)

Per-bucket reductions of `interpret T ⟨choice_T, fdata, [first_target]⟩ [c]`
into closed form. Each lemma covers one bucket of `first_target`'s
constructor. Used by `RHS_eq_canonical_msform_singleton` to bridge the
RHS canonical form to the per-bucket sub-lemma RHS forms. -/

/-- **T_orig interpret reduction**: when `first_target = .t_orig v` and
    `C = [c]`, interpret produces:
    - T-side: `multiGraft T (choice_T.zip pre_T_B ++ [(v, c)])` — the only
      modification is the appended `(v, c)` graft pair; no T_graft pairs
      modify pre_T_B.
    - F-side: `buildFIns F_A pre_FA_B fdata` — no FA_orig or FA_graft pairs
      modify the F-side.

    Proof outline:
    1. `unfold interpret` exposes the let-binding structure.
    2. C_paired = [(.t_orig v, c)]; reduce extractors via `_cons_t_orig` lemmas:
       T_orig_pairs = [(v, c)]; T_graft/FA_orig/FA_graft pairs = [].
    3. pre_T_B' = (finRange).map (multiGraft pre_T_B[k.val] []) = pre_T_B
       via multiGraft_nil + List.map_getElem_finRange.
    4. F-side similar reduction. -/
private theorem interpret_singleton_t_orig
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (choice_T : List Path) (fdata : List (Fin F_A.length × Path))
    (v : Path) (c : Planar α) :
    interpret T
      ({ pre_T_B_choice := choice_T
         pre_FA_B_choice := fdata
         C_targets := [AlphaConstrainedChoice.t_orig v
            (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B)] }
       : GraftingData F_A pre_T_B pre_FA_B) [c] =
      multiGraft T (choice_T.zip pre_T_B ++ [(v, c)]) ::
        buildFIns F_A pre_FA_B fdata := by
  -- Helper: under T_orig context, pre_T_B' = pre_T_B (no T_graft modifications).
  have hpre_T_B' :
      ((List.finRange pre_T_B.length).map fun k =>
        multiGraft pre_T_B[k.val]
          (extractTGraftPairsAt
            [(AlphaConstrainedChoice.t_orig
                (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) v, c)] k)) =
      pre_T_B := by
    have h : ((List.finRange pre_T_B.length).map fun k =>
        multiGraft pre_T_B[k.val]
          (extractTGraftPairsAt
            [(AlphaConstrainedChoice.t_orig
                (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) v, c)] k)) =
        (List.finRange pre_T_B.length).map (fun k => pre_T_B[k.val]) := by
      apply List.map_congr_left
      intro k _
      rw [extractTGraftPairsAt_cons_t_orig]
      exact multiGraft_nil _
    rw [h, List.map_getElem_finRange]
  -- Helper: under T_orig context, pre_FA_B' = pre_FA_B (no FA_graft modifications).
  have hpre_FA_B' :
      ((List.finRange pre_FA_B.length).map fun k =>
        multiGraft pre_FA_B[k.val]
          (extractFAGraftPairsAt
            [(AlphaConstrainedChoice.t_orig
                (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) v, c)] k)) =
      pre_FA_B := by
    have h : ((List.finRange pre_FA_B.length).map fun k =>
        multiGraft pre_FA_B[k.val]
          (extractFAGraftPairsAt
            [(AlphaConstrainedChoice.t_orig
                (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) v, c)] k)) =
        (List.finRange pre_FA_B.length).map (fun k => pre_FA_B[k.val]) := by
      apply List.map_congr_left
      intro k _
      rw [extractFAGraftPairsAt_cons_t_orig]
      exact multiGraft_nil _
    rw [h, List.map_getElem_finRange]
  -- Now unfold interpret and substitute the helpers.
  unfold interpret
  simp only [List.zip_cons_cons, List.zip_nil_left]
  rw [hpre_T_B', hpre_FA_B']
  -- T_orig_pairs = [(v, c)]; F_orig_pairs at i = [].
  rw [show extractTOrigPairs
        [(AlphaConstrainedChoice.t_orig
            (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) v, c)] = [(v, c)] from rfl]
  congr 1
  -- F-side
  apply List.map_congr_left
  intro i _
  congr 1
  -- perTreePairsFromFChoice ... i ++ [] = perTreePairsFromFChoice ... i
  rw [show extractFAOrigPairsAt
        [(AlphaConstrainedChoice.t_orig
            (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) v, c)] i =
        ([] : List (Path × Planar α)) from rfl]
  rw [List.append_nil]
  rfl

/-- **T_graft interpret reduction**: when `first_target = .t_graft k q` and
    `C = [c]`, interpret produces:
    - T-side: `multiGraft T (choice_T.zip pre_T_B'_kq)` where `pre_T_B'_kq`
      modifies pre_T_B at index k by `multiGraft pre_T_B[k.val] [(q, c)]`.
    - F-side: `buildFIns F_A pre_FA_B fdata` — no F-side changes.

    The T_graft sub-lemma's RHS uses `if k' = k then multiGraft pre_T_B[k.val]
    [(q, c)] else pre_T_B[k'.val]` for the per-`k'` modification; interpret
    naturally produces `multiGraft pre_T_B[k'.val] (if k' = k then [(q, c)]
    else [])`. These match because (a) k' = k makes k'.val = k.val, and
    (b) `multiGraft x [] = x` (multiGraft_nil). -/
private theorem interpret_singleton_t_graft
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (choice_T : List Path) (fdata : List (Fin F_A.length × Path))
    (k : Fin pre_T_B.length) (q : Path) (c : Planar α) :
    interpret T
      ({ pre_T_B_choice := choice_T
         pre_FA_B_choice := fdata
         C_targets := [AlphaConstrainedChoice.t_graft
            (F_A := F_A) (pre_FA_B := pre_FA_B) k q] }
       : GraftingData F_A pre_T_B pre_FA_B) [c] =
      multiGraft T (choice_T.zip ((List.finRange pre_T_B.length).map fun k' =>
        if k' = k then multiGraft pre_T_B[k.val] [(q, c)]
        else pre_T_B[k'.val])) ::
        buildFIns F_A pre_FA_B fdata := by
  -- Helper: under T_graft k q context, pre_T_B' equals the if-then-else form.
  have hpre_T_B' :
      ((List.finRange pre_T_B.length).map fun k' =>
        multiGraft pre_T_B[k'.val]
          (extractTGraftPairsAt
            [(AlphaConstrainedChoice.t_graft
                (F_A := F_A) (pre_FA_B := pre_FA_B) k q, c)] k')) =
      ((List.finRange pre_T_B.length).map fun k' =>
        if k' = k then multiGraft pre_T_B[k.val] [(q, c)]
        else pre_T_B[k'.val]) := by
    apply List.map_congr_left
    intro k' _
    by_cases h : k' = k
    · -- h : k' = k. Lemma's k' is constructor index = my `k`; lemma's k = query = my `k'`.
      -- So lemma's h : k' = k → my_k = my_k', i.e., h.symm.
      rw [extractTGraftPairsAt_cons_t_graft_eq (k := k') (k' := k) (q := q) (c := c)
            (rest_paired := []) (h := h.symm)]
      rw [show extractTGraftPairsAt
            ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α)) k' =
            ([] : List (Path × Planar α)) from rfl]
      rw [if_pos h]
      congr 2
      exact Fin.val_eq_of_eq h
    · -- h : k' ≠ k. Lemma's h : k' ≠ k → my_k ≠ my_k', i.e., Ne.symm h.
      rw [extractTGraftPairsAt_cons_t_graft_neq (k := k') (k' := k) (q := q) (c := c)
            (rest_paired := []) (h := Ne.symm h)]
      rw [show extractTGraftPairsAt
            ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α)) k' =
            ([] : List (Path × Planar α)) from rfl]
      rw [if_neg h, multiGraft_nil]
  -- Helper: under T_graft context, pre_FA_B' = pre_FA_B (no FA_graft pairs).
  have hpre_FA_B' :
      ((List.finRange pre_FA_B.length).map fun k' =>
        multiGraft pre_FA_B[k'.val]
          (extractFAGraftPairsAt
            [(AlphaConstrainedChoice.t_graft
                (F_A := F_A) (pre_FA_B := pre_FA_B) k q, c)] k')) =
      pre_FA_B := by
    have h : ((List.finRange pre_FA_B.length).map fun k' =>
        multiGraft pre_FA_B[k'.val]
          (extractFAGraftPairsAt
            [(AlphaConstrainedChoice.t_graft
                (F_A := F_A) (pre_FA_B := pre_FA_B) k q, c)] k')) =
        (List.finRange pre_FA_B.length).map (fun k' => pre_FA_B[k'.val]) := by
      apply List.map_congr_left
      intro k' _
      rw [extractFAGraftPairsAt_cons_t_graft]
      exact multiGraft_nil _
    rw [h, List.map_getElem_finRange]
  -- Now unfold interpret and substitute the helpers.
  unfold interpret
  simp only [List.zip_cons_cons, List.zip_nil_left]
  rw [hpre_T_B', hpre_FA_B']
  -- T_orig_pairs = []; FA_orig_pairs at i = []; the multiGraft T arg becomes
  -- choice_T.zip pre_T_B'_kq ++ [] = choice_T.zip pre_T_B'_kq.
  rw [show extractTOrigPairs
        [(AlphaConstrainedChoice.t_graft
            (F_A := F_A) (pre_FA_B := pre_FA_B) k q, c)] =
        ([] : List (Path × Planar α)) from rfl]
  rw [List.append_nil]
  congr 1
  -- F-side
  apply List.map_congr_left
  intro i _
  congr 1
  rw [show extractFAOrigPairsAt
        [(AlphaConstrainedChoice.t_graft
            (F_A := F_A) (pre_FA_B := pre_FA_B) k q, c)] i =
        ([] : List (Path × Planar α)) from rfl]
  rw [List.append_nil]
  rfl

/-- **FA_orig interpret reduction**: when `first_target = .fa_orig i v` and
    `C = [c]`, interpret produces:
    - T-side: `multiGraft T (choice_T.zip pre_T_B)` — no T-side changes.
    - F-side: per-`i'` modified, with `[(v, c)]` appended at index `i' = i`.

    Matches the FA_orig sub-lemma's RHS structure with the `if i = i'` branch. -/
private theorem interpret_singleton_fa_orig
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (choice_T : List Path) (fdata : List (Fin F_A.length × Path))
    (i : Fin F_A.length) (v : Path) (c : Planar α) :
    interpret T
      ({ pre_T_B_choice := choice_T
         pre_FA_B_choice := fdata
         C_targets := [AlphaConstrainedChoice.fa_orig
            (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i v] }
       : GraftingData F_A pre_T_B pre_FA_B) [c] =
      multiGraft T (choice_T.zip pre_T_B) ::
        (List.finRange F_A.length).map fun i' =>
          multiGraft F_A[i'.val]
            (perTreePairsFromFChoice F_A pre_FA_B fdata i' ++
             (if i = i' then [(v, c)] else [])) := by
  -- Helper: pre_T_B' = pre_T_B (no T_graft pairs).
  have hpre_T_B' :
      ((List.finRange pre_T_B.length).map fun k =>
        multiGraft pre_T_B[k.val]
          (extractTGraftPairsAt
            [(AlphaConstrainedChoice.fa_orig
                (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i v, c)] k)) =
      pre_T_B := by
    have h : ((List.finRange pre_T_B.length).map fun k =>
        multiGraft pre_T_B[k.val]
          (extractTGraftPairsAt
            [(AlphaConstrainedChoice.fa_orig
                (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i v, c)] k)) =
        (List.finRange pre_T_B.length).map (fun k => pre_T_B[k.val]) := by
      apply List.map_congr_left
      intro k _
      rw [extractTGraftPairsAt_cons_fa_orig]
      exact multiGraft_nil _
    rw [h, List.map_getElem_finRange]
  -- Helper: pre_FA_B' = pre_FA_B (no FA_graft pairs).
  have hpre_FA_B' :
      ((List.finRange pre_FA_B.length).map fun k =>
        multiGraft pre_FA_B[k.val]
          (extractFAGraftPairsAt
            [(AlphaConstrainedChoice.fa_orig
                (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i v, c)] k)) =
      pre_FA_B := by
    have h : ((List.finRange pre_FA_B.length).map fun k =>
        multiGraft pre_FA_B[k.val]
          (extractFAGraftPairsAt
            [(AlphaConstrainedChoice.fa_orig
                (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i v, c)] k)) =
        (List.finRange pre_FA_B.length).map (fun k => pre_FA_B[k.val]) := by
      apply List.map_congr_left
      intro k _
      rw [extractFAGraftPairsAt_cons_fa_orig]
      exact multiGraft_nil _
    rw [h, List.map_getElem_finRange]
  -- Unfold interpret and substitute helpers.
  unfold interpret
  simp only [List.zip_cons_cons, List.zip_nil_left]
  rw [hpre_T_B', hpre_FA_B']
  -- T_orig_pairs = []; multiGraft T (choice_T.zip pre_T_B ++ []) = multiGraft T (choice_T.zip pre_T_B).
  rw [show extractTOrigPairs
        [(AlphaConstrainedChoice.fa_orig
            (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i v, c)] =
        ([] : List (Path × Planar α)) from rfl]
  rw [List.append_nil]
  congr 1
  -- F-side: per-i' modified at i' = i.
  apply List.map_congr_left
  intro i' _
  congr 1
  by_cases h : i = i'
  · -- h : i = i'. Lemma's i is query = my `i'`; lemma's i' = constructor = my `i`.
    -- Lemma's h : i' = i → my_i = my_i' = h.
    rw [extractFAOrigPairsAt_cons_fa_orig_eq (i := i') (i' := i) (v := v) (c := c)
          (rest_paired := []) (h := h)]
    rw [show extractFAOrigPairsAt
          ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α)) i' =
          ([] : List (Path × Planar α)) from rfl]
    rw [if_pos h]
    rfl
  · rw [extractFAOrigPairsAt_cons_fa_orig_neq (i := i') (i' := i) (v := v) (c := c)
          (rest_paired := []) (h := h)]
    rw [show extractFAOrigPairsAt
          ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α)) i' =
          ([] : List (Path × Planar α)) from rfl]
    rw [if_neg h]
    simp only [List.append_nil]
    rfl

/-- **FA_graft interpret reduction**: when `first_target = .fa_graft k q` and
    `C = [c]`, interpret produces:
    - T-side: `multiGraft T (choice_T.zip pre_T_B)` — no T-side changes.
    - F-side: `buildFIns F_A pre_FA_B'_kq fdata` where `pre_FA_B'_kq` modifies
      pre_FA_B at index k by `multiGraft pre_FA_B[k.val] [(q, c)]`.

    Matches the FA_graft sub-lemma's RHS structure. -/
private theorem interpret_singleton_fa_graft
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (choice_T : List Path) (fdata : List (Fin F_A.length × Path))
    (k : Fin pre_FA_B.length) (q : Path) (c : Planar α) :
    interpret T
      ({ pre_T_B_choice := choice_T
         pre_FA_B_choice := fdata
         C_targets := [AlphaConstrainedChoice.fa_graft
            (F_A := F_A) (pre_T_B := pre_T_B) k q] }
       : GraftingData F_A pre_T_B pre_FA_B) [c] =
      multiGraft T (choice_T.zip pre_T_B) ::
        buildFIns F_A
          ((List.finRange pre_FA_B.length).map fun k' =>
            if k' = k then multiGraft pre_FA_B[k.val] [(q, c)]
            else pre_FA_B[k'.val])
          fdata := by
  -- Helper: pre_T_B' = pre_T_B (no T_graft pairs).
  have hpre_T_B' :
      ((List.finRange pre_T_B.length).map fun k' =>
        multiGraft pre_T_B[k'.val]
          (extractTGraftPairsAt
            [(AlphaConstrainedChoice.fa_graft
                (F_A := F_A) (pre_T_B := pre_T_B) k q, c)] k')) =
      pre_T_B := by
    have h : ((List.finRange pre_T_B.length).map fun k' =>
        multiGraft pre_T_B[k'.val]
          (extractTGraftPairsAt
            [(AlphaConstrainedChoice.fa_graft
                (F_A := F_A) (pre_T_B := pre_T_B) k q, c)] k')) =
        (List.finRange pre_T_B.length).map (fun k' => pre_T_B[k'.val]) := by
      apply List.map_congr_left
      intro k' _
      rw [extractTGraftPairsAt_cons_fa_graft]
      exact multiGraft_nil _
    rw [h, List.map_getElem_finRange]
  -- Helper: pre_FA_B' = the if-then-else form.
  have hpre_FA_B' :
      ((List.finRange pre_FA_B.length).map fun k' =>
        multiGraft pre_FA_B[k'.val]
          (extractFAGraftPairsAt
            [(AlphaConstrainedChoice.fa_graft
                (F_A := F_A) (pre_T_B := pre_T_B) k q, c)] k')) =
      ((List.finRange pre_FA_B.length).map fun k' =>
        if k' = k then multiGraft pre_FA_B[k.val] [(q, c)]
        else pre_FA_B[k'.val]) := by
    apply List.map_congr_left
    intro k' _
    by_cases h : k' = k
    · rw [extractFAGraftPairsAt_cons_fa_graft_eq (k := k') (k' := k) (q := q) (c := c)
            (rest_paired := []) (h := h.symm)]
      rw [show extractFAGraftPairsAt
            ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α)) k' =
            ([] : List (Path × Planar α)) from rfl]
      rw [if_pos h]
      congr 2
      exact Fin.val_eq_of_eq h
    · rw [extractFAGraftPairsAt_cons_fa_graft_neq (k := k') (k' := k) (q := q) (c := c)
            (rest_paired := []) (h := Ne.symm h)]
      rw [show extractFAGraftPairsAt
            ([] : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B × Planar α)) k' =
            ([] : List (Path × Planar α)) from rfl]
      rw [if_neg h, multiGraft_nil]
  -- Unfold interpret and substitute helpers.
  unfold interpret
  simp only [List.zip_cons_cons, List.zip_nil_left]
  rw [hpre_T_B', hpre_FA_B']
  -- T_orig_pairs = []; multiGraft T (choice_T.zip pre_T_B ++ []) = multiGraft T (choice_T.zip pre_T_B).
  rw [show extractTOrigPairs
        [(AlphaConstrainedChoice.fa_graft
            (F_A := F_A) (pre_T_B := pre_T_B) k q, c)] =
        ([] : List (Path × Planar α)) from rfl]
  rw [List.append_nil]
  congr 1
  -- F-side: per-i, the inner uses the modified pre_FA_B'_kq.
  apply List.map_congr_left
  intro i _
  congr 1
  rw [show extractFAOrigPairsAt
        [(AlphaConstrainedChoice.fa_graft
            (F_A := F_A) (pre_T_B := pre_T_B) k q, c)] i =
        ([] : List (Path × Planar α)) from rfl]
  rw [List.append_nil]
  rfl

/-! ### §1.10.4 prelude: per-bucket iteratedQuadSum-leaf reductions

For the singleton `α = [b]` case, the iteratedQuadSum-leaf with
`pres = (fun t => bucketSlice [c] [b] t)` reduces to a closed form where
only the `b`-bucket has `[c]` as its accumulated guests, and all other
buckets are empty. These per-bucket reductions match the LHS forms of
the singleton sub-lemmas (§1.10.2). -/

private theorem iteratedQuadSum_singleton_T_orig
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (c : Planar α) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B
      (fun t => bucketSlice [c] [QuadIdx.T_orig] t) [] =
    (insertionForest pre_T_B ([] : List (Planar α))).bind fun pre_T_B' =>
      (insertion T (pre_T_B' ++ [c])).bind fun T' =>
        (insertionForest pre_FA_B ([] : List (Planar α))).bind fun pre_FA_B' =>
          (insertionForest F_A (pre_FA_B' ++ ([] : List (Planar α)))).map fun F' =>
            T' :: F' := by
  rw [iteratedQuadSum_nil_remaining]
  -- bucketSlice [c] [T_orig] T_graft = []; bucketSlice [c] [T_orig] T_orig = [c]; etc.
  rfl

private theorem iteratedQuadSum_singleton_T_graft
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (c : Planar α) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B
      (fun t => bucketSlice [c] [QuadIdx.T_graft] t) [] =
    (insertionForest pre_T_B [c]).bind fun pre_T_B' =>
      (insertion T (pre_T_B' ++ ([] : List (Planar α)))).bind fun T' =>
        (insertionForest pre_FA_B ([] : List (Planar α))).bind fun pre_FA_B' =>
          (insertionForest F_A (pre_FA_B' ++ ([] : List (Planar α)))).map fun F' =>
            T' :: F' := by
  rw [iteratedQuadSum_nil_remaining]
  rfl

private theorem iteratedQuadSum_singleton_FA_orig
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (c : Planar α) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B
      (fun t => bucketSlice [c] [QuadIdx.FA_orig] t) [] =
    (insertionForest pre_T_B ([] : List (Planar α))).bind fun pre_T_B' =>
      (insertion T (pre_T_B' ++ ([] : List (Planar α)))).bind fun T' =>
        (insertionForest pre_FA_B ([] : List (Planar α))).bind fun pre_FA_B' =>
          (insertionForest F_A (pre_FA_B' ++ [c])).map fun F' =>
            T' :: F' := by
  rw [iteratedQuadSum_nil_remaining]
  rfl

private theorem iteratedQuadSum_singleton_FA_graft
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (c : Planar α) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B
      (fun t => bucketSlice [c] [QuadIdx.FA_graft] t) [] =
    (insertionForest pre_T_B ([] : List (Planar α))).bind fun pre_T_B' =>
      (insertion T (pre_T_B' ++ ([] : List (Planar α)))).bind fun T' =>
        (insertionForest pre_FA_B [c]).bind fun pre_FA_B' =>
          (insertionForest F_A (pre_FA_B' ++ ([] : List (Planar α)))).map fun F' =>
            T' :: F' := by
  rw [iteratedQuadSum_nil_remaining]
  rfl

/-! ### §1.10.4: `RHS_eq_canonical_msform_singleton` — composition

The full singleton case `C = [c]` of `RHS_eq_canonical_msform`. Composes the
4 per-bucket sub-lemmas (§1.10.2) with the per-bucket interpret reductions
(§1.10.3) to bridge the LHS form (with `α : List QuadIdx` of length 1) to
the canonical form (`enumGraftingData ... 1`). -/

/-- **Singleton case** of `RHS_eq_canonical_msform`. The α-bind on the LHS
    has length 1 (single QuadIdx), so it decomposes into 4 separate cases,
    one per bucket. Each case matches the corresponding sub-lemma's LHS form,
    which equals the sub-lemma's RHS canonical form. The sub-lemma RHS
    canonical form equals the per-bucket interpret-reduced form via the
    `interpret_singleton_<bucket>` reductions. -/
private theorem RHS_eq_canonical_msform_singleton
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (c : Planar α) :
    ((Multiset.ofList (listChoices
        [QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft] 1)).bind
      fun a =>
        iteratedQuadSum T F_A pre_T_B pre_FA_B
          (fun t => bucketSlice [c] a t) []).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((enumGraftingData T F_A pre_T_B pre_FA_B 1).map
        (fun gd => interpret T gd [c])).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- ## LHS: decompose listChoices [4 buckets] 1 → 4 explicit summands
  rw [show (Multiset.ofList (listChoices
            [QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft] 1) :
            Multiset (List QuadIdx)) =
          [QuadIdx.T_orig] ::ₘ [QuadIdx.T_graft] ::ₘ [QuadIdx.FA_orig] ::ₘ [QuadIdx.FA_graft] ::ₘ 0
        from rfl]
  rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.cons_bind, Multiset.cons_bind,
      Multiset.zero_bind, add_zero]
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_add]
  -- LHS now: 4 summands
  -- (iQS T_orig).map msform + (iQS T_graft).map msform + (iQS FA_orig).map msform + (iQS FA_graft).map msform
  -- Where iQS b = iteratedQuadSum T F_A pre_T_B pre_FA_B (fun t => bucketSlice [c] [b] t) [].

  -- Reduce each iQS-leaf via the per-bucket helper lemmas (§1.10.4 prelude).
  rw [iteratedQuadSum_singleton_T_orig, iteratedQuadSum_singleton_T_graft,
      iteratedQuadSum_singleton_FA_orig, iteratedQuadSum_singleton_FA_graft]
  -- Now LHS has 4 summands matching the LHS of the 4 per-bucket sub-lemmas.
  -- Apply each sub-lemma to convert to canonical form.
  rw [show (((insertionForest pre_T_B ([] : List (Planar α))).bind fun pre_T_B' =>
              (insertion T (pre_T_B' ++ [c])).bind fun T' =>
                (insertionForest pre_FA_B ([] : List (Planar α))).bind fun pre_FA_B' =>
                  (insertionForest F_A (pre_FA_B' ++ ([] : List (Planar α)))).map fun F' =>
                    T' :: F').map (fun L => Multiset.ofList (L.map Nonplanar.mk))) =
          ((Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
            (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind fun fdata =>
              (Multiset.ofList (vertices T)).map fun v =>
                multiGraft T (choice_T.zip pre_T_B ++ [(v, c)]) ::
                  buildFIns F_A pre_FA_B fdata).map
            (fun L => Multiset.ofList (L.map Nonplanar.mk)) from
        RHS_eq_canonical_msform_singleton_T_orig T F_A pre_T_B pre_FA_B c]
  rw [show (((insertionForest pre_T_B [c]).bind fun pre_T_B' =>
              (insertion T (pre_T_B' ++ ([] : List (Planar α)))).bind fun T' =>
                (insertionForest pre_FA_B ([] : List (Planar α))).bind fun pre_FA_B' =>
                  (insertionForest F_A (pre_FA_B' ++ ([] : List (Planar α)))).map fun F' =>
                    T' :: F').map (fun L => Multiset.ofList (L.map Nonplanar.mk))) =
          ((Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
            (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind fun fdata =>
              (Multiset.ofList (List.finRange pre_T_B.length)).bind fun k =>
                (Multiset.ofList (vertices pre_T_B[k.val])).map fun q =>
                  multiGraft T (choice_T.zip ((List.finRange pre_T_B.length).map fun k' =>
                    if k' = k then multiGraft pre_T_B[k.val] [(q, c)]
                    else pre_T_B[k'.val])) ::
                    buildFIns F_A pre_FA_B fdata).map
            (fun L => Multiset.ofList (L.map Nonplanar.mk)) from
        RHS_eq_canonical_msform_singleton_T_graft T F_A pre_T_B pre_FA_B c]
  rw [show (((insertionForest pre_T_B ([] : List (Planar α))).bind fun pre_T_B' =>
              (insertion T (pre_T_B' ++ ([] : List (Planar α)))).bind fun T' =>
                (insertionForest pre_FA_B ([] : List (Planar α))).bind fun pre_FA_B' =>
                  (insertionForest F_A (pre_FA_B' ++ [c])).map fun F' =>
                    T' :: F').map (fun L => Multiset.ofList (L.map Nonplanar.mk))) =
          ((Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
            (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind fun fdata =>
              (Multiset.ofList (List.finRange F_A.length)).bind fun i =>
                (Multiset.ofList (vertices F_A[i.val])).map fun v =>
                  multiGraft T (choice_T.zip pre_T_B) ::
                    (List.finRange F_A.length).map fun i' =>
                      multiGraft F_A[i'.val]
                        (perTreePairsFromFChoice F_A pre_FA_B fdata i' ++
                         (if i = i' then [(v, c)] else []))).map
            (fun L => Multiset.ofList (L.map Nonplanar.mk)) from
        RHS_eq_canonical_msform_singleton_FA_orig T F_A pre_T_B pre_FA_B c]
  rw [show (((insertionForest pre_T_B ([] : List (Planar α))).bind fun pre_T_B' =>
              (insertion T (pre_T_B' ++ ([] : List (Planar α)))).bind fun T' =>
                (insertionForest pre_FA_B [c]).bind fun pre_FA_B' =>
                  (insertionForest F_A (pre_FA_B' ++ ([] : List (Planar α)))).map fun F' =>
                    T' :: F').map (fun L => Multiset.ofList (L.map Nonplanar.mk))) =
          ((Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
            (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind fun fdata =>
              (Multiset.ofList (List.finRange pre_FA_B.length)).bind fun k =>
                (Multiset.ofList (vertices pre_FA_B[k.val])).map fun q =>
                  multiGraft T (choice_T.zip pre_T_B) ::
                    buildFIns F_A
                      ((List.finRange pre_FA_B.length).map fun k' =>
                        if k' = k then multiGraft pre_FA_B[k.val] [(q, c)]
                        else pre_FA_B[k'.val])
                      fdata).map
            (fun L => Multiset.ofList (L.map Nonplanar.mk)) from
        RHS_eq_canonical_msform_singleton_FA_graft T F_A pre_T_B pre_FA_B c]
  -- Now LHS is the sum of 4 canonical RHS forms.

  -- ## RHS: apply enumGraftingData_succ_factored, decompose [4 buckets].
  -- Key: keep `.map msform` outside throughout; only push when handling per-bucket inner.
  rw [show (1 : Nat) = 0 + 1 from rfl, enumGraftingData_succ_factored]

  -- Reduce inner listChoices ... 0 = {[]}, simplify the map-singleton.
  -- This collapses `(listChoices ... 0).map (...)` to a singleton multiset.
  rw [show (fun choice_T : List Path =>
              (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind
                fun fdata =>
                  (([QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft] :
                      Multiset QuadIdx).bind fun first_b =>
                    (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B first_b).bind
                      fun first_target =>
                        (Multiset.ofList
                          (listChoices (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B) 0)).map
                        fun rest_targets =>
                          ({ pre_T_B_choice := choice_T
                             pre_FA_B_choice := fdata
                             C_targets := first_target :: rest_targets }
                           : GraftingData F_A pre_T_B pre_FA_B))) =
            (fun choice_T : List Path =>
              (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind
                fun fdata =>
                  (([QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft] :
                      Multiset QuadIdx).bind fun first_b =>
                    (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B first_b).map
                      fun first_target =>
                        ({ pre_T_B_choice := choice_T
                           pre_FA_B_choice := fdata
                           C_targets := [first_target] }
                         : GraftingData F_A pre_T_B pre_FA_B))) from by
        funext choice_T
        refine Multiset.bind_congr fun fdata _ => ?_
        refine Multiset.bind_congr fun first_b _ => ?_
        rw [show (Multiset.ofList
                    (listChoices (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B) 0) :
                    Multiset (List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))) =
                  ({[]} : Multiset (List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))) from by
              rw [listChoices_zero]; rfl]
        simp_rw [Multiset.map_singleton]
        rw [← Multiset.bind_singleton]]

  -- Decompose [4 buckets] inside via simp_rw with cons + bind_add.
  simp_rw [show ([QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft] :
            Multiset QuadIdx) =
          QuadIdx.T_orig ::ₘ QuadIdx.T_graft ::ₘ QuadIdx.FA_orig ::ₘ QuadIdx.FA_graft ::ₘ 0
        from rfl,
        Multiset.cons_bind, Multiset.zero_bind, add_zero, Multiset.bind_add]

  -- Push outer .map (interpret T · [c]).map msform across the additions.
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_add,
      Multiset.map_add, Multiset.map_add, Multiset.map_add]

  -- Now both sides have 4 right-associated summands:
  -- S1 + (S2 + (S3 + S4)).
  -- Apply congr 1 (3 times) — each split gives [S_i = S_i', rest = rest'].
  congr 1
  · -- T_orig case: S1 = S1'
    -- LHS: (canonical T_orig).map msform
    -- RHS: ((factored T_orig).map (interpret · [c])).map msform
    congr 1
    simp_rw [Multiset.map_bind, Multiset.map_map]
    refine Multiset.bind_congr fun choice_T _ => ?_
    refine Multiset.bind_congr fun fdata _ => ?_
    unfold enumAlphaConstrainedChoice
    dsimp only
    rw [show (Multiset.ofList ((vertices T).map (AlphaConstrainedChoice.t_orig
              (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B))) :
              Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
            (Multiset.ofList (vertices T)).map (AlphaConstrainedChoice.t_orig
              (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B)) from rfl]
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun v _ => ?_
    simp only [Function.comp_apply]
    rw [interpret_singleton_t_orig]
  · congr 1
    · -- T_graft case: S2 = S2'
      congr 1
      simp_rw [Multiset.map_bind, Multiset.map_map]
      refine Multiset.bind_congr fun choice_T _ => ?_
      refine Multiset.bind_congr fun fdata _ => ?_
      unfold enumAlphaConstrainedChoice
      dsimp only
      rw [Multiset.map_bind]
      refine Multiset.bind_congr fun k _ => ?_
      rw [show (Multiset.ofList ((vertices pre_T_B[k.val]).map (AlphaConstrainedChoice.t_graft
                (F_A := F_A) (pre_FA_B := pre_FA_B) k)) :
                Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
              (Multiset.ofList (vertices pre_T_B[k.val])).map (AlphaConstrainedChoice.t_graft
                (F_A := F_A) (pre_FA_B := pre_FA_B) k) from rfl]
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun q _ => ?_
      simp only [Function.comp_apply]
      rw [interpret_singleton_t_graft]
    · congr 1
      · -- FA_orig case: S3 = S3'
        congr 1
        simp_rw [Multiset.map_bind, Multiset.map_map]
        refine Multiset.bind_congr fun choice_T _ => ?_
        refine Multiset.bind_congr fun fdata _ => ?_
        unfold enumAlphaConstrainedChoice
        dsimp only
        rw [Multiset.map_bind]
        refine Multiset.bind_congr fun i _ => ?_
        rw [show (Multiset.ofList ((vertices F_A[i.val]).map (AlphaConstrainedChoice.fa_orig
                  (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i)) :
                  Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
                (Multiset.ofList (vertices F_A[i.val])).map (AlphaConstrainedChoice.fa_orig
                  (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i) from rfl]
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl fun v _ => ?_
        simp only [Function.comp_apply]
        rw [interpret_singleton_fa_orig]
      · -- FA_graft case: S4 = S4'
        congr 1
        simp_rw [Multiset.map_bind, Multiset.map_map]
        refine Multiset.bind_congr fun choice_T _ => ?_
        refine Multiset.bind_congr fun fdata _ => ?_
        unfold enumAlphaConstrainedChoice
        dsimp only
        rw [Multiset.map_bind]
        refine Multiset.bind_congr fun k _ => ?_
        rw [show (Multiset.ofList ((vertices pre_FA_B[k.val]).map (AlphaConstrainedChoice.fa_graft
                  (F_A := F_A) (pre_T_B := pre_T_B) k)) :
                  Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
                (Multiset.ofList (vertices pre_FA_B[k.val])).map (AlphaConstrainedChoice.fa_graft
                  (F_A := F_A) (pre_T_B := pre_T_B) k) from rfl]
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl fun q _ => ?_
        simp only [Function.comp_apply]
        rw [interpret_singleton_fa_graft]

/-! ### §1.10.5: Per-bucket interpret cons-head reductions

For the cons case `C = c :: rest` with `C_targets = first_target :: rest_targets`,
`interpret` decomposes into a "head contribution" from `(first_target, c)` plus
a "tail computation" using `(rest_targets.zip rest)`. The four lemmas below
(one per bucket) compute the head contribution explicitly, exposing the
T-side / F-side multiGraft structure with the head's `(v, c)` (or `(q, c)`)
pair injected at the appropriate position.

These generalize the `interpret_singleton_<bucket>` lemmas (§1.10.3, where
`rest_targets = []` and `rest = []`) to non-empty `rest_targets` and `rest`.
Useful for any future cons-case bridge proof of `RHS_eq_canonical_msform`. -/

/-- **T_orig interpret cons-head reduction**: when `C_targets = .t_orig v :: rest_targets`
    and `C = c :: rest`, interpret produces:
    - T-side: `multiGraft T (choice_T.zip pre_T_B'_rest ++ ((v, c) :: T_orig_rest))`
      where `pre_T_B'_rest` and `T_orig_rest` are computed from `rest_targets.zip rest`
      (no contribution from the head `.t_orig v` to `pre_T_B'`).
    - F-side: per-`i'` `multiGraft F_A[i'.val]` with pre_FA_B' and FA_orig pairs
      both computed from `rest_targets.zip rest`.

    Proof: definitional equality. The head `(.t_orig v, c)` matches T_orig
    extractor (gives `(v, c)` prepended) and gives `none` for T_graft, FA_orig,
    FA_graft extractors (constructor mismatch). All extractor reductions are
    `rfl`-equal via the `extract*_cons_t_orig` simp lemmas. -/
private theorem interpret_cons_t_orig
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (choice_T : List Path) (fdata : List (Fin F_A.length × Path))
    (v : Path) (rest_targets : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
    (c : Planar α) (rest : List (Planar α)) :
    interpret T
      ({ pre_T_B_choice := choice_T
         pre_FA_B_choice := fdata
         C_targets := AlphaConstrainedChoice.t_orig v
            (F_A := F_A) (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) :: rest_targets }
       : GraftingData F_A pre_T_B pre_FA_B) (c :: rest) =
    multiGraft T
      (choice_T.zip
        ((List.finRange pre_T_B.length).map fun k =>
          multiGraft pre_T_B[k.val] (extractTGraftPairsAt (rest_targets.zip rest) k)) ++
       ((v, c) :: extractTOrigPairs (rest_targets.zip rest))) ::
    (List.finRange F_A.length).map fun i =>
      multiGraft F_A[i.val]
        ((fdata.zip
          ((List.finRange pre_FA_B.length).map fun k =>
            multiGraft pre_FA_B[k.val] (extractFAGraftPairsAt (rest_targets.zip rest) k))).filterMap
          (fun p => if p.fst.fst = i then some (p.fst.snd, p.snd) else none) ++
         extractFAOrigPairsAt (rest_targets.zip rest) i) := rfl

/-- **T_graft interpret cons-head reduction**: when `C_targets = .t_graft k q :: rest_targets`
    and `C = c :: rest`, interpret produces:
    - T-side: `multiGraft T (choice_T.zip pre_T_B'_kq_rest)` where
      `pre_T_B'_kq_rest[k']` modifies pre_T_B[k.val] by `multiGraft pre_T_B[k.val]
      ((q, c) :: extractTGraftPairsAt(rest_targets.zip rest) k)` and other indices
      use `extractTGraftPairsAt(rest_targets.zip rest)`.
    - T-side T_orig pairs: `extractTOrigPairs(rest_targets.zip rest)` (no
      contribution from `.t_graft k q`).
    - F-side: same as for `(rest_targets, rest)` (no F-side contribution).

    Proof: definitional reduction via `extract*_cons_t_graft_*` lemmas.
    The k = k' case requires explicit `if_pos`. -/
private theorem interpret_cons_t_graft
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (choice_T : List Path) (fdata : List (Fin F_A.length × Path))
    (k : Fin pre_T_B.length) (q : Path)
    (rest_targets : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
    (c : Planar α) (rest : List (Planar α)) :
    interpret T
      ({ pre_T_B_choice := choice_T
         pre_FA_B_choice := fdata
         C_targets := AlphaConstrainedChoice.t_graft
            (F_A := F_A) (pre_FA_B := pre_FA_B) k q :: rest_targets }
       : GraftingData F_A pre_T_B pre_FA_B) (c :: rest) =
    multiGraft T
      (choice_T.zip
        ((List.finRange pre_T_B.length).map fun k' =>
          if k' = k then
            multiGraft pre_T_B[k.val]
              ((q, c) :: extractTGraftPairsAt (rest_targets.zip rest) k')
          else
            multiGraft pre_T_B[k'.val]
              (extractTGraftPairsAt (rest_targets.zip rest) k')) ++
       extractTOrigPairs (rest_targets.zip rest)) ::
    (List.finRange F_A.length).map fun i =>
      multiGraft F_A[i.val]
        ((fdata.zip
          ((List.finRange pre_FA_B.length).map fun k' =>
            multiGraft pre_FA_B[k'.val]
              (extractFAGraftPairsAt (rest_targets.zip rest) k'))).filterMap
          (fun p => if p.fst.fst = i then some (p.fst.snd, p.snd) else none) ++
         extractFAOrigPairsAt (rest_targets.zip rest) i) := by
  unfold interpret
  simp only [List.zip_cons_cons]
  -- Peel: outer T' :: F'.
  congr 1
  · -- T-side: multiGraft T (...) = multiGraft T (...)
    congr 1  -- multiGraft T _
    -- Goal: choice_T.zip pre_T_B'_LHS ++ extractTOrigPairs ... = choice_T.zip pre_T_B'_RHS ++ extractTOrig...
    -- The extractTOrigPairs of both sides is equal (extractTOrigPairs ((.t_graft k q, c) :: ...) =
    --   extractTOrigPairs ...) via extractTOrigPairs_cons_t_graft (rfl simp lemma).
    -- Use `simp only` with the simp lemma to reduce the LHS extractor.
    simp only [extractTOrigPairs_cons_t_graft]
    congr 1  -- _ ++ extractTOrig (now equal on both sides)
    -- Goal: choice_T.zip pre_T_B'_LHS = choice_T.zip pre_T_B'_RHS
    congr 1  -- choice_T.zip _
    -- Goal: pre_T_B'_LHS = pre_T_B'_RHS (both are .map over finRange)
    apply List.map_congr_left
    intro k' _
    by_cases h : k' = k
    · rw [extractTGraftPairsAt_cons_t_graft_eq (k := k') (k' := k) (q := q) (c := c)
            (rest_paired := rest_targets.zip rest) (h := h.symm)]
      rw [if_pos h]
      congr 2
      exact Fin.val_eq_of_eq h
    · rw [extractTGraftPairsAt_cons_t_graft_neq (k := k') (k' := k) (q := q) (c := c)
            (rest_paired := rest_targets.zip rest) (h := Ne.symm h)]
      rw [if_neg h]

/-- **FA_orig interpret cons-head reduction**: when `C_targets = .fa_orig i v :: rest_targets`
    and `C = c :: rest`, interpret produces:
    - T-side: same as for `(rest_targets, rest)` (no T-side contribution).
    - F-side: per-`i'`, the `multiGraft F_A[i'.val]` includes `(v, c)` as an
      additional FA_orig pair when `i' = i`.

    Proof: definitional reduction via `extract*_cons_fa_orig_*` lemmas. -/
private theorem interpret_cons_fa_orig
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (choice_T : List Path) (fdata : List (Fin F_A.length × Path))
    (i : Fin F_A.length) (v : Path)
    (rest_targets : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
    (c : Planar α) (rest : List (Planar α)) :
    interpret T
      ({ pre_T_B_choice := choice_T
         pre_FA_B_choice := fdata
         C_targets := AlphaConstrainedChoice.fa_orig
            (pre_T_B := pre_T_B) (pre_FA_B := pre_FA_B) i v :: rest_targets }
       : GraftingData F_A pre_T_B pre_FA_B) (c :: rest) =
    multiGraft T
      (choice_T.zip
        ((List.finRange pre_T_B.length).map fun k =>
          multiGraft pre_T_B[k.val] (extractTGraftPairsAt (rest_targets.zip rest) k)) ++
       extractTOrigPairs (rest_targets.zip rest)) ::
    (List.finRange F_A.length).map fun i' =>
      multiGraft F_A[i'.val]
        ((fdata.zip
          ((List.finRange pre_FA_B.length).map fun k =>
            multiGraft pre_FA_B[k.val] (extractFAGraftPairsAt (rest_targets.zip rest) k))).filterMap
          (fun p => if p.fst.fst = i' then some (p.fst.snd, p.snd) else none) ++
         (if i = i' then (v, c) :: extractFAOrigPairsAt (rest_targets.zip rest) i'
          else extractFAOrigPairsAt (rest_targets.zip rest) i')) := by
  unfold interpret
  simp only [List.zip_cons_cons]
  congr 1
  -- F-side: per-i' case on i = i'.
  apply List.map_congr_left
  intro i' _
  congr 1
  congr 1
  by_cases h : i = i'
  · rw [extractFAOrigPairsAt_cons_fa_orig_eq (i := i') (i' := i) (v := v) (c := c)
          (rest_paired := rest_targets.zip rest) (h := h)]
    rw [if_pos h]
  · rw [extractFAOrigPairsAt_cons_fa_orig_neq (i := i') (i' := i) (v := v) (c := c)
          (rest_paired := rest_targets.zip rest) (h := h)]
    rw [if_neg h]

/-- **FA_graft interpret cons-head reduction**: when `C_targets = .fa_graft k q :: rest_targets`
    and `C = c :: rest`, interpret produces:
    - T-side: same as for `(rest_targets, rest)` (no T-side contribution).
    - F-side: per-i', includes `pre_FA_B'_kq_rest` where `pre_FA_B'_kq_rest[k']`
      modifies pre_FA_B[k.val] by adding `(q, c)` to its FA_graft pairs.

    Proof: definitional reduction via `extract*_cons_fa_graft_*` lemmas.
    The k = k' case requires explicit `if_pos`. -/
private theorem interpret_cons_fa_graft
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (choice_T : List Path) (fdata : List (Fin F_A.length × Path))
    (k : Fin pre_FA_B.length) (q : Path)
    (rest_targets : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
    (c : Planar α) (rest : List (Planar α)) :
    interpret T
      ({ pre_T_B_choice := choice_T
         pre_FA_B_choice := fdata
         C_targets := AlphaConstrainedChoice.fa_graft
            (F_A := F_A) (pre_T_B := pre_T_B) k q :: rest_targets }
       : GraftingData F_A pre_T_B pre_FA_B) (c :: rest) =
    multiGraft T
      (choice_T.zip
        ((List.finRange pre_T_B.length).map fun k' =>
          multiGraft pre_T_B[k'.val] (extractTGraftPairsAt (rest_targets.zip rest) k')) ++
       extractTOrigPairs (rest_targets.zip rest)) ::
    (List.finRange F_A.length).map fun i =>
      multiGraft F_A[i.val]
        ((fdata.zip
          ((List.finRange pre_FA_B.length).map fun k' =>
            if k' = k then
              multiGraft pre_FA_B[k.val]
                ((q, c) :: extractFAGraftPairsAt (rest_targets.zip rest) k')
            else
              multiGraft pre_FA_B[k'.val]
                (extractFAGraftPairsAt (rest_targets.zip rest) k'))).filterMap
          (fun p => if p.fst.fst = i then some (p.fst.snd, p.snd) else none) ++
         extractFAOrigPairsAt (rest_targets.zip rest) i) := by
  unfold interpret
  -- All T-side extractors reduce rfl via cons_fa_graft simp lemmas.
  -- F-side FA_graft needs case analysis on k = k'.
  simp only [List.zip_cons_cons,
             extractTOrigPairs_cons_fa_graft, extractTGraftPairsAt_cons_fa_graft,
             extractFAOrigPairsAt_cons_fa_graft]
  -- Goal: T' :: F' = T'_RHS :: F'_RHS; T-side is rfl-equal post simp.
  refine congr_arg₂ _ rfl ?_
  -- F-side .map equality: peel per-i, then per-multiGraft, then per-++, then per-filterMap,
  -- then per-fdata.zip, finally to the .map equality and per-k' case analysis.
  refine List.map_congr_left fun i _ => ?_
  -- multiGraft F_A[i.val] (lhs ++ rhs) = multiGraft F_A[i.val] (lhs' ++ rhs)
  congr 1  -- peels multiGraft → arg list equality
  congr 1  -- peels ++ → first arg equality (extractFAOrig already equal post simp)
  congr 1  -- peels filterMap → list equality (filter fn already equal)
  congr 1  -- peels fdata.zip → second arg equality (fdata already equal)
  -- Now: LHS .map = RHS .map
  refine List.map_congr_left fun k' _ => ?_
  by_cases h : k' = k
  · rw [extractFAGraftPairsAt_cons_fa_graft_eq (k := k') (k' := k) (q := q) (c := c)
          (rest_paired := rest_targets.zip rest) (h := h.symm)]
    rw [if_pos h]
    congr 2
    exact Fin.val_eq_of_eq h
  · rw [extractFAGraftPairsAt_cons_fa_graft_neq (k := k') (k' := k) (q := q) (c := c)
          (rest_paired := rest_targets.zip rest) (h := Ne.symm h)]
    rw [if_neg h]

/-! ### §1.10.6: Per-bucket iteratedQuadSum-leaf cons-head reductions

For each `first_b ∈ {T_orig, T_graft, FA_orig, FA_graft}`, the
`iteratedQuadSum`-leaf with `pres = (fun t => bucketSlice (c :: rest) (first_b :: rest_α) t)`
reduces to a closed form where the first_b bucket has `[c]` prepended to its
`bucketSlice rest rest_α first_b` value, and other buckets have `bucketSlice
rest rest_α` directly. These generalize `iteratedQuadSum_singleton_<bucket>`
(§1.10.4 prelude, where rest_α = [] and rest = []) to non-empty rest.

Useful for any future cons-case bridge proof; pairs with the
`interpret_cons_<bucket>` lemmas in §1.10.5 to align the LHS iQS-leaf with
the RHS interpret form per first_b. -/

private theorem iteratedQuadSum_cons_T_orig_first
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (c : Planar α) (rest : List (Planar α)) (rest_α : List QuadIdx) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B
      (fun t => bucketSlice (c :: rest) (QuadIdx.T_orig :: rest_α) t) [] =
    (insertionForest pre_T_B (bucketSlice rest rest_α QuadIdx.T_graft)).bind fun pre_T_B' =>
      (insertion T (pre_T_B' ++ ([c] ++ bucketSlice rest rest_α QuadIdx.T_orig))).bind fun T' =>
        (insertionForest pre_FA_B (bucketSlice rest rest_α QuadIdx.FA_graft)).bind fun pre_FA_B' =>
          (insertionForest F_A (pre_FA_B' ++ bucketSlice rest rest_α QuadIdx.FA_orig)).map fun F' =>
            T' :: F' := by
  rw [iteratedQuadSum_nil_remaining]
  simp only [bucketSlice_cons_cons, List.nil_append, ite_self,
             if_pos (rfl : QuadIdx.T_orig = QuadIdx.T_orig),
             if_neg (by decide : QuadIdx.T_orig ≠ QuadIdx.T_graft),
             if_neg (by decide : QuadIdx.T_orig ≠ QuadIdx.FA_orig),
             if_neg (by decide : QuadIdx.T_orig ≠ QuadIdx.FA_graft),
             if_true]

private theorem iteratedQuadSum_cons_T_graft_first
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (c : Planar α) (rest : List (Planar α)) (rest_α : List QuadIdx) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B
      (fun t => bucketSlice (c :: rest) (QuadIdx.T_graft :: rest_α) t) [] =
    (insertionForest pre_T_B ([c] ++ bucketSlice rest rest_α QuadIdx.T_graft)).bind fun pre_T_B' =>
      (insertion T (pre_T_B' ++ bucketSlice rest rest_α QuadIdx.T_orig)).bind fun T' =>
        (insertionForest pre_FA_B (bucketSlice rest rest_α QuadIdx.FA_graft)).bind fun pre_FA_B' =>
          (insertionForest F_A (pre_FA_B' ++ bucketSlice rest rest_α QuadIdx.FA_orig)).map fun F' =>
            T' :: F' := by
  rw [iteratedQuadSum_nil_remaining]
  simp only [bucketSlice_cons_cons, List.nil_append, ite_self,
             if_pos (rfl : QuadIdx.T_graft = QuadIdx.T_graft),
             if_neg (by decide : QuadIdx.T_graft ≠ QuadIdx.T_orig),
             if_neg (by decide : QuadIdx.T_graft ≠ QuadIdx.FA_orig),
             if_neg (by decide : QuadIdx.T_graft ≠ QuadIdx.FA_graft),
             if_true]

private theorem iteratedQuadSum_cons_FA_orig_first
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (c : Planar α) (rest : List (Planar α)) (rest_α : List QuadIdx) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B
      (fun t => bucketSlice (c :: rest) (QuadIdx.FA_orig :: rest_α) t) [] =
    (insertionForest pre_T_B (bucketSlice rest rest_α QuadIdx.T_graft)).bind fun pre_T_B' =>
      (insertion T (pre_T_B' ++ bucketSlice rest rest_α QuadIdx.T_orig)).bind fun T' =>
        (insertionForest pre_FA_B (bucketSlice rest rest_α QuadIdx.FA_graft)).bind fun pre_FA_B' =>
          (insertionForest F_A (pre_FA_B' ++ ([c] ++ bucketSlice rest rest_α QuadIdx.FA_orig))).map
            fun F' => T' :: F' := by
  rw [iteratedQuadSum_nil_remaining]
  simp only [bucketSlice_cons_cons, List.nil_append, ite_self,
             if_pos (rfl : QuadIdx.FA_orig = QuadIdx.FA_orig),
             if_neg (by decide : QuadIdx.FA_orig ≠ QuadIdx.T_orig),
             if_neg (by decide : QuadIdx.FA_orig ≠ QuadIdx.T_graft),
             if_neg (by decide : QuadIdx.FA_orig ≠ QuadIdx.FA_graft),
             if_true]

private theorem iteratedQuadSum_cons_FA_graft_first
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (c : Planar α) (rest : List (Planar α)) (rest_α : List QuadIdx) :
    iteratedQuadSum T F_A pre_T_B pre_FA_B
      (fun t => bucketSlice (c :: rest) (QuadIdx.FA_graft :: rest_α) t) [] =
    (insertionForest pre_T_B (bucketSlice rest rest_α QuadIdx.T_graft)).bind fun pre_T_B' =>
      (insertion T (pre_T_B' ++ bucketSlice rest rest_α QuadIdx.T_orig)).bind fun T' =>
        (insertionForest pre_FA_B ([c] ++ bucketSlice rest rest_α QuadIdx.FA_graft)).bind
          fun pre_FA_B' =>
            (insertionForest F_A (pre_FA_B' ++ bucketSlice rest rest_α QuadIdx.FA_orig)).map
              fun F' => T' :: F' := by
  rw [iteratedQuadSum_nil_remaining]
  simp only [bucketSlice_cons_cons, List.nil_append, ite_self,
             if_pos (rfl : QuadIdx.FA_graft = QuadIdx.FA_graft),
             if_neg (by decide : QuadIdx.FA_graft ≠ QuadIdx.T_orig),
             if_neg (by decide : QuadIdx.FA_graft ≠ QuadIdx.T_graft),
             if_neg (by decide : QuadIdx.FA_graft ≠ QuadIdx.FA_orig),
             if_true]

/-! ### §1.10.6.5: Insertion-split-middle-pair substrate

Bridges `(insertion T (X ++ [c] ++ Y)).bind Q` to a 3-level bind structure
where the middle vertex choice `v` is exposed. Used by per-bucket cons
sub-lemmas to extract the head c-graft as a `(v, c)` pair. -/

private theorem insertion_split_middle_pair_bind {γ : Type*}
    (T : Planar α) (X Y : List (Planar α)) (c : Planar α)
    (Q : Planar α → Multiset γ) :
    (insertion T (X ++ ([c] ++ Y))).bind Q =
    (Multiset.ofList (listChoices (vertices T) X.length)).bind fun cX =>
      (Multiset.ofList (vertices T)).bind fun v =>
        (Multiset.ofList (listChoices (vertices T) Y.length)).bind fun cY =>
          Q (multiGraft T (cX.zip X ++ [(v, c)] ++ cY.zip Y)) := by
  rw [insertion_def]
  rw [show (X ++ ([c] ++ Y)).length = X.length + (1 + Y.length) from by
        rw [List.length_append, List.length_append, List.length_singleton]]
  rw [← Multiset.map_coe, Multiset.bind_map]
  -- Apply listChoices_split_bind: total = X.length + (1 + Y.length).
  rw [listChoices_split_bind (vertices T) X.length (1 + Y.length)]
  refine Multiset.bind_congr fun cX hcX => ?_
  rw [Multiset.mem_coe] at hcX
  have hX_len : cX.length = X.length := mem_listChoices_length _ _ _ hcX
  -- Inner: split (1 + Y.length).
  rw [listChoices_split_bind (vertices T) 1 Y.length]
  -- Reduce listChoices V(T) 1 to (ofList V(T)).bind v => {[v]}-form.
  rw [show (Multiset.ofList (listChoices (vertices T) 1) : Multiset (List Path)) =
        ↑((vertices T).flatMap (fun v => [[v]])) from by
      rw [show listChoices (vertices T) 1 =
              (vertices T).flatMap (fun v => (listChoices (vertices T) 0).map (v :: ·))
            from rfl, listChoices_zero]
      rfl]
  rw [show (↑((vertices T).flatMap (fun v => [[v]])) : Multiset (List Path)) =
        (Multiset.ofList (vertices T)).bind (fun v => ({[v]} : Multiset (List Path))) from by
      rw [← Multiset.coe_bind]; rfl]
  simp only [Multiset.bind_assoc, Multiset.singleton_bind]
  refine Multiset.bind_congr fun v _ => ?_
  refine Multiset.bind_congr fun cY hcY => ?_
  rw [Multiset.mem_coe] at hcY
  have hY_len : cY.length = Y.length := mem_listChoices_length _ _ _ hcY
  -- Goal: Q (multiGraft T ((cX ++ ([v] ++ cY)).zip (X ++ ([c] ++ Y))))
  --     = Q (multiGraft T (cX.zip X ++ [(v, c)] ++ cY.zip Y))
  congr 2
  rw [List.zip_append hX_len]
  -- LHS now: cX.zip X ++ ([v] ++ cY).zip ([c] ++ Y)
  -- RHS: cX.zip X ++ [(v, c)] ++ cY.zip Y (left-grouped)
  -- Normalize RHS associativity to right-grouped via List.append_assoc.
  rw [List.append_assoc (cX.zip X) [(v, c)] (cY.zip Y)]
  -- Now: cX.zip X ++ ([v] ++ cY).zip ([c] ++ Y) = cX.zip X ++ ([(v, c)] ++ cY.zip Y)
  -- Both sides are definitionally equal at this point; congr 1 closes via rfl.
  congr 1

/-! ### §1.11: Strong-IH substrate — augmented grafting data with `pres`

To prove the cons case of `RHS_eq_canonical_msform`, the standard IH bridges
`LHS-rest = RHS-rest` at msform level — but the per-bucket cons sub-lemmas need
the equality to hold AFTER injecting `(v_first, c)` into `multiGraft T`'s pair
list. This injection isn't a function of the msform output (msform
`= Multiset.ofList ∘ List.map Nonplanar.mk` loses the pair-list structure).

The strong-IH bypasses this by parameterizing the canonical form over
`pres : QuadIdx → List (Planar α)`, so the IH can be applied with augmented
pres and the result tracks the additional graft pairs explicitly.

`AugGraftingData F_A pre_T_B pre_FA_B pres` extends the standard `GraftingData`
with one choice list per pres bucket:

| Bucket   | Field                     | Element type                  | Length                    |
|----------|---------------------------|-------------------------------|---------------------------|
| T_orig   | `pres_T_orig_choice`      | `Path`                        | `(pres .T_orig).length`   |
| T_graft  | `pres_T_graft_choice`     | `Fin pre_T_B.length × Path`   | `(pres .T_graft).length`  |
| FA_orig  | `pres_FA_orig_choice`     | `Fin F_A.length × Path`       | `(pres .FA_orig).length`  |
| FA_graft | `pres_FA_graft_choice`    | `Fin pre_FA_B.length × Path`  | `(pres .FA_graft).length` |

`augInterpret` is the analog of `interpret` extended with these pres pairs:
each pres entry contributes a graft pair PRE-PENDED to the corresponding
bucket's pair list (pres pairs first, C-derived pairs second). At
`pres = (fun _ => [])` the four `pres_*_choice` fields are `[]`, making
`augInterpret` reduce to `interpret` (modulo Multiset structure).

`enumAugGraftingData` enumerates all valid `AugGraftingData` whose four
`pres_*_choice` lists have the matching lengths. -/

/-- Canonical labeled grafting data, augmented with per-pres-element vertex
    choices. Generalizes `GraftingData` by adding 4 more choice lists, one per
    pres bucket. The standard `GraftingData` is the specialization at
    `pres = (fun _ => [])`. -/
private structure AugGraftingData (F_A pre_T_B pre_FA_B : List (Planar α))
    (pres : QuadIdx → List (Planar α)) where
  /-- Per-pre_T_B[k] graft position in V(T). Expected length `pre_T_B.length`. -/
  pre_T_B_choice  : List Path
  /-- Per-pre_FA_B[k] graft position: which F_A tree + vertex within.
      Expected length `pre_FA_B.length`. -/
  pre_FA_B_choice : List (Fin F_A.length × Path)
  /-- Per-c bucket-classified target. Expected length matches consumer's `C.length`. -/
  C_targets       : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)
  /-- Per-(pres .T_orig)[i] graft position in V(T).
      Expected length `(pres .T_orig).length`. -/
  pres_T_orig_choice  : List Path
  /-- Per-(pres .T_graft)[i] graft position: which pre_T_B tree + vertex within.
      Expected length `(pres .T_graft).length`. -/
  pres_T_graft_choice : List (Fin pre_T_B.length × Path)
  /-- Per-(pres .FA_orig)[i] graft position: which F_A tree + vertex within.
      Expected length `(pres .FA_orig).length`. -/
  pres_FA_orig_choice : List (Fin F_A.length × Path)
  /-- Per-(pres .FA_graft)[i] graft position: which pre_FA_B tree + vertex within.
      Expected length `(pres .FA_graft).length`. -/
  pres_FA_graft_choice : List (Fin pre_FA_B.length × Path)

/-! ### §1.11.1: `augInterpret` — single-pass grafting with `pres` -/

/-- Single-pass interpretation of `AugGraftingData` plus `C` into the resulting
    forest. Like `interpret` but with the per-bucket pair lists augmented by
    pres-derived pairs (pres pairs FIRST, then C-derived pairs).

    Specifically, for each bucket b, the augmented pair list is
    `pres-pairs-at-b ++ C-pairs-at-b`. The pres-pairs come from zipping
    `agd.pres_b_choice` with `pres b`; the C-pairs come from `extract_b
    (agd.C_targets.zip C)` as in standard `interpret`. -/
private def augInterpret
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    {pres : QuadIdx → List (Planar α)}
    (agd : AugGraftingData F_A pre_T_B pre_FA_B pres)
    (C : List (Planar α)) : List (Planar α) :=
  let C_paired := agd.C_targets.zip C
  let pres_T_orig_pairs : List (Path × Planar α) :=
    agd.pres_T_orig_choice.zip (pres .T_orig)
  let pres_T_graft_pairs_at (k : Fin pre_T_B.length) : List (Path × Planar α) :=
    (agd.pres_T_graft_choice.zip (pres .T_graft)).filterMap fun p =>
      if p.fst.fst = k then some (p.fst.snd, p.snd) else none
  let pres_FA_orig_pairs_at (i : Fin F_A.length) : List (Path × Planar α) :=
    (agd.pres_FA_orig_choice.zip (pres .FA_orig)).filterMap fun p =>
      if p.fst.fst = i then some (p.fst.snd, p.snd) else none
  let pres_FA_graft_pairs_at (k : Fin pre_FA_B.length) : List (Path × Planar α) :=
    (agd.pres_FA_graft_choice.zip (pres .FA_graft)).filterMap fun p =>
      if p.fst.fst = k then some (p.fst.snd, p.snd) else none
  let pre_T_B' : List (Planar α) :=
    (List.finRange pre_T_B.length).map fun k =>
      multiGraft pre_T_B[k.val]
        (pres_T_graft_pairs_at k ++ extractTGraftPairsAt C_paired k)
  let T' : Planar α :=
    multiGraft T (agd.pre_T_B_choice.zip pre_T_B' ++
                  pres_T_orig_pairs ++ extractTOrigPairs C_paired)
  let pre_FA_B' : List (Planar α) :=
    (List.finRange pre_FA_B.length).map fun k =>
      multiGraft pre_FA_B[k.val]
        (pres_FA_graft_pairs_at k ++ extractFAGraftPairsAt C_paired k)
  let F' : List (Planar α) :=
    (List.finRange F_A.length).map fun i =>
      let pre_FA_B'_for_i : List (Path × Planar α) :=
        (agd.pre_FA_B_choice.zip pre_FA_B').filterMap fun p =>
          if p.fst.fst = i then some (p.fst.snd, p.snd) else none
      multiGraft F_A[i.val]
        (pre_FA_B'_for_i ++ pres_FA_orig_pairs_at i ++
         extractFAOrigPairsAt C_paired i)
  T' :: F'

/-! ### §1.11.2: `enumAugGraftingData` — canonical enumeration -/

/-- Multiset of all valid `AugGraftingData` for given `T`, `F_A`, `pre_T_B`,
    `pre_FA_B`, `pres`, and target `C_length`.

    Each entry has:
    - `pre_T_B_choice.length = pre_T_B.length`
    - `pre_FA_B_choice.length = pre_FA_B.length`
    - `C_targets.length = C_length`
    - `pres_T_orig_choice.length = (pres .T_orig).length`
    - `pres_T_graft_choice.length = (pres .T_graft).length`
    - `pres_FA_orig_choice.length = (pres .FA_orig).length`
    - `pres_FA_graft_choice.length = (pres .FA_graft).length`

    These length invariants follow from `listChoices`'s length lemma at
    consumption sites. -/
private def enumAugGraftingData
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (pres : QuadIdx → List (Planar α))
    (C_length : Nat) : Multiset (AugGraftingData F_A pre_T_B pre_FA_B pres) :=
  Multiset.ofList <|
    (listChoices (vertices T) pre_T_B.length).flatMap fun choice_T =>
      (listChoices (perKFChoice F_A) pre_FA_B.length).flatMap fun fdata =>
        (listChoices
            (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B) C_length).flatMap
          fun targets =>
            (listChoices (vertices T) (pres .T_orig).length).flatMap fun pTO =>
              (listChoices (perKFChoice pre_T_B) (pres .T_graft).length).flatMap
                fun pTG =>
                  (listChoices (perKFChoice F_A) (pres .FA_orig).length).flatMap
                    fun pFO =>
                      (listChoices
                        (perKFChoice pre_FA_B) (pres .FA_graft).length).map
                        fun pFG =>
                          { pre_T_B_choice := choice_T
                            pre_FA_B_choice := fdata
                            C_targets := targets
                            pres_T_orig_choice := pTO
                            pres_T_graft_choice := pTG
                            pres_FA_orig_choice := pFO
                            pres_FA_graft_choice := pFG }

/-! ### §1.11.3: F-side append substrate (multi-element generalization)

`buildFIns F_A (X ++ Y) (xdata ++ ydata)` decomposes as the per-`i'` sum of the
per-tree pairs from `(X, xdata)` and `(Y, ydata)`. Generalization of
`buildFIns_append_singleton` (§1.10.1.1) to non-singleton appends. -/

/-- `perTreePairsFromFChoice` distributes over append on the data and pre_FA_B
    sides, when the data lengths match the pre_FA_B halves. Multi-element
    generalization of `perTreePairsFromFChoice_append_singleton`. -/
private theorem perTreePairsFromFChoice_append
    (F_A X Y : List (Planar α))
    (xdata : List (Fin F_A.length × Path)) (ydata : List (Fin F_A.length × Path))
    (hxdata : xdata.length = X.length) (i' : Fin F_A.length) :
    perTreePairsFromFChoice F_A (X ++ Y) (xdata ++ ydata) i' =
      perTreePairsFromFChoice F_A X xdata i' ++
      perTreePairsFromFChoice F_A Y ydata i' := by
  unfold perTreePairsFromFChoice
  rw [List.zip_append hxdata, List.filterMap_append]

/-- `buildFIns` distributes over append on the data and pre_FA_B sides, when
    the data lengths match the pre_FA_B halves. Multi-element generalization of
    `buildFIns_append_singleton`. -/
private theorem buildFIns_append
    (F_A X Y : List (Planar α))
    (xdata : List (Fin F_A.length × Path)) (ydata : List (Fin F_A.length × Path))
    (hxdata : xdata.length = X.length) :
    buildFIns F_A (X ++ Y) (xdata ++ ydata) =
      (List.finRange F_A.length).map fun i' =>
        multiGraft F_A[i'.val]
          (perTreePairsFromFChoice F_A X xdata i' ++
           perTreePairsFromFChoice F_A Y ydata i') := by
  unfold buildFIns
  refine List.map_congr_left fun i' _ => ?_
  rw [perTreePairsFromFChoice_append F_A X Y xdata ydata hxdata i']

/-! ### §1.11.4: `augInterpret_C_nil` — C = [] reduction

When `C = []`, `augInterpret` reduces to a pres-only computation: each pres
bucket's pairs are zipped/filterMapped from the corresponding `pres_*_choice`
field, with no contribution from `extract*_pairs` (which all reduce to `[]`
on empty `C_paired`). The closed form mirrors the iterated-grafting LHS:
- T-side: `multiGraft T (pre_T_B_choice.zip pre_T_B' ++ pres_T_orig_pairs)`
  where `pre_T_B'[k] = multiGraft pre_T_B[k] pres_T_graft_pairs_at k`.
- F-side: per-`i'`, `multiGraft F_A[i'] (perTree pre_FA_B' i' ++ pres_FA_orig_pairs_at i')`.
-/

/-- Reducing `augInterpret T agd []` (the C = []) case to a closed form.

    The T-side becomes `multiGraft T (pre_T_B_choice.zip pre_T_B' ++ pres_T_orig_pairs)`
    where `pre_T_B'[k] = multiGraft pre_T_B[k] (pres_T_graft_pairs_at k)`.
    The F-side becomes per-`i'` multiGraft of `F_A[i'.val]` with the
    `pre_FA_B'`-derived pairs and `pres_FA_orig_pairs_at i'` appended. -/
private theorem augInterpret_C_nil
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    {pres : QuadIdx → List (Planar α)}
    (agd : AugGraftingData F_A pre_T_B pre_FA_B pres) :
    augInterpret T agd ([] : List (Planar α)) =
      multiGraft T
        (agd.pre_T_B_choice.zip
          ((List.finRange pre_T_B.length).map fun k =>
            multiGraft pre_T_B[k.val]
              ((agd.pres_T_graft_choice.zip (pres .T_graft)).filterMap fun p =>
                if p.fst.fst = k then some (p.fst.snd, p.snd) else none)) ++
         agd.pres_T_orig_choice.zip (pres .T_orig)) ::
      (List.finRange F_A.length).map fun i =>
        multiGraft F_A[i.val]
          ((agd.pre_FA_B_choice.zip
              ((List.finRange pre_FA_B.length).map fun k =>
                multiGraft pre_FA_B[k.val]
                  ((agd.pres_FA_graft_choice.zip (pres .FA_graft)).filterMap fun p =>
                    if p.fst.fst = k then some (p.fst.snd, p.snd) else none))).filterMap
            (fun p => if p.fst.fst = i then some (p.fst.snd, p.snd) else none) ++
           (agd.pres_FA_orig_choice.zip (pres .FA_orig)).filterMap fun p =>
              if p.fst.fst = i then some (p.fst.snd, p.snd) else none) := by
  -- Unfold augInterpret and reduce the C-paired zips to nil.
  simp only [augInterpret,
             show agd.C_targets.zip ([] : List (Planar α)) = [] from
               List.zip_nil_right (l := agd.C_targets),
             extractTOrigPairs, extractTGraftPairsAt,
             extractFAOrigPairsAt, extractFAGraftPairsAt,
             List.filterMap_nil, List.append_nil]

/-! ### §1.11.5: `enumAugGraftingData_zero` — C_length = 0 collapse -/

/-- The C_length = 0 specialization of `enumAugGraftingData`: the C_targets
    enumeration `listChoices _ 0 = [[]]` collapses, leaving a flat enumeration
    over the 6 remaining choice lists with `C_targets = []`. -/
private theorem enumAugGraftingData_zero
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (pres : QuadIdx → List (Planar α)) :
    enumAugGraftingData T F_A pre_T_B pre_FA_B pres 0 =
      (Multiset.ofList
        ((listChoices (vertices T) pre_T_B.length).flatMap fun choice_T =>
          (listChoices (perKFChoice F_A) pre_FA_B.length).flatMap fun fdata =>
            (listChoices (vertices T) (pres .T_orig).length).flatMap fun pTO =>
              (listChoices (perKFChoice pre_T_B) (pres .T_graft).length).flatMap
                fun pTG =>
                  (listChoices (perKFChoice F_A) (pres .FA_orig).length).flatMap
                    fun pFO =>
                      (listChoices
                        (perKFChoice pre_FA_B) (pres .FA_graft).length).map
                        fun pFG =>
                          ({ pre_T_B_choice := choice_T
                             pre_FA_B_choice := fdata
                             C_targets := ([] :
                               List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
                             pres_T_orig_choice := pTO
                             pres_T_graft_choice := pTG
                             pres_FA_orig_choice := pFO
                             pres_FA_graft_choice := pFG }
                           : AugGraftingData F_A pre_T_B pre_FA_B pres))) := by
  unfold enumAugGraftingData
  congr 1
  apply List.flatMap_congr
  intro choice_T _
  apply List.flatMap_congr
  intro fdata _
  -- listChoices allAlpha 0 = [[]]; flatMap of singleton [[]] applies the inner
  -- function once with targets = [].
  rw [show listChoices (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B) 0 =
        ([[]] : List (List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))) from
      listChoices_zero _]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-! ### §1.11.5b: `enumAugGraftingData_succ_factored` — head decomposition

Cons-case factored form for `enumAugGraftingData`: peels one `C_target` off
the front and decomposes its enumeration into a 4-bucket bind. The standard
form analog `enumGraftingData_succ_factored` (§1.10.1) is the
`pres = (fun _ => [])` specialization. -/

/-- **Factored cons-case decomposition** for `enumAugGraftingData`. Peels
    one `C_target` off the front (via `listChoices_succ`) and decomposes
    the per-target enumeration into a 4-bucket bind (via
    `allAlphaConstrainedChoiceList_bind_eq_bucketList_bind`).

    Analog of `enumGraftingData_succ_factored` (§1.10.1) with 4 additional
    `pres_*_choice` enumeration layers preserved at the inner positions. -/
private theorem enumAugGraftingData_succ_factored
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (pres : QuadIdx → List (Planar α)) (n : Nat) :
    enumAugGraftingData T F_A pre_T_B pre_FA_B pres (n + 1) =
      (Multiset.ofList (listChoices (vertices T) pre_T_B.length)).bind fun choice_T =>
        (Multiset.ofList (listChoices (perKFChoice F_A) pre_FA_B.length)).bind fun fdata =>
          (([QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft] :
              Multiset QuadIdx).bind fun first_b =>
            (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B first_b).bind fun first_target =>
              (Multiset.ofList
                (listChoices (allAlphaConstrainedChoiceList T F_A pre_T_B pre_FA_B) n)).bind
                fun rest_targets =>
                  (Multiset.ofList
                      (listChoices (vertices T) (pres .T_orig).length)).bind fun pTO =>
                    (Multiset.ofList
                        (listChoices (perKFChoice pre_T_B) (pres .T_graft).length)).bind
                      fun pTG =>
                        (Multiset.ofList
                            (listChoices (perKFChoice F_A) (pres .FA_orig).length)).bind
                          fun pFO =>
                            (Multiset.ofList
                                (listChoices (perKFChoice pre_FA_B)
                                  (pres .FA_graft).length)).map fun pFG =>
                              ({ pre_T_B_choice := choice_T
                                 pre_FA_B_choice := fdata
                                 C_targets := first_target :: rest_targets
                                 pres_T_orig_choice := pTO
                                 pres_T_graft_choice := pTG
                                 pres_FA_orig_choice := pFO
                                 pres_FA_graft_choice := pFG }
                               : AugGraftingData F_A pre_T_B pre_FA_B pres)) := by
  unfold enumAugGraftingData
  -- Convert outer ofList of nested flatMaps to nested Multiset.bind via
  -- ← Multiset.coe_bind, entering each binder via bind_congr.
  rw [← Multiset.coe_bind]
  refine Multiset.bind_congr fun choice_T _ => ?_
  rw [← Multiset.coe_bind]
  refine Multiset.bind_congr fun fdata _ => ?_
  -- Peel the targets via listChoices_succ.
  rw [listChoices_succ]
  -- Push outer flatMap over allAlpha into the result via flatMap_assoc.
  rw [List.flatMap_assoc]
  -- Now: ofList (allAlpha.flatMap fun first =>
  --        ((listChoices allAlpha n).map fun rest => first :: rest).flatMap fun targets => INNER)
  -- Convert outer ofList over allAlpha.flatMap to Multiset.bind, then apply
  -- bucket-list factoring at the first level.
  rw [← Multiset.coe_bind]
  rw [allAlphaConstrainedChoiceList_bind_eq_bucketList_bind]
  -- Both sides now have [4 buckets].bind first_b => (enumAlpha first_b).bind first_target => INNER.
  refine Multiset.bind_congr fun first_b _ => ?_
  refine Multiset.bind_congr fun first_target _ => ?_
  -- Inner: ofList (((listChoices allAlpha n).map (fun a => first_target :: a)).flatMap (fun targets => INNER))
  -- Apply List.flatMap_map to combine (l.map f).flatMap g into l.flatMap (g ∘ f).
  rw [List.flatMap_map]
  -- Now: ofList ((listChoices allAlpha n).flatMap (fun a => INNER (first_target :: a)))
  rw [← Multiset.coe_bind]
  refine Multiset.bind_congr fun rest_targets _ => ?_
  -- Now 4 layers of pres_*_choice flatMap with .map at innermost.
  rw [← Multiset.coe_bind]
  refine Multiset.bind_congr fun pTO _ => ?_
  rw [← Multiset.coe_bind]
  refine Multiset.bind_congr fun pTG _ => ?_
  rw [← Multiset.coe_bind]
  refine Multiset.bind_congr fun pFO _ => ?_
  -- Innermost is ofList (l.map f) which is defeq to (ofList l).map f.
  rfl

/-! ### §1.11.5c: per-bucket leaf-equality helpers for cons case

For each first_b ∈ {T_orig, T_graft, FA_orig, FA_graft}, the leaf-level
equality between `augInterpret T agd' rest` (with `pres' = update pres
first_b (pres first_b ++ [c])` and `agd'.pres_first_b_choice = pTO ++ [v]`)
and `augInterpret T agd (c :: rest)` (with `agd.C_targets = first_target_b ::
targets` and `agd.pres_first_b_choice = pTO`). Both sides produce the same
forest because (a) for T_orig, the `(v, c)` pair appears in T-side pres
pairs on LHS but in T-side C-extracted pairs on RHS, equal by `++ assoc`;
(b) symmetric for T_graft (pre_T_B' computation), FA_orig (F'
computation), FA_graft (pre_FA_B' computation). -/

/-- Leaf equality for the T_orig bucket case of the cons step. -/
private theorem augInterpret_T_orig_succ_bridge
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (pres : QuadIdx → List (Planar α)) (c : Planar α) (rest : List (Planar α))
    (pre_T_B_choice : List Path) (pre_FA_B_choice : List (Fin F_A.length × Path))
    (targets : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
    (pTO : List Path) (v : Path)
    (pTG : List (Fin pre_T_B.length × Path))
    (pFO : List (Fin F_A.length × Path))
    (pFG : List (Fin pre_FA_B.length × Path))
    (hPTOlen : pTO.length = (pres QuadIdx.T_orig).length) :
    augInterpret T
      ({ pre_T_B_choice := pre_T_B_choice
         pre_FA_B_choice := pre_FA_B_choice
         C_targets := targets
         pres_T_orig_choice := pTO ++ [v]
         pres_T_graft_choice := pTG
         pres_FA_orig_choice := pFO
         pres_FA_graft_choice := pFG }
       : AugGraftingData F_A pre_T_B pre_FA_B
           (Function.update pres QuadIdx.T_orig (pres QuadIdx.T_orig ++ [c]))) rest =
    augInterpret T
      ({ pre_T_B_choice := pre_T_B_choice
         pre_FA_B_choice := pre_FA_B_choice
         C_targets := AlphaConstrainedChoice.t_orig v :: targets
         pres_T_orig_choice := pTO
         pres_T_graft_choice := pTG
         pres_FA_orig_choice := pFO
         pres_FA_graft_choice := pFG }
       : AugGraftingData F_A pre_T_B pre_FA_B pres) (c :: rest) := by
  -- Both sides produce the same `T' :: F'` forest. The `.t_orig v` on RHS
  -- C_targets contributes `(v, c)` to extractTOrigPairs (T-side); the `(v, c)`
  -- appended to LHS's pres_T_orig_choice contributes to pres_T_orig_pairs
  -- (also T-side). These land in the same T' input position (right after
  -- pre_T_B'-derived pairs); the F-side and T-side pre_T_B' computations are
  -- unaffected (extractTGraft/FAOrig/FAGraft on `.t_orig` reduces to dropping it).
  unfold augInterpret
  -- Reduce Function.update on LHS: T_orig → pres T_orig ++ [c]; others → pres .
  have hT : (Function.update pres QuadIdx.T_orig (pres QuadIdx.T_orig ++ [c]))
              QuadIdx.T_orig = pres QuadIdx.T_orig ++ [c] := Function.update_self _ _ _
  have hG : (Function.update pres QuadIdx.T_orig (pres QuadIdx.T_orig ++ [c]))
              QuadIdx.T_graft = pres QuadIdx.T_graft :=
    Function.update_of_ne (by decide) _ _
  have hO : (Function.update pres QuadIdx.T_orig (pres QuadIdx.T_orig ++ [c]))
              QuadIdx.FA_orig = pres QuadIdx.FA_orig :=
    Function.update_of_ne (by decide) _ _
  have hF : (Function.update pres QuadIdx.T_orig (pres QuadIdx.T_orig ++ [c]))
              QuadIdx.FA_graft = pres QuadIdx.FA_graft :=
    Function.update_of_ne (by decide) _ _
  rw [hT, hG, hO, hF]
  -- After hT/hG/hO/hF, both pres-applications are computed.
  -- T-side T' input list: differs only in placement of `(v, c)`.
  --   LHS: ... ++ (pTO ++ [v]).zip (pres T_orig ++ [c]) ++ extractTOrig(targets.zip rest)
  --   RHS: ... ++ pTO.zip (pres T_orig) ++ extractTOrig((.t_orig v :: targets).zip (c :: rest))
  -- The RHS extractTOrig reduces by `rfl` (filterMap on .t_orig matches),
  -- yielding `(v, c) :: extractTOrig(targets.zip rest)`.
  -- The LHS zip splits via List.zip_append hPTOlen, yielding pTO.zip ++ [(v, c)] ++ ...
  -- F-side: extractFA{Orig,Graft} on .t_orig prefix definitionally drops it
  -- (the catch-all match clause). pre_T_B' computation similar.
  rw [List.zip_append hPTOlen]
  -- Reduce: [v].zip [c] → [(v, c)]; [].zip [] → []; nil_append; extractTOrig on
  -- (.t_orig v, c) :: rest → (v, c) :: extractTOrig rest; extract*Pairs on
  -- (.t_orig v, c) :: rest for non-T_orig buckets → unchanged.
  simp only [List.zip_cons_cons, List.zip_nil_right, List.zip_nil_left,
             List.nil_append, List.cons_append, List.append_assoc,
             extractTOrigPairs_cons_t_orig, extractTGraftPairsAt_cons_t_orig,
             extractFAOrigPairsAt_cons_t_orig, extractFAGraftPairsAt_cons_t_orig]

/-- Leaf equality for the T_graft bucket case of the cons step. -/
private theorem augInterpret_T_graft_succ_bridge
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (pres : QuadIdx → List (Planar α)) (c : Planar α) (rest : List (Planar α))
    (pre_T_B_choice : List Path) (pre_FA_B_choice : List (Fin F_A.length × Path))
    (targets : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
    (pTO : List Path)
    (pTG : List (Fin pre_T_B.length × Path))
    (k : Fin pre_T_B.length) (q : Path)
    (pFO : List (Fin F_A.length × Path))
    (pFG : List (Fin pre_FA_B.length × Path))
    (hPTGlen : pTG.length = (pres QuadIdx.T_graft).length) :
    augInterpret T
      ({ pre_T_B_choice := pre_T_B_choice
         pre_FA_B_choice := pre_FA_B_choice
         C_targets := targets
         pres_T_orig_choice := pTO
         pres_T_graft_choice := pTG ++ [(k, q)]
         pres_FA_orig_choice := pFO
         pres_FA_graft_choice := pFG }
       : AugGraftingData F_A pre_T_B pre_FA_B
           (Function.update pres QuadIdx.T_graft (pres QuadIdx.T_graft ++ [c]))) rest =
    augInterpret T
      ({ pre_T_B_choice := pre_T_B_choice
         pre_FA_B_choice := pre_FA_B_choice
         C_targets := AlphaConstrainedChoice.t_graft k q :: targets
         pres_T_orig_choice := pTO
         pres_T_graft_choice := pTG
         pres_FA_orig_choice := pFO
         pres_FA_graft_choice := pFG }
       : AugGraftingData F_A pre_T_B pre_FA_B pres) (c :: rest) := by
  unfold augInterpret
  -- Reduce Function.update: T_graft → +[c]; others → unchanged.
  have hT : (Function.update pres QuadIdx.T_graft (pres QuadIdx.T_graft ++ [c]))
              QuadIdx.T_orig = pres QuadIdx.T_orig :=
    Function.update_of_ne (by decide) _ _
  have hG : (Function.update pres QuadIdx.T_graft (pres QuadIdx.T_graft ++ [c]))
              QuadIdx.T_graft = pres QuadIdx.T_graft ++ [c] :=
    Function.update_self _ _ _
  have hO : (Function.update pres QuadIdx.T_graft (pres QuadIdx.T_graft ++ [c]))
              QuadIdx.FA_orig = pres QuadIdx.FA_orig :=
    Function.update_of_ne (by decide) _ _
  have hF : (Function.update pres QuadIdx.T_graft (pres QuadIdx.T_graft ++ [c]))
              QuadIdx.FA_graft = pres QuadIdx.FA_graft :=
    Function.update_of_ne (by decide) _ _
  rw [hT, hG, hO, hF]
  -- Reduce LHS's (pTG ++ [(k, q)]).zip(pres T_graft ++ [c]) and RHS's
  -- (.t_graft k q :: targets).zip (c :: rest) to cons forms.
  rw [show (pTG ++ [(k, q)]).zip (pres QuadIdx.T_graft ++ [c]) =
        pTG.zip (pres QuadIdx.T_graft) ++ [((k, q), c)] from by
        rw [List.zip_append hPTGlen]; rfl,
      show (AlphaConstrainedChoice.t_graft k q :: targets).zip (c :: rest) =
        (AlphaConstrainedChoice.t_graft k q, c) :: targets.zip rest from rfl]
  -- Unify both sides via `List.filterMap_append` on LHS singleton + `extract*_cons_*`.
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
             List.append_nil, extractTOrigPairs, extractTGraftPairsAt,
             extractFAOrigPairsAt, extractFAGraftPairsAt]
  -- Now both sides have explicit filterMap structures. The leaf differs only in
  -- the T-graft contribution (per-k_idx, controlled by `if k = k_idx`).
  -- After the simp, F-side is auto-rfl; only T-side remains.
  -- T-side: descend to pre_T_B'[k_idx]'s function via congr, then funext.
  congr 6
  funext k_idx
  congr 1
  split_ifs with h
  · simp [List.append_assoc]
  · simp

/-- Leaf equality for the FA_orig bucket case of the cons step. -/
private theorem augInterpret_FA_orig_succ_bridge
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (pres : QuadIdx → List (Planar α)) (c : Planar α) (rest : List (Planar α))
    (pre_T_B_choice : List Path) (pre_FA_B_choice : List (Fin F_A.length × Path))
    (targets : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
    (pTO : List Path)
    (pTG : List (Fin pre_T_B.length × Path))
    (pFO : List (Fin F_A.length × Path))
    (i : Fin F_A.length) (v : Path)
    (pFG : List (Fin pre_FA_B.length × Path))
    (hPFOlen : pFO.length = (pres QuadIdx.FA_orig).length) :
    augInterpret T
      ({ pre_T_B_choice := pre_T_B_choice
         pre_FA_B_choice := pre_FA_B_choice
         C_targets := targets
         pres_T_orig_choice := pTO
         pres_T_graft_choice := pTG
         pres_FA_orig_choice := pFO ++ [(i, v)]
         pres_FA_graft_choice := pFG }
       : AugGraftingData F_A pre_T_B pre_FA_B
           (Function.update pres QuadIdx.FA_orig (pres QuadIdx.FA_orig ++ [c]))) rest =
    augInterpret T
      ({ pre_T_B_choice := pre_T_B_choice
         pre_FA_B_choice := pre_FA_B_choice
         C_targets := AlphaConstrainedChoice.fa_orig i v :: targets
         pres_T_orig_choice := pTO
         pres_T_graft_choice := pTG
         pres_FA_orig_choice := pFO
         pres_FA_graft_choice := pFG }
       : AugGraftingData F_A pre_T_B pre_FA_B pres) (c :: rest) := by
  unfold augInterpret
  have hT : (Function.update pres QuadIdx.FA_orig (pres QuadIdx.FA_orig ++ [c]))
              QuadIdx.T_orig = pres QuadIdx.T_orig :=
    Function.update_of_ne (by decide) _ _
  have hG : (Function.update pres QuadIdx.FA_orig (pres QuadIdx.FA_orig ++ [c]))
              QuadIdx.T_graft = pres QuadIdx.T_graft :=
    Function.update_of_ne (by decide) _ _
  have hO : (Function.update pres QuadIdx.FA_orig (pres QuadIdx.FA_orig ++ [c]))
              QuadIdx.FA_orig = pres QuadIdx.FA_orig ++ [c] :=
    Function.update_self _ _ _
  have hF : (Function.update pres QuadIdx.FA_orig (pres QuadIdx.FA_orig ++ [c]))
              QuadIdx.FA_graft = pres QuadIdx.FA_graft :=
    Function.update_of_ne (by decide) _ _
  rw [hT, hG, hO, hF]
  -- Reduce LHS's (pFO ++ [(i, v)]).zip and RHS's (.fa_orig i v :: targets).zip to cons forms.
  rw [show (pFO ++ [(i, v)]).zip (pres QuadIdx.FA_orig ++ [c]) =
        pFO.zip (pres QuadIdx.FA_orig) ++ [((i, v), c)] from by
        rw [List.zip_append hPFOlen]; rfl,
      show (AlphaConstrainedChoice.fa_orig i v :: targets).zip (c :: rest) =
        (AlphaConstrainedChoice.fa_orig i v, c) :: targets.zip rest from rfl]
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
             List.append_nil, extractTOrigPairs, extractTGraftPairsAt, extractFAOrigPairsAt,
             extractFAGraftPairsAt]
  -- F-side substantive (per-i_idx); other parts auto-rfl after simp.
  congr 6
  funext i_idx
  congr 1
  split_ifs with h
  · simp [List.append_assoc]
  · simp

/-- Leaf equality for the FA_graft bucket case of the cons step. -/
private theorem augInterpret_FA_graft_succ_bridge
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (pres : QuadIdx → List (Planar α)) (c : Planar α) (rest : List (Planar α))
    (pre_T_B_choice : List Path) (pre_FA_B_choice : List (Fin F_A.length × Path))
    (targets : List (AlphaConstrainedChoice F_A pre_T_B pre_FA_B))
    (pTO : List Path)
    (pTG : List (Fin pre_T_B.length × Path))
    (pFO : List (Fin F_A.length × Path))
    (pFG : List (Fin pre_FA_B.length × Path))
    (k : Fin pre_FA_B.length) (q : Path)
    (hPFGlen : pFG.length = (pres QuadIdx.FA_graft).length) :
    augInterpret T
      ({ pre_T_B_choice := pre_T_B_choice
         pre_FA_B_choice := pre_FA_B_choice
         C_targets := targets
         pres_T_orig_choice := pTO
         pres_T_graft_choice := pTG
         pres_FA_orig_choice := pFO
         pres_FA_graft_choice := pFG ++ [(k, q)] }
       : AugGraftingData F_A pre_T_B pre_FA_B
           (Function.update pres QuadIdx.FA_graft (pres QuadIdx.FA_graft ++ [c]))) rest =
    augInterpret T
      ({ pre_T_B_choice := pre_T_B_choice
         pre_FA_B_choice := pre_FA_B_choice
         C_targets := AlphaConstrainedChoice.fa_graft k q :: targets
         pres_T_orig_choice := pTO
         pres_T_graft_choice := pTG
         pres_FA_orig_choice := pFO
         pres_FA_graft_choice := pFG }
       : AugGraftingData F_A pre_T_B pre_FA_B pres) (c :: rest) := by
  unfold augInterpret
  have hT : (Function.update pres QuadIdx.FA_graft (pres QuadIdx.FA_graft ++ [c]))
              QuadIdx.T_orig = pres QuadIdx.T_orig :=
    Function.update_of_ne (by decide) _ _
  have hG : (Function.update pres QuadIdx.FA_graft (pres QuadIdx.FA_graft ++ [c]))
              QuadIdx.T_graft = pres QuadIdx.T_graft :=
    Function.update_of_ne (by decide) _ _
  have hO : (Function.update pres QuadIdx.FA_graft (pres QuadIdx.FA_graft ++ [c]))
              QuadIdx.FA_orig = pres QuadIdx.FA_orig :=
    Function.update_of_ne (by decide) _ _
  have hF : (Function.update pres QuadIdx.FA_graft (pres QuadIdx.FA_graft ++ [c]))
              QuadIdx.FA_graft = pres QuadIdx.FA_graft ++ [c] :=
    Function.update_self _ _ _
  rw [hT, hG, hO, hF]
  -- Reduce LHS's (pFG ++ [(k, q)]).zip and RHS's (.fa_graft k q :: targets).zip to cons forms.
  rw [show (pFG ++ [(k, q)]).zip (pres QuadIdx.FA_graft ++ [c]) =
        pFG.zip (pres QuadIdx.FA_graft) ++ [((k, q), c)] from by
        rw [List.zip_append hPFGlen]; rfl,
      show (AlphaConstrainedChoice.fa_graft k q :: targets).zip (c :: rest) =
        (AlphaConstrainedChoice.fa_graft k q, c) :: targets.zip rest from rfl]
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
             List.append_nil, extractTOrigPairs, extractTGraftPairsAt, extractFAOrigPairsAt,
             extractFAGraftPairsAt]
  -- F-side substantive: pre_FA_B'[k_idx] differs (per-k_idx), then the i-loop uses it.
  -- The pre_FA_B' (List.map fun k_idx ...) is used in pre_FA_B_choice.zip pre_FA_B' for F.
  -- T-side: T' has no FA_graft contribution (extract*_cons_fa_graft drops on T_orig/T_graft).
  -- T-side auto-rfl after simp; only F-side remains.
  -- F-side: descend per-i, then per-k_idx (pre_FA_B'[k_idx] differs).
  congr 1
  refine List.map_congr_left fun i _ => ?_
  congr 5
  refine List.map_congr_left fun k_idx _ => ?_
  congr 1
  split_ifs with h
  · simp [List.append_assoc]
  · simp

/-! ### §1.11.6: Strong-IH headline theorem (sorry-fenced)

The pres-parameterized analog of `RHS_eq_canonical_msform`. Generalizes the
standard form to track per-bucket pres data via `AugGraftingData`'s four
`pres_*_choice` fields.

**Structural plan for the proof** (multi-session work, ~500-900 LOC total):

* **Base case** `C = []`. After `iteratedQuadSum_nil_remaining`, the LHS is a
  4-deep bind over `(insertionForest pre_T_B (pres .T_graft))`,
  `(insertion T (... ++ pres .T_orig))`, `(insertionForest pre_FA_B (pres .FA_graft))`,
  `(insertionForest F_A (... ++ pres .FA_orig))`. Each layer expands via
  `insertionForest_eq_explicit` / `insertion_def`, then `listChoices_split_bind`
  splits the combined choice (e.g., for `(pre_T_B' ++ pres .T_orig).length`)
  into per-bucket choices `(choice_T, pTO)` aligning with `AugGraftingData`
  fields. After expansion + bind-reorderings, both sides reduce to the same
  6-deep multiset enumeration with `augInterpret`-style leaf — closeable via
  `enumAugGraftingData_zero` + `augInterpret_C_nil` + bind-congruence.
  Estimated: ~250-400 LOC.

* **Cons case** `C = c :: rest`. After `iteratedQuadSum_cons_remaining`, the
  LHS is `[4 buckets].bind first_b => iQS pres' rest .map msform` where
  `pres' = Function.update pres first_b (pres first_b ++ [c])`. Apply IH at
  `pres'` and `rest`. The RHS becomes
  `[4 buckets].bind first_b => (enumAugGraftingData ... pres' rest.length).map (augInterpret pres' · rest) .map msform`.
  Bridge to `(enumAugGraftingData ... pres (rest.length + 1)).map (augInterpret pres · (c :: rest)) .map msform`
  via the bijection: each `AlphaConstrainedChoice.t_orig v` (T_orig case) on
  the RHS-side `C_targets[0]` corresponds to `(first_b = T_orig, pres'_T_orig_choice = pres_T_orig_choice ++ [v])`
  on the strong-IH side. Symmetric for other 3 buckets. The augInterpret outputs
  match because pres pairs and C-derived pairs concatenate in the same order
  (pres first, then C). Estimated: ~250-500 LOC.

The cons case avoids the structural blocker of the standard cons-case attack
(per session 10's analysis): the per-bucket case-split happens at the
`AugGraftingData` enumeration level (before msform), not inside the
multiGraft pair-list (after msform). Each bucket's bijection is uniform —
"shift one entry from C_targets to pres_*_choice".

Closing both base + cons cases unblocks `RHS_eq_canonical_msform` (Phase C),
which together with `LHS_eq_canonical_msform` (Phase D) closes
`LHS_eq_iteratedQuadSum_msform_cons_alphaBind` (the A3.3 sorry-fence). -/

/-- **Strong-IH theorem** (sorry-fenced): the pres-parameterized canonical-form
    bridge for `iteratedQuadSum`. Specializes to `RHS_eq_canonical_msform` at
    `pres = (fun _ => [])`.

    Proof strategy: induction on `C`. Base case via expansion of all four
    insertionForest/insertion layers + bind reordering to match
    `enumAugGraftingData`. Cons case via IH at `pres' = update pres first_b
    (pres first_b ++ [c])` + per-bucket bijection moving the head choice
    between `pres_*_choice` and `C_targets[0]`. -/
private theorem RHS_eq_canonical_msform_pres
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (pres : QuadIdx → List (Planar α)) (C : List (Planar α)) :
    (iteratedQuadSum T F_A pre_T_B pre_FA_B pres C).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((enumAugGraftingData T F_A pre_T_B pre_FA_B pres C.length).map
        (fun agd => augInterpret T agd C)).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  induction C generalizing pres with
  | nil =>
    -- BASE CASE: C = []. Apply iteratedQuadSum_nil_remaining on LHS,
    -- enumAugGraftingData_zero on RHS (after reducing [].length), then
    -- Multiset.map_map collapses outer maps; reduce RHS leaf via
    -- augInterpret_C_nil.
    simp only [List.length_nil]
    rw [iteratedQuadSum_nil_remaining, enumAugGraftingData_zero,
        Multiset.map_map]
    -- Push augInterpret_C_nil into RHS leaf via funext + rfl.
    rw [show ((fun L => Multiset.ofList (L.map Nonplanar.mk)) ∘
              (fun agd : AugGraftingData F_A pre_T_B pre_FA_B pres =>
                augInterpret T agd ([] : List (Planar α)))) =
            (fun agd : AugGraftingData F_A pre_T_B pre_FA_B pres =>
              Multiset.ofList ((augInterpret T agd []).map Nonplanar.mk))
        from rfl]
    -- LHS expansion Step 1: expand outer insertionForest pre_T_B (pres .T_graft)
    -- via insertionForest_eq_explicit, then convert .map.bind via Multiset.bind_map.
    -- Push outer .map msform inside via Multiset.map_bind.
    rw [insertionForest_eq_explicit pre_T_B (pres .T_graft),
        show enumFChoices pre_T_B (pres .T_graft) =
            Multiset.ofList (listChoices (perKFChoice pre_T_B) (pres .T_graft).length)
          from rfl,
        Multiset.bind_map, Multiset.map_bind]
    -- LHS expansion Step 2: push msform further inside the bind chain.
    simp_rw [Multiset.map_bind]
    -- LHS now: bind pTG => bind T' => bind pre_FA_B' => map F' => msform (T' :: F').
    -- LHS expansion Step 3: expand third layer insertionForest pre_FA_B (pres .FA_graft)
    -- via insertionForest_eq_explicit. Use simp_rw to enter the binders.
    simp_rw [insertionForest_eq_explicit pre_FA_B (pres .FA_graft),
             show enumFChoices pre_FA_B (pres .FA_graft) =
                 Multiset.ofList (listChoices (perKFChoice pre_FA_B) (pres .FA_graft).length)
               from rfl,
             Multiset.bind_map]
    -- LHS expansion Step 4: expand inner insertion T (...) via insertion_def.
    -- Convert Multiset.ofList (l.map f) to (Multiset.ofList l).map f via ← map_coe,
    -- then Multiset.bind_map for the bind ∘ map. Pattern from line 2668.
    simp_rw [insertion_def, ← Multiset.map_coe, Multiset.bind_map]
    -- LHS expansion Step 5: expand inner insertionForest F_A (... ++ pres .FA_orig)
    -- via insertionForest_eq_explicit. Use enumFChoices unfolding.
    simp_rw [insertionForest_eq_explicit F_A,
             show ∀ pre_FA_B' : List (Planar α),
                 enumFChoices F_A (pre_FA_B' ++ pres .FA_orig) =
                 Multiset.ofList (listChoices (perKFChoice F_A)
                   (pre_FA_B' ++ pres .FA_orig).length)
               from fun _ => rfl]
    -- LHS expansion Step 6: collapse FA-side (Multiset.ofList .map buildFIns).map (T' :: ·)
    -- via Multiset.map_map.
    simp_rw [Multiset.map_map]
    -- LHS expansion Step 7: expand the combined-list lengths in listChoices arguments.
    -- (buildFIns F (pres .T_graft) pTG ++ pres .T_orig).length = pre_T_B.length + (pres .T_orig).length
    -- (buildFIns pre_FA_B (pres .FA_graft) pFG ++ pres .FA_orig).length = pre_FA_B.length + (pres .FA_orig).length
    simp_rw [List.length_append, buildFIns, List.length_map, List.length_finRange]
    -- LHS expansion Step 8: split combined choices via listChoices_split_bind for
    -- T-side (.bind), and listChoices_split_map for FA-side (.map at innermost).
    -- T-side: choice_T (pre_T_B.length) + pTO ((pres .T_orig).length).
    -- FA-side: fdata (pre_FA_B.length) + pFO ((pres .FA_orig).length).
    simp_rw [listChoices_split_bind, listChoices_split_map]
    -- LHS now has 5 binds + 1 map: (pTG, choice_T, pTO, pFG, fdata, pFO).
    -- Convert final .map to .bind via ← Multiset.bind_singleton.
    simp_rw [← Multiset.bind_singleton]
    -- Now LHS has 6 binds. Apply Multiset.bind_bind swaps to reach RHS order
    -- (choice_T, fdata, pTO, pTG, pFO, pFG). 8 swaps total.
    rw [Multiset.bind_bind]  -- swap 1: pTG↔choice_T
    conv_lhs => rhs; ext choice_T; rw [Multiset.bind_bind]  -- swap 2: pTG↔pTO
    conv_lhs => rhs; ext choice_T; rhs; ext pTO; rw [Multiset.bind_bind]  -- swap 3
    conv_lhs => rhs; ext choice_T; rhs; ext pTO; rhs; ext pFG; rw [Multiset.bind_bind]  -- swap 4
    conv_lhs => rhs; ext choice_T; rhs; ext pTO; rw [Multiset.bind_bind]  -- swap 5
    conv_lhs => rhs; ext choice_T; rw [Multiset.bind_bind]  -- swap 6
    conv_lhs => rhs; ext choice_T; rhs; ext fdata; rhs; ext pTO; rw [Multiset.bind_bind]  -- swap 7
    conv_lhs => rhs; ext choice_T; rhs; ext fdata; rhs; ext pTO; rhs; ext pTG; rw [Multiset.bind_bind]  -- swap 8
    -- Now LHS order: (choice_T, fdata, pTO, pTG, pFO, pFG) ✓
    -- Convert RHS Multiset.ofList of List.flatMap to nested Multiset.bind.
    simp_rw [← Multiset.coe_bind]
    -- The innermost RHS has Multiset.ofList (List.map ...). Convert via ← map_coe.
    simp_rw [← Multiset.map_coe]
    -- RHS has structure ((5 binds).Multiset.map _ M_6).bind (fun x => {leaf' x}).
    -- Apply Multiset.bind_assoc to push outer .bind through 5 inner binds.
    simp_rw [Multiset.bind_assoc]
    -- Now the OUTER structure is M_1.bind ... .M_5.bind (fun b5 => (M_6.map _).bind G).
    -- Combine the inner .map .bind via Multiset.bind_map.
    simp_rw [Multiset.bind_map]
    -- Now both sides are 6-deep .bind. Use Multiset.bind_congr per layer,
    -- capturing membership for length hypotheses.
    refine Multiset.bind_congr fun choice_T h_choice_T => ?_
    refine Multiset.bind_congr fun fdata h_fdata => ?_
    refine Multiset.bind_congr fun pTO _ => ?_
    refine Multiset.bind_congr fun pTG _ => ?_
    refine Multiset.bind_congr fun pFO _ => ?_
    refine Multiset.bind_congr fun pFG _ => ?_
    -- Length hypotheses for List.zip_append.
    have hcT : choice_T.length = pre_T_B.length :=
      mem_listChoices_length _ _ _ (Multiset.mem_coe.mp h_choice_T)
    have hfd : fdata.length = pre_FA_B.length :=
      mem_listChoices_length _ _ _ (Multiset.mem_coe.mp h_fdata)
    -- Equate the singleton multisets via underlying list equality.
    congr 1
    congr 1
    -- Now: list equality.
    -- Apply augInterpret_C_nil to RHS, unfold function compositions on LHS,
    -- and use List.zip_append + List.filterMap_append for the splits.
    rw [augInterpret_C_nil T]
    -- Reduce composition on LHS.
    simp only [Function.comp_apply, perTreePairsFromFChoice]
    -- Apply List.zip_append on T-side and F-side splits.
    have h_lhs_pre_T_B'_len :
        (List.map (fun i : Fin pre_T_B.length => multiGraft pre_T_B[i.val]
            ((pTG.zip (pres .T_graft)).filterMap fun p =>
              if p.fst.fst = i then some (p.fst.snd, p.snd) else none))
          (List.finRange pre_T_B.length)).length = choice_T.length := by
      rw [List.length_map, List.length_finRange, hcT]
    have h_lhs_pre_FA_B'_len :
        (List.map (fun i : Fin pre_FA_B.length => multiGraft pre_FA_B[i.val]
            ((pFG.zip (pres .FA_graft)).filterMap fun p =>
              if p.fst.fst = i then some (p.fst.snd, p.snd) else none))
          (List.finRange pre_FA_B.length)).length = fdata.length := by
      rw [List.length_map, List.length_finRange, hfd]
    rw [List.zip_append h_lhs_pre_T_B'_len.symm,
        List.zip_append h_lhs_pre_FA_B'_len.symm]
    -- Push filterMap through the resulting append in F-side. This closes the
    -- goal: both sides reduce to the same list expression.
    simp only [List.filterMap_append]
  | cons c rest ih =>
    -- CONS CASE: see §1.11.6 docstring for proof plan.
    -- Step 1: iteratedQuadSum_cons_remaining gives 4-bucket outer bind on LHS.
    -- Then push outer .map msform through bind via Multiset.map_bind.
    rw [iteratedQuadSum_cons_remaining, Multiset.map_bind]
    -- LHS: ([4 buckets]).bind first_b => (iteratedQuadSum ... pres' rest).map msform
    -- where pres' = update pres first_b (pres first_b ++ [c]).
    -- Step 2: Apply IH per first_b.
    conv_lhs =>
      rhs; ext first_b
      rw [ih (Function.update pres first_b (pres first_b ++ [c]))]
    -- LHS: ([4 buckets]).bind first_b =>
    --        ((enumAugGraftingData ... pres' rest.length).map (augInterpret · rest)).map msform
    -- Step 3: Apply enumAugGraftingData_succ_factored to RHS.
    rw [show (c :: rest).length = rest.length + 1 from rfl, enumAugGraftingData_succ_factored]
    -- Step 4: Push outer .map msform inside RHS via Multiset.map_map +
    -- Multiset.map_bind. RHS becomes nested bind chain ending with leaf
    -- msform (augInterpret AGD (c :: rest)).
    rw [Multiset.map_map]
    simp_rw [Multiset.map_bind]
    -- Step 5: RHS structure now is:
    --   choice_T.bind => fdata.bind => [4 buckets].bind first_b =>
    --     first_target.bind => rest_targets.bind => pTO.bind => pTG.bind => pFO.bind => pFG.map => leaf
    -- LHS has [4 buckets] outermost; need to swap on RHS via Multiset.bind_bind
    -- to bring [4 buckets] outside of fdata, then outside of choice_T.
    conv_rhs => rhs; ext choice_T; rw [Multiset.bind_bind]  -- swap (fdata, [4 buckets])
    rw [Multiset.bind_bind]  -- swap (choice_T, [4 buckets])
    -- Step 6: Both sides now have ([4 buckets]).bind first_b => INNER.
    refine Multiset.bind_congr fun first_b _ => ?_
    -- Per-bucket bridge: case-split on first_b.
    cases first_b
    -- Case T_orig: pres' .T_orig = pres .T_orig ++ [c]; LHS-side has pTO_ext
    -- of length (pres .T_orig).length + 1; RHS-side first_target = .t_orig v
    -- with (vertices T).map .t_orig as its enumeration.
    · -- LHS-side: 7-level enumeration with pTO_ext (length (pres T_orig).length + 1).
      -- RHS-side: choice_T, fdata, first_target ∈ enumAlpha T_orig, rest_targets,
      --           pTO (length (pres T_orig).length), pTG, pFO, pFG.
      -- Bridge: pTO_ext ↔ (pTO, v) via listChoices_split_bind; v becomes the first_target.
      -- Step T_orig.1: Expand LHS via unfold + collapse outer maps + flatMap-map.
      unfold enumAugGraftingData
      rw [Multiset.map_map, Multiset.map_coe]
      simp_rw [List.map_flatMap, List.map_map]
      -- Step T_orig.2: Convert all LHS flatMap layers to Multiset.bind chain.
      simp_rw [← Multiset.coe_bind]
      -- Step T_orig.3: Reduce Function.update for pres' buckets and length sums.
      simp only [show (Function.update pres QuadIdx.T_orig (pres QuadIdx.T_orig ++ [c]))
                        QuadIdx.T_orig = pres QuadIdx.T_orig ++ [c]
                  from Function.update_self _ _ _,
                 show (Function.update pres QuadIdx.T_orig (pres QuadIdx.T_orig ++ [c]))
                        QuadIdx.T_graft = pres QuadIdx.T_graft
                  from Function.update_of_ne (by decide) _ _,
                 show (Function.update pres QuadIdx.T_orig (pres QuadIdx.T_orig ++ [c]))
                        QuadIdx.FA_orig = pres QuadIdx.FA_orig
                  from Function.update_of_ne (by decide) _ _,
                 show (Function.update pres QuadIdx.T_orig (pres QuadIdx.T_orig ++ [c]))
                        QuadIdx.FA_graft = pres QuadIdx.FA_graft
                  from Function.update_of_ne (by decide) _ _,
                 List.length_append, List.length_singleton]
      -- Step T_orig.4: Reduce RHS enumAlpha T_orig to (ofList vert).map .t_orig,
      -- then convert (.map .t_orig).bind to (ofList vert).bind ∘ .t_orig via Multiset.bind_map.
      conv_rhs =>
        rw [show (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.T_orig :
                Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
              (Multiset.ofList (vertices T)).map AlphaConstrainedChoice.t_orig from by
              show (Multiset.ofList ((vertices T).map AlphaConstrainedChoice.t_orig) :
                    Multiset _) = (Multiset.ofList (vertices T)).map AlphaConstrainedChoice.t_orig
              rw [← Multiset.map_coe]]
      simp_rw [Multiset.bind_map]
      -- Step T_orig.5: Apply listChoices_split_bind on LHS pTO_ext layer.
      simp_rw [listChoices_split_bind (vertices T) (pres QuadIdx.T_orig).length 1]
      -- Step T_orig.6: Reduce listChoices vert 1 = vert.map (fun v => [v]) and
      -- combine the .map with .bind via Multiset.bind_map.
      rw [show (listChoices (vertices T) 1 : List (List Path)) =
            (vertices T).map (fun v => [v]) from by
            rw [show (1 : Nat) = 0 + 1 from rfl, listChoices_succ]
            simp only [listChoices_zero, List.map_singleton]
            rw [List.map_eq_flatMap]]
      simp_rw [← Multiset.map_coe, Multiset.bind_map]
      -- Step T_orig.7: Reorder LHS to bring v outside (matching RHS position).
      -- Current LHS: choice_T.bind => fdata.bind => targets.bind => pTO.bind => v.bind => INNER
      -- Want LHS:    choice_T.bind => fdata.bind => v.bind => targets.bind => pTO.bind => INNER
      -- Swap (pTO, v):
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata; rhs; ext targets
        rw [Multiset.bind_bind]
      -- Swap (targets, v):
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata
        rw [Multiset.bind_bind]
      -- Step T_orig.8: Apply bind_congr through 8 layers, then leaf via the helper.
      refine Multiset.bind_congr fun choice_T h_choice_T => ?_
      refine Multiset.bind_congr fun fdata h_fdata => ?_
      refine Multiset.bind_congr fun v _ => ?_
      refine Multiset.bind_congr fun rest_targets _ => ?_
      refine Multiset.bind_congr fun pTO h_pTO => ?_
      refine Multiset.bind_congr fun pTG _ => ?_
      refine Multiset.bind_congr fun pFO _ => ?_
      -- Leaf: .map fun pFG => msform(augInterpret AGD' rest)
      --     = .map fun pFG => msform(augInterpret AGD (c :: rest))
      -- RHS still has nested .map (from Multiset.map_bind on enumAlpha), collapse
      -- to single .map via Multiset.map_map. Then equate functions per-pFG via
      -- the leaf helper.
      have hPTOlen : pTO.length = (pres QuadIdx.T_orig).length :=
        mem_listChoices_length _ _ _ (Multiset.mem_coe.mp h_pTO)
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun pFG _ => ?_
      simp only [Function.comp_apply]
      exact congrArg _ (augInterpret_T_orig_succ_bridge T pres c rest choice_T fdata
        rest_targets pTO v pTG pFO pFG hPTOlen ▸ rfl)
    -- Case T_graft: pres' .T_graft = pres .T_graft ++ [c]; LHS-side has pTG_ext
    -- of length (pres .T_graft).length + 1; RHS-side first_target = .t_graft k q
    -- with enumeration via (perKFChoice pre_T_B).map (fun p => .t_graft p.fst p.snd).
    · unfold enumAugGraftingData
      rw [Multiset.map_map, Multiset.map_coe]
      simp_rw [List.map_flatMap, List.map_map]
      simp_rw [← Multiset.coe_bind]
      simp only [show (Function.update pres QuadIdx.T_graft (pres QuadIdx.T_graft ++ [c]))
                        QuadIdx.T_orig = pres QuadIdx.T_orig
                  from Function.update_of_ne (by decide) _ _,
                 show (Function.update pres QuadIdx.T_graft (pres QuadIdx.T_graft ++ [c]))
                        QuadIdx.T_graft = pres QuadIdx.T_graft ++ [c]
                  from Function.update_self _ _ _,
                 show (Function.update pres QuadIdx.T_graft (pres QuadIdx.T_graft ++ [c]))
                        QuadIdx.FA_orig = pres QuadIdx.FA_orig
                  from Function.update_of_ne (by decide) _ _,
                 show (Function.update pres QuadIdx.T_graft (pres QuadIdx.T_graft ++ [c]))
                        QuadIdx.FA_graft = pres QuadIdx.FA_graft
                  from Function.update_of_ne (by decide) _ _,
                 List.length_append, List.length_singleton]
      conv_rhs =>
        rw [show (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.T_graft :
                Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
              (Multiset.ofList (perKFChoice pre_T_B)).map
                (fun p => AlphaConstrainedChoice.t_graft p.fst p.snd) from by
              rw [← ofList_T_graft_eq_enumAlpha]
              rw [show (List.finRange pre_T_B.length).flatMap (fun k =>
                          (vertices pre_T_B[k.val]).map (AlphaConstrainedChoice.t_graft k)) =
                       (perKFChoice pre_T_B).map
                         (fun p => AlphaConstrainedChoice.t_graft p.fst p.snd) from by
                    unfold perKFChoice
                    rw [List.map_flatMap]
                    apply List.flatMap_congr
                    intro k _
                    rw [List.map_map]
                    rfl]
              rw [← Multiset.map_coe]]
      simp_rw [Multiset.bind_map]
      simp_rw [listChoices_split_bind (perKFChoice pre_T_B) (pres QuadIdx.T_graft).length 1]
      rw [show (listChoices (perKFChoice pre_T_B) 1 :
                List (List (Fin pre_T_B.length × Path))) =
            (perKFChoice pre_T_B).map (fun p => [p]) from by
            rw [show (1 : Nat) = 0 + 1 from rfl, listChoices_succ]
            simp only [listChoices_zero, List.map_singleton]
            rw [List.map_eq_flatMap]]
      simp_rw [← Multiset.map_coe, Multiset.bind_map]
      -- Reorder LHS: bring (k, q) outside.
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata; rhs; ext targets; rhs; ext pTO
        rw [Multiset.bind_bind]
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata; rhs; ext targets
        rw [Multiset.bind_bind]
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata
        rw [Multiset.bind_bind]
      refine Multiset.bind_congr fun choice_T _ => ?_
      refine Multiset.bind_congr fun fdata _ => ?_
      refine Multiset.bind_congr fun kq _ => ?_
      refine Multiset.bind_congr fun rest_targets _ => ?_
      refine Multiset.bind_congr fun pTO _ => ?_
      refine Multiset.bind_congr fun pTG h_pTG => ?_
      refine Multiset.bind_congr fun pFO _ => ?_
      have hPTGlen : pTG.length = (pres QuadIdx.T_graft).length :=
        mem_listChoices_length _ _ _ (Multiset.mem_coe.mp h_pTG)
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun pFG _ => ?_
      simp only [Function.comp_apply]
      exact congrArg _ (augInterpret_T_graft_succ_bridge T pres c rest choice_T fdata
        rest_targets pTO pTG kq.fst kq.snd pFO pFG hPTGlen ▸ rfl)
    -- Case FA_orig: pres' .FA_orig = pres .FA_orig ++ [c]; LHS-side has pFO_ext
    -- of length (pres .FA_orig).length + 1; RHS-side first_target = .fa_orig i v
    -- with enumeration via (perKFChoice F_A).map (fun p => .fa_orig p.fst p.snd).
    · unfold enumAugGraftingData
      rw [Multiset.map_map, Multiset.map_coe]
      simp_rw [List.map_flatMap, List.map_map]
      simp_rw [← Multiset.coe_bind]
      simp only [show (Function.update pres QuadIdx.FA_orig (pres QuadIdx.FA_orig ++ [c]))
                        QuadIdx.T_orig = pres QuadIdx.T_orig
                  from Function.update_of_ne (by decide) _ _,
                 show (Function.update pres QuadIdx.FA_orig (pres QuadIdx.FA_orig ++ [c]))
                        QuadIdx.T_graft = pres QuadIdx.T_graft
                  from Function.update_of_ne (by decide) _ _,
                 show (Function.update pres QuadIdx.FA_orig (pres QuadIdx.FA_orig ++ [c]))
                        QuadIdx.FA_orig = pres QuadIdx.FA_orig ++ [c]
                  from Function.update_self _ _ _,
                 show (Function.update pres QuadIdx.FA_orig (pres QuadIdx.FA_orig ++ [c]))
                        QuadIdx.FA_graft = pres QuadIdx.FA_graft
                  from Function.update_of_ne (by decide) _ _,
                 List.length_append, List.length_singleton]
      conv_rhs =>
        rw [show (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.FA_orig :
                Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
              (Multiset.ofList (perKFChoice F_A)).map
                (fun p => AlphaConstrainedChoice.fa_orig p.fst p.snd) from by
              rw [← ofList_FA_orig_eq_enumAlpha]
              rw [show (List.finRange F_A.length).flatMap (fun i =>
                          (vertices F_A[i.val]).map (AlphaConstrainedChoice.fa_orig i)) =
                       (perKFChoice F_A).map
                         (fun p => AlphaConstrainedChoice.fa_orig p.fst p.snd) from by
                    unfold perKFChoice
                    rw [List.map_flatMap]
                    apply List.flatMap_congr
                    intro i _
                    rw [List.map_map]
                    rfl]
              rw [← Multiset.map_coe]]
      simp_rw [Multiset.bind_map]
      simp_rw [listChoices_split_bind (perKFChoice F_A) (pres QuadIdx.FA_orig).length 1]
      rw [show (listChoices (perKFChoice F_A) 1 :
                List (List (Fin F_A.length × Path))) =
            (perKFChoice F_A).map (fun p => [p]) from by
            rw [show (1 : Nat) = 0 + 1 from rfl, listChoices_succ]
            simp only [listChoices_zero, List.map_singleton]
            rw [List.map_eq_flatMap]]
      simp_rw [← Multiset.map_coe, Multiset.bind_map]
      -- Reorder LHS: bring (i, v) outside past pTO, pTG, targets.
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata; rhs; ext targets; rhs; ext pTO; rhs; ext pTG
        rw [Multiset.bind_bind]
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata; rhs; ext targets; rhs; ext pTO
        rw [Multiset.bind_bind]
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata; rhs; ext targets
        rw [Multiset.bind_bind]
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata
        rw [Multiset.bind_bind]
      refine Multiset.bind_congr fun choice_T _ => ?_
      refine Multiset.bind_congr fun fdata _ => ?_
      refine Multiset.bind_congr fun iv _ => ?_
      refine Multiset.bind_congr fun rest_targets _ => ?_
      refine Multiset.bind_congr fun pTO _ => ?_
      refine Multiset.bind_congr fun pTG _ => ?_
      refine Multiset.bind_congr fun pFO h_pFO => ?_
      have hPFOlen : pFO.length = (pres QuadIdx.FA_orig).length :=
        mem_listChoices_length _ _ _ (Multiset.mem_coe.mp h_pFO)
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun pFG _ => ?_
      simp only [Function.comp_apply]
      exact congrArg _ (augInterpret_FA_orig_succ_bridge T pres c rest choice_T fdata
        rest_targets pTO pTG pFO iv.fst iv.snd pFG hPFOlen ▸ rfl)
    -- Case FA_graft: pres' .FA_graft = pres .FA_graft ++ [c]; LHS-side has pFG_ext
    -- of length (pres .FA_graft).length + 1; RHS-side first_target = .fa_graft k q
    -- with enumeration via (perKFChoice pre_FA_B).map (fun p => .fa_graft p.fst p.snd).
    · unfold enumAugGraftingData
      rw [Multiset.map_map, Multiset.map_coe]
      simp_rw [List.map_flatMap, List.map_map]
      simp_rw [← Multiset.coe_bind]
      simp only [show (Function.update pres QuadIdx.FA_graft (pres QuadIdx.FA_graft ++ [c]))
                        QuadIdx.T_orig = pres QuadIdx.T_orig
                  from Function.update_of_ne (by decide) _ _,
                 show (Function.update pres QuadIdx.FA_graft (pres QuadIdx.FA_graft ++ [c]))
                        QuadIdx.T_graft = pres QuadIdx.T_graft
                  from Function.update_of_ne (by decide) _ _,
                 show (Function.update pres QuadIdx.FA_graft (pres QuadIdx.FA_graft ++ [c]))
                        QuadIdx.FA_orig = pres QuadIdx.FA_orig
                  from Function.update_of_ne (by decide) _ _,
                 show (Function.update pres QuadIdx.FA_graft (pres QuadIdx.FA_graft ++ [c]))
                        QuadIdx.FA_graft = pres QuadIdx.FA_graft ++ [c]
                  from Function.update_self _ _ _,
                 List.length_append, List.length_singleton]
      conv_rhs =>
        rw [show (enumAlphaConstrainedChoice T F_A pre_T_B pre_FA_B QuadIdx.FA_graft :
                Multiset (AlphaConstrainedChoice F_A pre_T_B pre_FA_B)) =
              (Multiset.ofList (perKFChoice pre_FA_B)).map
                (fun p => AlphaConstrainedChoice.fa_graft p.fst p.snd) from by
              rw [← ofList_FA_graft_eq_enumAlpha]
              rw [show (List.finRange pre_FA_B.length).flatMap (fun k =>
                          (vertices pre_FA_B[k.val]).map (AlphaConstrainedChoice.fa_graft k)) =
                       (perKFChoice pre_FA_B).map
                         (fun p => AlphaConstrainedChoice.fa_graft p.fst p.snd) from by
                    unfold perKFChoice
                    rw [List.map_flatMap]
                    apply List.flatMap_congr
                    intro k _
                    rw [List.map_map]
                    rfl]
              rw [← Multiset.map_coe]]
      simp_rw [Multiset.bind_map]
      -- Convert innermost `↑(List.map G L)` to `(↑L).map G` so listChoices_split_map matches.
      simp_rw [← Multiset.map_coe]
      simp_rw [listChoices_split_map (perKFChoice pre_FA_B) (pres QuadIdx.FA_graft).length 1]
      rw [show (listChoices (perKFChoice pre_FA_B) 1 :
                List (List (Fin pre_FA_B.length × Path))) =
            (perKFChoice pre_FA_B).map (fun p => [p]) from by
            rw [show (1 : Nat) = 0 + 1 from rfl, listChoices_succ]
            simp only [listChoices_zero, List.map_singleton]
            rw [List.map_eq_flatMap]]
      simp_rw [← Multiset.map_coe, Multiset.map_map]
      -- Convert LHS innermost .map (over perKFChoice) to .bind over singleton,
      -- so it matches RHS's bind structure for first_target.
      simp_rw [← Multiset.bind_singleton]
      -- Reorder LHS: bring p (innermost) outside past pFG_part1, pFO, pTG, pTO, targets.
      -- Total 5 swaps to bring p from position 8 to position 3.
      -- Reorder LHS: bring p (currently innermost, depth 8) to position 3.
      -- Each swap moves p past one outer layer. Total: 5 swaps to go from
      -- position 8 → 7 → 6 → 5 → 4 → 3.
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata; rhs; ext targets; rhs; ext pTO
        rhs; ext pTG; rhs; ext pFO
        rw [Multiset.bind_bind]
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata; rhs; ext targets; rhs; ext pTO; rhs; ext pTG
        rw [Multiset.bind_bind]
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata; rhs; ext targets; rhs; ext pTO
        rw [Multiset.bind_bind]
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata; rhs; ext targets
        rw [Multiset.bind_bind]
      conv_lhs =>
        rhs; ext choice_T; rhs; ext fdata
        rw [Multiset.bind_bind]
      -- RHS innermost was already converted to .bind by global simp_rw [← bind_singleton].
      refine Multiset.bind_congr fun choice_T _ => ?_
      refine Multiset.bind_congr fun fdata _ => ?_
      refine Multiset.bind_congr fun kq _ => ?_
      refine Multiset.bind_congr fun rest_targets _ => ?_
      refine Multiset.bind_congr fun pTO _ => ?_
      refine Multiset.bind_congr fun pTG _ => ?_
      refine Multiset.bind_congr fun pFO _ => ?_
      refine Multiset.bind_congr fun pFG h_pFG => ?_
      have hPFGlen : pFG.length = (pres QuadIdx.FA_graft).length :=
        mem_listChoices_length _ _ _ (Multiset.mem_coe.mp h_pFG)
      -- Both sides are now singletons. Equate via leaf helper wrapped in singleton+map.
      simp only [Function.comp_apply]
      have h := augInterpret_FA_graft_succ_bridge T pres c rest choice_T fdata
        rest_targets pTO pTG pFO pFG kq.fst kq.snd hPFGlen
      -- Replace `(kq.1, kq.2)` with `kq` in `pFG ++ [(kq.1, kq.2)]` via Prod eta.
      have hkq : pFG ++ [(kq.fst, kq.snd)] = pFG ++ [kq] := by rfl
      rw [hkq] at h
      exact congrArg
        (fun (M : Multiset (Planar α)) =>
          ({M.bind fun x => ({Nonplanar.mk x} : Multiset _)} : Multiset _))
        (congrArg Multiset.ofList h)

/-! ### §1.11.7: `RHS_eq_canonical_msform` derived from strong-IH

The standard form follows from `RHS_eq_canonical_msform_pres` at
`pres = (fun _ => [])`. At empty pres, the four `pres_*_choice` fields all
have length 0 (forced to `[]` by the `listChoices ... 0 = [[]]` collapse in
`enumAugGraftingData`), and `augInterpret T agd C` reduces to `interpret T
(agd-projected-to-GraftingData) C` (the pres pairs all become empty zips). -/

/-- Project an `AugGraftingData` at empty pres down to a standard `GraftingData`
    (forgetting the four `pres_*_choice` fields, which are all `[]` by length). -/
private def agdToGd
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (agd : AugGraftingData F_A pre_T_B pre_FA_B (fun _ => [])) :
    GraftingData F_A pre_T_B pre_FA_B :=
  { pre_T_B_choice := agd.pre_T_B_choice
    pre_FA_B_choice := agd.pre_FA_B_choice
    C_targets := agd.C_targets }

/-- Inject a `GraftingData` to an `AugGraftingData` at empty pres (with all
    four `pres_*_choice` fields set to `[]`, matching `(fun _ => []) bucket`'s
    length 0). -/
private def gdToAgdEmpty
    {F_A pre_T_B pre_FA_B : List (Planar α)}
    (gd : GraftingData F_A pre_T_B pre_FA_B) :
    AugGraftingData F_A pre_T_B pre_FA_B (fun _ => []) :=
  { pre_T_B_choice := gd.pre_T_B_choice
    pre_FA_B_choice := gd.pre_FA_B_choice
    C_targets := gd.C_targets
    pres_T_orig_choice := []
    pres_T_graft_choice := []
    pres_FA_orig_choice := []
    pres_FA_graft_choice := [] }

/-- At `pres = (fun _ => [])`, `augInterpret` reduces to `interpret`: every
    `pres_*_pairs` contribution vanishes because `(fun _ => []) bucket = []`,
    so the per-bucket `.zip []` and `.zip [].filterMap` evaluate to `[]`.

    Sorry-fenced: requires careful let-binding reduction (4 pres pair-bindings
    collapse to `[]`, then `_ ++ []` cleanup). The reduction is conceptually
    straightforward but Lean's `simp`/`dsimp` interaction with let-bindings
    inside `def` bodies needs precise handling. -/
private theorem augInterpret_at_empty_pres
    (T : Planar α) {F_A pre_T_B pre_FA_B : List (Planar α)}
    (agd : AugGraftingData F_A pre_T_B pre_FA_B (fun _ => []))
    (C : List (Planar α)) :
    augInterpret T agd C = interpret T (agdToGd agd) C := by
  simp only [augInterpret, interpret, agdToGd,
             List.zip_nil_right, List.filterMap_nil,
             List.nil_append, List.append_nil]

/-- At empty pres, `enumAugGraftingData` is the image of `enumGraftingData`
    under `gdToAgdEmpty`. The four inner flatMaps over `listChoices _ 0 = [[]]`
    each iterate once with the empty choice, collapsing the augmented enumeration
    to the standard one.

    Sorry-fenced: requires reducing 4 inner `listChoices xs 0 = [[]]` flatMaps
    to single iterations + collapsing `flatMap (fun x => [f x]) ↔ map f`.
    Provable structurally; proof scaffolding present (commented above). -/
private theorem enumAugGraftingData_at_empty_pres
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α)) (n : Nat) :
    enumAugGraftingData T F_A pre_T_B pre_FA_B (fun _ => []) n =
      (enumGraftingData T F_A pre_T_B pre_FA_B n).map gdToAgdEmpty := by
  unfold enumAugGraftingData enumGraftingData
  -- Push the outer .map gdToAgdEmpty through Multiset.ofList.
  rw [Multiset.map_coe]
  -- Reduce both sides to List equality.
  congr 1
  -- (fun _ => []) X = []; (pres .X).length = 0; collapse 4 inner [[]] flatMaps.
  -- After collapse, LHS inner singleton and RHS .map should match.
  simp_rw [List.map_flatMap, List.map_map]
  apply List.flatMap_congr; intro choice_T _
  apply List.flatMap_congr; intro fdata _
  -- LHS: (listChoices alphaConstr n).flatMap fun targets =>
  --        [[]].flatMap fun pTO => [[]].flatMap fun pTG =>
  --          [[]].flatMap fun pFO => [[]].map fun pFG => agd
  -- RHS: (listChoices alphaConstr n).map fun targets =>
  --        gdToAgdEmpty {pre_T_B_choice := choice_T, ..., C_targets := targets}
  rw [List.map_eq_flatMap]
  apply List.flatMap_congr; intro targets _
  -- Each [[]].flatMap g reduces to g [], [[]].map f reduces to [f []].
  rfl

/-- The standard `RHS_eq_canonical_msform`, derived from the strong-IH
    `RHS_eq_canonical_msform_pres` at `pres = (fun _ => [])`. The chain of
    sorries is (1) the strong-IH itself (§1.11.6), (2) the empty-pres bridges
    `augInterpret_at_empty_pres` and `enumAugGraftingData_at_empty_pres`. -/
private theorem RHS_eq_canonical_msform
    (T : Planar α) (F_A pre_T_B pre_FA_B C : List (Planar α)) :
    ((Multiset.ofList (listChoices
        [QuadIdx.T_orig, QuadIdx.T_graft, QuadIdx.FA_orig, QuadIdx.FA_graft]
        C.length)).bind fun a =>
      iteratedQuadSum T F_A pre_T_B pre_FA_B
        (fun t => bucketSlice C a t) []).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((enumGraftingData T F_A pre_T_B pre_FA_B C.length).map
        (fun gd => interpret T gd C)).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- LHS: rewrite via iteratedQuadSum_eq_alphaBind in reverse to expose
  -- iQS at pres = (fun _ => []) on the full C.
  rw [← iteratedQuadSum_eq_alphaBind]
  -- LHS now: (iteratedQuadSum T F_A pre_T_B pre_FA_B (fun _ => []) C).map msform
  -- Apply strong-IH at pres = (fun _ => []).
  rw [RHS_eq_canonical_msform_pres T F_A pre_T_B pre_FA_B (fun _ => []) C]
  -- Bridge enumAug at empty pres → enumGrafting via gdToAgdEmpty, then
  -- augInterpret at empty pres → interpret via agdToGd.
  congr 1
  rw [enumAugGraftingData_at_empty_pres T F_A pre_T_B pre_FA_B C.length,
      Multiset.map_map]
  -- Goal: (enumGraftingData T F_A pre_T_B pre_FA_B C.length).map
  --         (augInterpret T · C ∘ gdToAgdEmpty) = ... .map (interpret T · C)
  refine Multiset.map_congr rfl fun gd _ => ?_
  -- Per gd, augInterpret T (gdToAgdEmpty gd) C = interpret T gd C
  -- via augInterpret_at_empty_pres (LHS reduces to interpret T (agdToGd
  -- (gdToAgdEmpty gd)) C, and agdToGd (gdToAgdEmpty gd) = gd).
  rw [Function.comp_apply, augInterpret_at_empty_pres]
  -- agdToGd (gdToAgdEmpty gd) = gd by struct-equality (both copy the same 3 fields).
  show interpret T (agdToGd (gdToAgdEmpty gd)) C = interpret T gd C
  rfl

/-! ### §1.9.5: Future bridges (full C : List)

The two theorems below are the targets for the next session. Both are stated
here as documentation; their proofs go in §1.10 (LHS bridge) and §1.11 (RHS
bridge). After both land, `LHS_eq_iteratedQuadSum_msform_cons_alphaBind` closes
in ~10-30 LOC by chaining them.

**`LHS_eq_canonical`** (target):
```lean
private theorem LHS_eq_canonical
    (T : Planar α) (F_A pre_T_B pre_FA_B C : List (Planar α)) :
  ((insertion T pre_T_B).bind fun T_ins =>
      (insertionForest F_A pre_FA_B).bind fun F_ins =>
        insertionForest (T_ins :: F_ins) C) =
  (enumGraftingData T F_A pre_T_B pre_FA_B C.length).map (interpret T · C)
```

**`RHS_eq_canonical_msform`** (target):
```lean
private theorem RHS_eq_canonical_msform
    (T : Planar α) (F_A pre_T_B pre_FA_B C : List (Planar α)) :
  ((Multiset.ofList (listChoices QuadIdx_list C.length)).bind fun a =>
      iteratedQuadSum T F_A pre_T_B pre_FA_B
        (fun t => bucketSlice C a t) []).map msform =
  ((enumGraftingData T F_A pre_T_B pre_FA_B C.length).map (interpret T · C)).map msform
```

**Caveat (correction to prior session prompt)**: `LHS_eq_canonical` likely
needs msform absorption on both sides too, NOT just the RHS bridge. Reason:
`interpret`'s T-side does ONE multi-graft pass
(`multiGraft T (choice_T.zip pre_T_B' ++ T_orig_pairs)`) while the LHS form
does TWO passes (first pre_T_B into T → T_ins, then T_orig-c's into T_ins).
At any vertex `v ∈ pairSources (choice_T.zip pre_T_B)` that ALSO receives a
T_orig-bucket c (via `.t_orig v`), the planar order of children differs
between the two forms (in interpret's pair list, T_orig comes after pre_T_B;
in the LHS, T_orig grafts on top of T_ins which already has pre_T_B grafted
as its first children at that vertex). The msform-level absorption uses
`multiGraft_perm_pair` to eliminate this planar-order difference.

After both: the cons-case sorry-fence collapses by composing them with
`Multiset.map_congr` (both sides msform-wrapped). -/

/-! ### §1.12: LHS-side strong-IH (sorry-fenced cons case)

Mirrors §1.11.6's `RHS_eq_canonical_msform_pres` for the LHS side. The
`LHS_form pres C` shape is the iteratedQuadSum-leaf shape with
`insertionForest (T' :: F') C` at the innermost (instead of `T' :: F'`):

```
LHS_form pres C =
  (insertionForest pre_T_B (pres .T_graft)).bind pre_T_B' =>
    (insertion T (pre_T_B' ++ pres .T_orig)).bind T' =>
      (insertionForest pre_FA_B (pres .FA_graft)).bind pre_FA_B' =>
        (insertionForest F_A (pre_FA_B' ++ pres .FA_orig)).bind F' =>
          insertionForest (T' :: F') C
```

* At `pres = (fun _ => [])`: `LHS_form` reduces to the standard LHS via
  `insertionForest_nil_guests` + `Multiset.singleton_bind` + `List.append_nil`.
* At `C = []`: `insertionForest (T' :: F') []` collapses to `{T' :: F'}`,
  reducing `LHS_form pres []` to `iteratedQuadSum T F_A pre_T_B pre_FA_B pres []`
  (the leaf form). The strong-IH then reduces to `RHS_eq_canonical_msform_pres`
  at `C = []`, which is sorry-free.

The cons case (sorry-fenced) requires:
1. Peel `c` off the inner `insertionForest (T' :: F') (c :: rest)`.
2. Use `vertices_forest_eq_partition` (`Graft.lean §10.5`) to decompose c's
   vertex choice into 4 buckets matching `QuadIdx`.
3. For each bucket, the c-graft into (T' :: F') equals augmenting the
   corresponding `pres` bucket with `[c]` modulo `multiGraft_perm_pair`.
4. Apply IH at `pres'` and rest.
5. Bridge to canonical-form RHS via `enumAugGraftingData_succ_factored` and
   the 4 leaf bridges (parallel to RHS strong-IH cons case from session 13).

Estimated cons case proof: ~400-700 LOC, deferred to next session. -/

/-- **LHS strong-IH** (sorry-fenced cons case): pres-parameterized canonical-form
    bridge for the LHS side. Mirrors `RHS_eq_canonical_msform_pres`.

    Specializes to `LHS_eq_canonical_msform` at `pres = (fun _ => [])`. -/
private theorem LHS_eq_canonical_msform_pres
    (T : Planar α) (F_A pre_T_B pre_FA_B : List (Planar α))
    (pres : QuadIdx → List (Planar α)) (C : List (Planar α)) :
    ((insertionForest pre_T_B (pres .T_graft)).bind fun pre_T_B' =>
        (insertion T (pre_T_B' ++ pres .T_orig)).bind fun T' =>
          (insertionForest pre_FA_B (pres .FA_graft)).bind fun pre_FA_B' =>
            (insertionForest F_A (pre_FA_B' ++ pres .FA_orig)).bind fun F' =>
              insertionForest (T' :: F') C).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((enumAugGraftingData T F_A pre_T_B pre_FA_B pres C.length).map
        (fun agd => augInterpret T agd C)).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  induction C generalizing pres with
  | nil =>
    -- LHS at C = []: insertionForest (T' :: F') [] = {T' :: F'}, so the inner
    -- .bind F' collapses to .map F' via Multiset.bind_singleton, reducing to
    -- iteratedQuadSum's nil leaf form. Then RHS_eq_canonical_msform_pres at
    -- C = [] (sorry-free) closes.
    simp only [insertionForest_cons_host_nil_guests, Multiset.bind_singleton]
    -- LHS now matches `iteratedQuadSum T F_A pre_T_B pre_FA_B pres []` (by
    -- iteratedQuadSum_nil_remaining, in reverse).
    rw [show ((insertionForest pre_T_B (pres QuadIdx.T_graft)).bind fun pre_T_B' =>
              (insertion T (pre_T_B' ++ pres QuadIdx.T_orig)).bind fun T' =>
                (insertionForest pre_FA_B (pres QuadIdx.FA_graft)).bind fun pre_FA_B' =>
                  (insertionForest F_A (pre_FA_B' ++ pres QuadIdx.FA_orig)).map fun F' =>
                    T' :: F') =
            iteratedQuadSum T F_A pre_T_B pre_FA_B pres []
        from (iteratedQuadSum_nil_remaining T F_A pre_T_B pre_FA_B pres).symm]
    exact RHS_eq_canonical_msform_pres T F_A pre_T_B pre_FA_B pres []
  | cons c rest ih =>
    -- TODO: cons case. ~400-700 LOC. Strategy:
    -- 1. Peel c off via `insertionForest_cons_host_nonempty_elem` (or analog)
    --    on the innermost `insertionForest (T' :: F') (c :: rest)`.
    -- 2. Decompose c-vertex choice via `vertices_forest_eq_partition` into 4
    --    α-bucket cases.
    -- 3. For each bucket, absorb c into pres bucket modulo `multiGraft_perm_pair`.
    -- 4. Apply IH at pres' = update pres first_b (pres first_b ++ [c]) and rest.
    -- 5. Bridge to canonical via `enumAugGraftingData_succ_factored` + 4 leaf
    --    bridges (parallel to RHS strong-IH cons case).
    sorry

/-! ### §1.13: `LHS_eq_canonical_msform` derived from strong-IH

The standard form follows from `LHS_eq_canonical_msform_pres` at
`pres = (fun _ => [])`. The LHS_form @ empty reduces to the standard LHS
via `insertionForest_nil_guests` (collapses pres .T_graft and pres .FA_graft
inserts to singletons) + `List.append_nil` (cleans up `_ ++ pres .T_orig`
and `_ ++ pres .FA_orig` appends) + `Multiset.singleton_bind` (collapses
the pre_T_B'/pre_FA_B' singleton binds). The canonical RHS reduces via
the same `enumAugGraftingData_at_empty_pres` + `augInterpret_at_empty_pres`
chain as `RHS_eq_canonical_msform`. -/

/-- The standard `LHS_eq_canonical_msform`, derived from the strong-IH
    `LHS_eq_canonical_msform_pres` at `pres = (fun _ => [])`. Mirrors
    `RHS_eq_canonical_msform`'s derivation pattern. -/
private theorem LHS_eq_canonical_msform
    (T : Planar α) (F_A pre_T_B pre_FA_B C : List (Planar α)) :
    ((insertion T pre_T_B).bind fun T_ins =>
        (insertionForest F_A pre_FA_B).bind fun F_ins =>
          insertionForest (T_ins :: F_ins) C).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    ((enumGraftingData T F_A pre_T_B pre_FA_B C.length).map
        (fun gd => interpret T gd C)).map
      (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- Specialize LHS_eq_canonical_msform_pres at pres = (fun _ => []).
  have h := LHS_eq_canonical_msform_pres T F_A pre_T_B pre_FA_B (fun _ => []) C
  -- Reduce LHS_form @ empty to standard LHS:
  --   - insertionForest pre_T_B [] = {pre_T_B} (then singleton_bind substitutes).
  --   - pre_T_B' ++ [] = pre_T_B' (List.append_nil cleans up pres .T_orig zero append).
  --   - Same for FA-side.
  simp only [insertionForest_nil_guests, List.append_nil, Multiset.singleton_bind] at h
  rw [h]
  -- Bridge canonical (augInterpret + enumAugGraftingData at empty pres) to
  -- standard interpret + enumGraftingData via the empty-pres bridges (same
  -- pattern as `RHS_eq_canonical_msform`'s closing block).
  congr 1
  rw [enumAugGraftingData_at_empty_pres T F_A pre_T_B pre_FA_B C.length, Multiset.map_map]
  refine Multiset.map_congr rfl fun gd _ => ?_
  rw [Function.comp_apply, augInterpret_at_empty_pres]
  show interpret T (agdToGd (gdToAgdEmpty gd)) C = interpret T gd C
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

/-- A3.3 cons-case sorry-fence — closes via composition of two canonical-form
    bridges:
    1. `LHS_eq_canonical_msform` (§1.13): LHS = canonical, derived from
       strong-IH `LHS_eq_canonical_msform_pres` (§1.12, sorry-fenced cons case).
    2. `RHS_eq_canonical_msform` (§1.11.7): canonical = RHS_alphaBind form,
       derived from sorry-free strong-IH `RHS_eq_canonical_msform_pres`.

    The substantive content is now ENTIRELY in the cons case of
    `LHS_eq_canonical_msform_pres` (§1.12). -/
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
  rw [LHS_eq_canonical_msform T F_A pre_T_B pre_FA_B (c :: rest),
      ← RHS_eq_canonical_msform T F_A pre_T_B pre_FA_B (c :: rest)]

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
