/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
import Mathlib.Data.Multiset.Powerset

set_option autoImplicit false

/-!
# Host-append decomposition for planar multi-tree insertion

The planar substrate for `Nonplanar.insertionMultiset_add_host`:
multi-graft into a concatenated host list `host_A ++ host_B`
decomposes as a sum over boolean assignments of guests to either
`host_A` or `host_B`, with each side recursively multi-grafted
independently.

## Architecture

The proof introduces `hostBucketSum`, a Multiset aggregator analogous
to `forestPairSum` but splitting guests by a 2-bucket partition between
two arbitrary host forests (rather than between a head tree and its
tail). The bridge `hostBucketSum_eq_insertionForest` is proved by
induction on `host_A`.

This is the planar-level companion to the `Nonplanar.insertionMultiset_add_host`
combinatorial identity used in `GrossmanLarsonAssoc.lean`'s
Oudom-Guin Prop 2.7.iii proof.

## Status

`[UPSTREAM]` candidate. **Sorry-free**.
-/

namespace RootedTree

namespace Planar

namespace Pathed

variable {α : Type*}

/-! ## §1: `hostBucketSum` aggregator

Splits a list of guest trees into two buckets — those destined for
`host_A` and those destined for `host_B` — by accumulating boolean
choices for each remaining guest. At the leaf, the cartesian product of
each side's `insertionForest` is concatenated. -/

/-- Two-host aggregator: at the leaf (no remaining guests), produce
    the cartesian product of `insertionForest host_A pre_A` and
    `insertionForest host_B pre_B`, joined by list concatenation.
    At a cons, bind over `[true, false]` and extend either bucket. -/
private def hostBucketSum (host_A host_B : List (Planar α)) :
    List (Planar α) → List (Planar α) → List (Planar α) →
      Multiset (List (Planar α))
  | pre_A, pre_B, []       =>
      ((insertionForest host_A pre_A) ×ˢ (insertionForest host_B pre_B)).map
        fun p => p.fst ++ p.snd
  | pre_A, pre_B, x :: rest =>
      (Multiset.ofList [true, false]).bind fun b =>
        if b then hostBucketSum host_A host_B (pre_A ++ [x]) pre_B rest
        else hostBucketSum host_A host_B pre_A (pre_B ++ [x]) rest

private theorem hostBucketSum_nil_remaining (host_A host_B : List (Planar α))
    (pre_A pre_B : List (Planar α)) :
    hostBucketSum host_A host_B pre_A pre_B [] =
      ((insertionForest host_A pre_A) ×ˢ (insertionForest host_B pre_B)).map
        fun p => p.fst ++ p.snd := by
  unfold hostBucketSum; rfl

private theorem hostBucketSum_cons_remaining (host_A host_B : List (Planar α))
    (pre_A pre_B : List (Planar α)) (x : Planar α) (rest : List (Planar α)) :
    hostBucketSum host_A host_B pre_A pre_B (x :: rest) =
      (Multiset.ofList [true, false]).bind fun b =>
        if b then hostBucketSum host_A host_B (pre_A ++ [x]) pre_B rest
        else hostBucketSum host_A host_B pre_A (pre_B ++ [x]) rest := rfl

/-- Assignment rewrite: `hostBucketSum` accumulating into `pre_A`/`pre_B`
    over remaining guests `Ts` equals the sum over `[true, false]`-
    assignments of `Ts` of `hostBucketSum` on empty remaining with the
    accumulators augmented by the partition. Mirrors
    `forestPairSum_assignment_rewrite` in `Insertion.lean`. -/
private theorem hostBucketSum_assignment_rewrite
    (host_A host_B : List (Planar α)) :
    ∀ (pre_A pre_B Ts : List (Planar α)),
    hostBucketSum host_A host_B pre_A pre_B Ts =
      (Multiset.ofList (listChoices [true, false] Ts.length)).bind fun α =>
        hostBucketSum host_A host_B
          (pre_A ++ (Ts.zip α).filterMap (fun p => if p.snd then some p.fst else none))
          (pre_B ++ (Ts.zip α).filterMap (fun p => if p.snd then none else some p.fst))
          [] := by
  intro pre_A pre_B Ts
  induction Ts generalizing pre_A pre_B with
  | nil =>
    simp [listChoices_zero, List.filterMap_nil, List.append_nil]
  | cons x rest ih =>
    rw [hostBucketSum_cons_remaining]
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
      refine Multiset.bind_congr fun α _ => ?_
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
      refine Multiset.bind_congr fun α _ => ?_
      rw [List.append_assoc, List.singleton_append]
      rfl

/-! ## §2: Base case — `hostBucketSum [] host_B [] [] guests = insertionForest host_B guests`

When `host_A = []`, only the "all-false" boolean assignment can
produce a non-zero `insertionForest [] _ ≠ 0`, since
`insertionForest [] _ = 0` whenever the second argument is non-empty.
The all-false path gives `({[]} ×ˢ insertionForest host_B guests).map (++)`,
which collapses to `insertionForest host_B guests`. -/

/-- When `pre_A = []` is non-empty, the leaf of `hostBucketSum []` is
    `0`. Helper for the base case of the bridge. -/
private theorem hostBucketSum_nil_A_nonempty_pre_A_zero
    (host_B : List (Planar α)) (a : Planar α) (pre_A pre_B : List (Planar α)) :
    hostBucketSum ([] : List (Planar α)) host_B (a :: pre_A) pre_B [] = 0 := by
  rw [hostBucketSum_nil_remaining]
  rw [insertionForest_empty_host_nonempty_guests]
  rw [Multiset.zero_product]
  rfl

/-- `hostBucketSum [] host_B (a :: pre_A) pre_B Ts = 0` for any
    remaining `Ts`. By induction on `Ts`, the recursive cases stay in
    the "pre_A non-empty" regime. -/
private theorem hostBucketSum_nil_A_pre_A_cons_zero
    (host_B : List (Planar α)) :
    ∀ (a : Planar α) (pre_A pre_B Ts : List (Planar α)),
    hostBucketSum ([] : List (Planar α)) host_B (a :: pre_A) pre_B Ts = 0 := by
  intro a pre_A pre_B Ts
  induction Ts generalizing pre_A pre_B with
  | nil => exact hostBucketSum_nil_A_nonempty_pre_A_zero host_B a pre_A pre_B
  | cons x rest ih =>
    rw [hostBucketSum_cons_remaining]
    refine (Multiset.bind_congr (g := fun _ => (0 : Multiset _)) ?_).trans
      (Multiset.bind_zero _)
    intro b _
    cases b
    · rw [if_neg (by decide : (false : Bool) ≠ true)]
      exact ih pre_A (pre_B ++ [x])
    · rw [if_pos rfl]
      -- pre_A ++ [x] = a :: (pre_A ++ [x]) when pre_A is non-empty,
      -- or a :: [x] when pre_A = []. Use `cons_append`.
      show hostBucketSum [] host_B (a :: pre_A ++ [x]) pre_B rest = 0
      rw [List.cons_append]
      exact ih (pre_A ++ [x]) pre_B

/-- General base-case lemma: `hostBucketSum [] host_B [] pre_B remaining` reduces to
    `insertionForest host_B (pre_B ++ remaining)`. By induction on `remaining`:
    the "true" branch contributes 0 (pre_A becomes non-empty), the "false"
    branch advances `pre_B` by one element. -/
private theorem hostBucketSum_nil_A_pre_B_remaining
    (host_B : List (Planar α)) :
    ∀ (pre_B remaining : List (Planar α)),
    hostBucketSum ([] : List (Planar α)) host_B [] pre_B remaining =
      insertionForest host_B (pre_B ++ remaining) := by
  intro pre_B remaining
  induction remaining generalizing pre_B with
  | nil =>
    rw [hostBucketSum_nil_remaining, insertionForest_nil_nil]
    -- {[]} ×ˢ insertionForest host_B pre_B = (insertionForest host_B pre_B).map (Prod.mk [])
    rw [show (({[]} : Multiset (List (Planar α))) ×ˢ insertionForest host_B pre_B)
            = (insertionForest host_B pre_B).map (Prod.mk []) from by
          rw [show ({[]} : Multiset (List (Planar α))) = ([] : List (Planar α)) ::ₘ 0 from rfl]
          rw [Multiset.cons_product, Multiset.zero_product, add_zero]]
    rw [Multiset.map_map]
    show (insertionForest host_B pre_B).map (fun x => [] ++ x) = insertionForest host_B (pre_B ++ [])
    rw [List.append_nil]
    simp
  | cons x rest ih =>
    rw [hostBucketSum_cons_remaining]
    -- bind over [t,f]
    show ((Multiset.ofList [true, false]).bind _) = _
    rw [show (Multiset.ofList [true, false] : Multiset Bool) =
            (true ::ₘ false ::ₘ 0) from by
          rw [show ([true, false] : List Bool) = true :: false :: ([] : List Bool) from rfl]
          rfl]
    rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [if_pos rfl, if_neg (by decide : (false : Bool) ≠ true)]
    -- True branch: pre_A = [] ++ [x] = [x] ≠ [], so it's 0.
    rw [show ([] : List (Planar α)) ++ [x] = x :: [] from rfl]
    rw [hostBucketSum_nil_A_pre_A_cons_zero host_B x [] pre_B rest]
    rw [zero_add]
    -- False branch: hostBucketSum [] host_B [] (pre_B ++ [x]) rest = (IH) insertionForest host_B (pre_B ++ [x] ++ rest)
    rw [ih (pre_B ++ [x])]
    -- Goal: insertionForest host_B (pre_B ++ [x] ++ rest) = insertionForest host_B (pre_B ++ (x :: rest))
    congr 1
    rw [List.append_assoc]
    rfl

/-- Bridge base case: `hostBucketSum [] host_B [] [] guests = insertionForest host_B guests`. -/
private theorem hostBucketSum_nil_A
    (host_B guests : List (Planar α)) :
    hostBucketSum ([] : List (Planar α)) host_B [] [] guests =
      insertionForest host_B guests := by
  have := hostBucketSum_nil_A_pre_B_remaining host_B [] guests
  rw [List.nil_append] at this
  exact this

/-! ## §3: 3-bucket aggregator and the full bridge

The headline planar identity. Combined with the Nonplanar lift below
(via `Quotient.out` + host-Perm invariance lifted through `Nonplanar.mk`),
this yields the substrate for `Nonplanar.insertionMultiset_add_host`.

The proof goes by induction on `host_A`. The base case (`host_A = []`)
is `hostBucketSum_nil_A` (above). The inductive case `host_A = T :: F_A`
proceeds via a 3-bucket aggregator `hostTripleSum` that explicitly
partitions guests into three buckets `{T-bucket, F_A-bucket, host_B-bucket}`.
We then prove:

- `hostBucketSum_eq_hostTripleSum`: LHS (the 2-step `hostBucketSum`)
   equals the 3-bucket sum (reorganizing "A-vs-B then T-vs-F_A within A").
- `insertionForest_cons_append_eq_hostTripleSum`: RHS (the
   `insertionForest` over `T :: (F_A ++ host_B)`) equals the 3-bucket
   sum (using the outer IH on `F_A` to convert
   `insertionForest (F_A ++ host_B) Y` into `hostBucketSum F_A host_B`,
   reorganizing "T-vs-rest then F_A-vs-host_B within rest"). -/

/-- 3-bucket aggregator: each remaining guest gets assigned to one of
    three buckets — T-bucket (eventually grafted at vertices of single
    tree T), F_A-bucket (eventually multi-grafted into forest F_A), or
    host_B-bucket (eventually multi-grafted into forest host_B). At the
    leaf, three independent `insertion`/`insertionForest` computations
    combine via list concatenation `T' :: F' ++ B`. -/
private def hostTripleSum (T : Planar α) (F_A host_B : List (Planar α)) :
    List (Planar α) → List (Planar α) → List (Planar α) →
      List (Planar α) → Multiset (List (Planar α))
  | pre_T, pre_FA, pre_B, [] =>
      (insertion T pre_T).bind fun T' =>
        (insertionForest F_A pre_FA).bind fun F' =>
          (insertionForest host_B pre_B).map fun B => T' :: F' ++ B
  | pre_T, pre_FA, pre_B, x :: rest =>
      hostTripleSum T F_A host_B (pre_T ++ [x]) pre_FA pre_B rest
        + hostTripleSum T F_A host_B pre_T (pre_FA ++ [x]) pre_B rest
        + hostTripleSum T F_A host_B pre_T pre_FA (pre_B ++ [x]) rest

private theorem hostTripleSum_nil_remaining
    (T : Planar α) (F_A host_B pre_T pre_FA pre_B : List (Planar α)) :
    hostTripleSum T F_A host_B pre_T pre_FA pre_B [] =
      (insertion T pre_T).bind fun T' =>
        (insertionForest F_A pre_FA).bind fun F' =>
          (insertionForest host_B pre_B).map fun B => T' :: F' ++ B := by
  unfold hostTripleSum; rfl

private theorem hostTripleSum_cons_remaining
    (T : Planar α) (F_A host_B pre_T pre_FA pre_B : List (Planar α))
    (x : Planar α) (rest : List (Planar α)) :
    hostTripleSum T F_A host_B pre_T pre_FA pre_B (x :: rest) =
      hostTripleSum T F_A host_B (pre_T ++ [x]) pre_FA pre_B rest
        + hostTripleSum T F_A host_B pre_T (pre_FA ++ [x]) pre_B rest
        + hostTripleSum T F_A host_B pre_T pre_FA (pre_B ++ [x]) rest := rfl

/-- Helper: `(M ×ˢ N).map (uncurry ++) = M.bind fun a => N.map fun b => a ++ b`. -/
private theorem product_map_append_eq_bind_map
    (M N : Multiset (List (Planar α))) :
    (M ×ˢ N).map (fun p => p.fst ++ p.snd) =
      M.bind fun a => N.map fun b => a ++ b := by
  show (Multiset.product M N).map (fun p => p.fst ++ p.snd) =
       M.bind fun a => N.map fun b => a ++ b
  unfold Multiset.product
  rw [Multiset.map_bind]
  refine Multiset.bind_congr fun a _ => ?_
  rw [Multiset.map_map]
  rfl

/-- Uniform decomposition of `insertionForest (T :: F) X` over `[true, false]`-assignments
    of `X`'s elements to the T-bucket or F-bucket. Works for empty X via singleton bind. -/
private theorem insertionForest_cons_assignment (T : Planar α)
    (F : List (Planar α)) (X : List (Planar α)) :
    insertionForest (T :: F) X =
      (Multiset.ofList (listChoices [true, false] X.length)).bind fun α =>
        (insertion T
            ((X.zip α).filterMap (fun p => if p.snd then some p.fst else none))).bind
          fun T' =>
            (insertionForest F
                ((X.zip α).filterMap (fun p => if p.snd then none else some p.fst))).map
              fun F' => T' :: F' := by
  match X with
  | [] =>
    rw [insertionForest_cons_host_nil_guests]
    -- listChoices [t,f] 0 = [[]], so ofList = {[]}
    simp only [List.length_nil, listChoices_zero, List.zip_nil_right, List.filterMap_nil,
               Multiset.coe_singleton, Multiset.singleton_bind]
    rw [insertion_nil_guests, insertionForest_nil_guests]
    rw [Multiset.singleton_bind, Multiset.map_singleton]
  | x :: rest =>
    exact insertionForest_cons_cons T F x rest

/-- **Lemma X (listChoices append-decomposition)**: enumerating length-`(n+1)`
    bit vectors and applying `g` equals enumerating length-`n` bit vectors and
    summing `g (α ++ [true]) + g (α ++ [false])`. Multiset-level, NOT list-level. -/
private theorem listChoices_succ_append_bind {γ : Type*}
    (n : Nat) (g : List Bool → Multiset γ) :
    (Multiset.ofList (listChoices [true, false] (n + 1))).bind g =
      (Multiset.ofList (listChoices [true, false] n)).bind fun a =>
        g (a ++ [true]) + g (a ++ [false]) := by
  induction n generalizing g with
  | zero =>
    -- listChoices [t,f] 1 = [[t], [f]], listChoices [t,f] 0 = [[]]
    show (Multiset.ofList ([[true], [false]] : List (List Bool))).bind g =
         (Multiset.ofList ([[]] : List (List Bool))).bind fun a => g (a ++ [true]) + g (a ++ [false])
    rw [show (Multiset.ofList [[true], [false]] : Multiset (List Bool)) =
            ([true] ::ₘ [false] ::ₘ 0) from rfl]
    rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [show (Multiset.ofList [([] : List Bool)] : Multiset (List Bool)) =
            (([] : List Bool) ::ₘ 0) from rfl]
    rw [Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rfl
  | succ n ih =>
    -- LHS = bind over listChoices [t,f] (n+2) of g
    --     = bind v over [t,f]: bind α' over listChoices [t,f] (n+1): g (v :: α')
    -- IH gives: bind α' over listChoices [t,f] (n+1): g_v (α') = bind α over listChoices [t,f] n: g_v (α ++ [t]) + g_v (α ++ [f])
    -- where g_v α' = g (v :: α'). So:
    -- LHS = bind v: bind α over listChoices [t,f] n: g (v :: α ++ [t]) + g (v :: α ++ [f])
    -- After bind_bind: = bind α: bind v: g (v :: α ++ [t]) + g (v :: α ++ [f])
    --                = bind α: g (t :: α ++ [t]) + g (t :: α ++ [f]) + g (f :: α ++ [t]) + g (f :: α ++ [f])
    --
    -- RHS = bind α' over listChoices [t,f] (n+1): g (α' ++ [t]) + g (α' ++ [f])
    --     = bind v: bind α over listChoices [t,f] n: g (v :: α ++ [t]) + g (v :: α ++ [f])
    -- After bind_bind: = same as LHS.
    have key : ∀ (h : List Bool → Multiset γ),
        (Multiset.ofList (listChoices [true, false] (n + 2))).bind h =
          (Multiset.ofList [true, false]).bind fun v =>
            (Multiset.ofList (listChoices [true, false] (n + 1))).bind fun a => h (v :: a) := by
      intro h
      show (Multiset.ofList (listChoices [true, false] (n + 2))).bind h =
           (Multiset.ofList [true, false]).bind fun v =>
             (Multiset.ofList (listChoices [true, false] (n + 1))).bind fun a => h (v :: a)
      rw [show (n + 2) = (n + 1) + 1 from rfl, listChoices_succ]
      rw [show (Multiset.ofList ([true, false].flatMap fun v =>
                  (listChoices [true, false] (n + 1)).map (v :: ·)) :
                Multiset (List Bool)) =
              (Multiset.ofList [true, false]).bind fun v =>
                Multiset.ofList ((listChoices [true, false] (n + 1)).map (v :: ·))
              from by rw [← Multiset.coe_bind]]
      rw [Multiset.bind_assoc]
      refine Multiset.bind_congr fun v _ => ?_
      rw [show (Multiset.ofList ((listChoices [true, false] (n + 1)).map (v :: ·)) :
                Multiset (List Bool)) =
              (Multiset.ofList (listChoices [true, false] (n + 1))).map (v :: ·)
              from rfl]
      rw [Multiset.bind_map]
    rw [key g]
    -- Apply IH on the inner bind for each v:
    conv_lhs =>
      rhs; ext v
      rw [ih (fun a => g (v :: a))]
    -- Now LHS = bind v: bind α over n: g (v :: (α ++ [t])) + g (v :: (α ++ [f]))
    -- Reformulate: g (v :: α ++ [t]) = g (v :: (α ++ [t]))  -- same thing by associativity of cons-then-append
    -- Want RHS form: bind α over n: bind v: g ((v :: α) ++ [t]) + g ((v :: α) ++ [f])
    -- = bind α: bind v: g (v :: α ++ [t]) + g (v :: α ++ [f])  -- by cons_append
    -- These will agree after bind_bind.
    rw [Multiset.bind_bind]
    -- LHS now: bind α over n: bind v: g (v :: (α ++ [t])) + g (v :: (α ++ [f]))
    -- RHS:    bind α' over listChoices [t,f] (n+1): g (α' ++ [t]) + g (α' ++ [f])
    --       = bind v: bind α over n: g (v :: α ++ [t]) + g (v :: α ++ [f])    -- by key
    --       = bind α over n: bind v: g (v :: α ++ [t]) + g (v :: α ++ [f])    -- bind_bind
    -- These should match. Let me compute RHS:
    conv_rhs =>
      rhs; ext a
      rw [show g (a ++ [true]) + g (a ++ [false]) =
              g (a ++ [true]) + g (a ++ [false]) from rfl]
    rw [show (Multiset.ofList (listChoices [true, false] (n + 1))) =
            (Multiset.ofList [true, false]).bind fun v =>
              (Multiset.ofList (listChoices [true, false] n)).map (v :: ·)
            from by
      rw [show (n + 1) = n + 1 from rfl, listChoices_succ]
      rw [← Multiset.coe_bind]
      rfl]
    -- RHS = (bind v: (ofList listChoices n).map (v :: ·)).bind fun a => g (a ++ [t]) + g (a ++ [f])
    rw [Multiset.bind_assoc]
    -- RHS = bind v: ((ofList listChoices n).map (v :: ·)).bind fun a => g (a ++ [t]) + g (a ++ [f])
    conv_rhs =>
      rhs; ext v
      rw [Multiset.bind_map]
    -- RHS = bind v: bind α over n: g ((v :: α) ++ [t]) + g ((v :: α) ++ [f])
    rw [Multiset.bind_bind]
    refine Multiset.bind_congr fun a _ => ?_
    refine Multiset.bind_congr fun v _ => ?_
    -- Goal: g (v :: (a ++ [true])) + g (v :: (a ++ [false])) = g ((v :: a) ++ [true]) + g ((v :: a) ++ [false])
    rfl

/-- Length lemma: every element of `listChoices xs n` has length exactly `n`.
    Used in the cons case of `hostBucketSum_eq_hostTripleSum_aux` to invoke
    `List.zip_append`. -/
private theorem mem_listChoices_length {β : Type*} (xs : List β) :
    ∀ (n : Nat) (α : List β), α ∈ listChoices xs n → α.length = n := by
  intro n
  induction n with
  | zero =>
    intro α hα
    rw [listChoices_zero, List.mem_singleton] at hα
    rw [hα]; rfl
  | succ k ih =>
    intro α hα
    rw [listChoices_succ, List.mem_flatMap] at hα
    obtain ⟨_v, _hv, hvα⟩ := hα
    rw [List.mem_map] at hvα
    obtain ⟨α', hα', heq⟩ := hvα
    rw [← heq, List.length_cons, ih α' hα']

/-- **Lemma A**: `hostBucketSum (T :: F_A) host_B pre_A pre_B remaining` equals
    the sum over `[true, false]`-splittings of `pre_A` into a T-piece and an
    F_A-piece of `hostTripleSum T F_A host_B pre_T pre_FA pre_B remaining`.
    By induction on `remaining`. -/
private theorem hostBucketSum_eq_hostTripleSum_aux
    (T : Planar α) (F_A host_B : List (Planar α)) :
    ∀ (pre_A pre_B remaining : List (Planar α)),
    hostBucketSum (T :: F_A) host_B pre_A pre_B remaining =
      (Multiset.ofList (listChoices [true, false] pre_A.length)).bind fun α =>
        hostTripleSum T F_A host_B
          ((pre_A.zip α).filterMap (fun p => if p.snd then some p.fst else none))
          ((pre_A.zip α).filterMap (fun p => if p.snd then none else some p.fst))
          pre_B remaining := by
  intro pre_A pre_B remaining
  induction remaining generalizing pre_A pre_B with
  | nil =>
    -- LHS = hostBucketSum (T :: F_A) host_B pre_A pre_B [] = leaf
    -- RHS = bind α: hostTripleSum T F_A host_B (zip α ft) (zip α ff) pre_B [] = bind α: leaf-of-triple
    rw [hostBucketSum_nil_remaining]
    -- LHS: (insertionForest (T :: F_A) pre_A ×ˢ insertionForest host_B pre_B).map (++)
    rw [product_map_append_eq_bind_map]
    -- LHS: (insertionForest (T :: F_A) pre_A).bind T_F => (insertionForest host_B pre_B).map (T_F ++ ·)
    rw [insertionForest_cons_assignment]
    -- LHS: (bind α: (insertion T (zip α ft)).bind T' => (insertionForest F_A (zip α ff)).map (T' :: ·)).bind T_F => ...
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun a _ => ?_
    rw [hostTripleSum_nil_remaining]
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun T' _ => ?_
    -- Goal: ((insertionForest F_A (zip α ff)).map (T' :: ·)).bind T_F => (insertionForest host_B pre_B).map (T_F ++ ·)
    --     = (insertionForest F_A (zip α ff)).bind F' => (insertionForest host_B pre_B).map fun B => T' :: F' ++ B
    rw [Multiset.bind_map]
    -- Resulting goal: (insertionForest F_A (zip α ff)).bind fun F' => (insertionForest host_B pre_B).map ((T' :: F') ++ ·)
    --             vs (insertionForest F_A (zip α ff)).bind fun F' => (insertionForest host_B pre_B).map fun B => T' :: F' ++ B
    -- These differ only by (T' :: F') ++ B vs T' :: F' ++ B  — same by List.cons_append (definitional).
  | cons x rest ih =>
    -- LHS = hostBucketSum cons: bind [t,f] -> if true: hostBucketSum (T :: F_A) host_B (pre_A ++ [x]) pre_B rest
    --                                       if false: hostBucketSum (T :: F_A) host_B pre_A (pre_B ++ [x]) rest
    rw [hostBucketSum_cons_remaining]
    -- RHS: bind α (over |pre_A|): hostTripleSum T F_A host_B (zip α ft) (zip α ff) pre_B (x :: rest)
    --    = bind α: hostTripleSum T F_A host_B ... ... ... (x :: rest)
    --    = bind α: (hostTripleSum T F_A host_B (... ++ [x]) ... pre_B rest)
    --             + (hostTripleSum T F_A host_B ... (... ++ [x]) pre_B rest)
    --             + (hostTripleSum T F_A host_B ... ... (pre_B ++ [x]) rest)
    -- so RHS = (bind α: triple T-add) + (bind α: triple FA-add) + (bind α: triple B-add)
    --        = "(T or FA bucket within pre_A's split, then add x to it) — but x is new guest"
    -- Wait: in the cons of remaining, x is consumed; pre_A doesn't change.
    -- So actually for adding x to T-bucket: pre_T ← pre_T ++ [x]
    -- For F_A-bucket: pre_FA ← pre_FA ++ [x]
    -- For B-bucket: pre_B ← pre_B ++ [x]
    -- After distributing, RHS becomes a bind over (α : assigns existing pre_A) of three additions (x → T, x → F_A, or x → B).
    -- Two of these (T-add, F_A-add) extend the SAME α-splitting of pre_A, but with x appended on different sides.
    -- Equivalently: an (|pre_A| + 1)-length α' that decomposes as α (on pre_A) appended with one bit for x.
    -- Therefore: bind α (over |pre_A|): triple(T-add) + triple(F_A-add)
    --         = bind α' (over |pre_A| + 1): triple(zip α' ft, zip α' ff, pre_B, rest)
    --         = bind α' (over |pre_A ++ [x]|): triple(zip α' ft on (pre_A ++ [x]), zip α' ff on (pre_A ++ [x]), pre_B, rest)
    -- That's exactly `ih (pre_A ++ [x]) pre_B`.
    -- Similarly the B-add branch matches `ih pre_A (pre_B ++ [x])` but with pre_A's α-splitting on |pre_A| unchanged.
    -- Hmm but in `ih pre_A (pre_B ++ [x])`, the α is over |pre_A|, same as RHS.
    -- Specifically:
    --   LHS true-branch (after ih (pre_A ++ [x]) pre_B):
    --     bind α' (over |pre_A| + 1): hostTripleSum (zip α' ft on (pre_A ++ [x])) (zip α' ff on ...) pre_B rest
    --   RHS T-add part: bind α (over |pre_A|): hostTripleSum (zip α ft on pre_A ++ [x]) (zip α ff on pre_A) pre_B rest
    --   RHS F_A-add part: bind α (over |pre_A|): hostTripleSum (zip α ft on pre_A) (zip α ff on pre_A ++ [x]) pre_B rest
    -- The combination of RHS T-add + F_A-add over all α should equal the bind α' over |pre_A| + 1 case.
    -- Because (α ++ [true]) handles T-add, (α ++ [false]) handles F_A-add.
    -- Reduce bind over [t, f]
    rw [show (Multiset.ofList [true, false] : Multiset Bool) = (true ::ₘ false ::ₘ 0) from rfl]
    rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
    rw [if_pos rfl, if_neg (by decide : (false : Bool) ≠ true)]
    -- LHS = hostBucketSum (T :: F_A) host_B (pre_A ++ [x]) pre_B rest
    --     + hostBucketSum (T :: F_A) host_B pre_A (pre_B ++ [x]) rest
    rw [ih (pre_A ++ [x]) pre_B, ih pre_A (pre_B ++ [x])]
    -- LHS = (bind α' over (pre_A ++ [x]).length: hostTripleSum on (pre_A ++ [x]) (pre_B) rest)
    --     + (bind α over pre_A.length: hostTripleSum on (pre_A) (pre_B ++ [x]) rest)
    rw [show (pre_A ++ [x]).length = pre_A.length + 1 from by simp]
    -- Apply listChoices_succ_append_bind to first piece
    rw [listChoices_succ_append_bind pre_A.length]
    -- Combine the two binds via ← bind_add
    rw [← Multiset.bind_add]
    -- LHS = bind assn: (g(assn ++ [t]) + g(assn ++ [f])) + (hostTripleSum on (pre_A) (pre_B ++ [x]) rest)
    -- where g assn' = hostTripleSum on (pre_A ++ [x]).zip assn' ft, ff parts
    -- Now match per-assn with RHS
    apply Multiset.bind_congr
    intros assn hassn
    -- Get assn.length = pre_A.length
    have hassn_len : assn.length = pre_A.length := by
      have hassn' : assn ∈ listChoices [true, false] pre_A.length := by
        rwa [show (Multiset.ofList (listChoices [true, false] pre_A.length) :
                Multiset (List Bool)) =
                ((listChoices [true, false] pre_A.length : List _) : Multiset _) from rfl,
             Multiset.mem_coe] at hassn
      exact mem_listChoices_length [true, false] pre_A.length assn hassn'
    -- Apply hostTripleSum_cons_remaining on RHS (the (x :: rest) form)
    rw [hostTripleSum_cons_remaining]
    -- Compute zip and filterMap on (pre_A ++ [x]).zip (assn ++ [b])
    have hzip_t : (pre_A ++ [x]).zip (assn ++ [true]) = pre_A.zip assn ++ [(x, true)] := by
      rw [List.zip_append hassn_len.symm]; rfl
    have hzip_f : (pre_A ++ [x]).zip (assn ++ [false]) = pre_A.zip assn ++ [(x, false)] := by
      rw [List.zip_append hassn_len.symm]; rfl
    -- Substitute and simplify both summands of g
    rw [hzip_t, hzip_f]
    -- Reduce the singleton filterMap using `if_pos rfl` and `if_neg`:
    -- For (x, true): filter_true → some x → [x]; filter_false → none → [].
    -- For (x, false): filter_true → none → []; filter_false → some x → [x].
    have h_true_t : ([(x, true)] : List (Planar α × Bool)).filterMap
        (fun p => if p.snd then some p.fst else none) = [x] := by
      simp
    have h_true_f : ([(x, true)] : List (Planar α × Bool)).filterMap
        (fun p => if p.snd then none else some p.fst) = [] := by
      simp
    have h_false_t : ([(x, false)] : List (Planar α × Bool)).filterMap
        (fun p => if p.snd then some p.fst else none) = [] := by
      simp
    have h_false_f : ([(x, false)] : List (Planar α × Bool)).filterMap
        (fun p => if p.snd then none else some p.fst) = [x] := by
      simp
    rw [List.filterMap_append, List.filterMap_append, List.filterMap_append, List.filterMap_append,
        h_true_t, h_true_f, h_false_t, h_false_f, List.append_nil, List.append_nil]

/-! ## §4: Connecting `hostTripleSum` with `insertion T` ∘ `hostBucketSum F_A host_B`

Lemma A reduces `hostBucketSum (T :: F_A) host_B [] [] guests` to
`hostTripleSum T F_A host_B [] [] [] guests`. To complete the bridge, we
need `hostTripleSum T F_A host_B [] [] [] guests = insertionForest (T :: (F_A ++ host_B)) guests`.

Approach: generalize to `hostTripleSum_T_split`:
```
hostTripleSum T F_A host_B pre_T pre_FA pre_B remaining =
  bind α over remaining.length:
    (insertion T (pre_T ++ filter_true remaining α)).bind T' =>
      (hostBucketSum F_A host_B pre_FA pre_B (filter_false remaining α)).map (T' :: ·)
```
Then for `pre_T = pre_FA = pre_B = []`, combine with the IH `hostBucketSum F_A host_B = insertionForest (F_A ++ host_B)` to close the bridge.

Requires `listChoices_succ_cons_bind` (the cons-prepending analog of
`listChoices_succ_append_bind`). -/

/-- Cons-prepending analog of `listChoices_succ_append_bind`. The bit
    for the cons-front guest goes at the FRONT of α rather than the back. -/
private theorem listChoices_succ_cons_bind {γ : Type*}
    (n : Nat) (g : List Bool → Multiset γ) :
    (Multiset.ofList (listChoices [true, false] (n + 1))).bind g =
      (Multiset.ofList (listChoices [true, false] n)).bind fun α =>
        g (true :: α) + g (false :: α) := by
  rw [listChoices_succ]
  rw [show (Multiset.ofList ([true, false].flatMap fun v =>
              (listChoices [true, false] n).map (v :: ·)) :
            Multiset (List Bool)) =
          (Multiset.ofList [true, false]).bind fun v =>
            Multiset.ofList ((listChoices [true, false] n).map (v :: ·))
          from by rw [← Multiset.coe_bind]]
  rw [Multiset.bind_assoc]
  rw [show (Multiset.ofList [true, false] : Multiset Bool) = (true ::ₘ false ::ₘ 0) from rfl]
  rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  rw [show (Multiset.ofList ((listChoices [true, false] n).map (true :: ·)) :
            Multiset (List Bool)) =
          (Multiset.ofList (listChoices [true, false] n)).map (true :: ·) from rfl]
  rw [show (Multiset.ofList ((listChoices [true, false] n).map (false :: ·)) :
            Multiset (List Bool)) =
          (Multiset.ofList (listChoices [true, false] n)).map (false :: ·) from rfl]
  rw [Multiset.bind_map, Multiset.bind_map]
  rw [← Multiset.bind_add]

/-- **Generalized cross-form**: `hostTripleSum` recasts as a per-guest decision
    of "T-bucket vs not-T-bucket", with the not-T portion handled by `hostBucketSum
    F_A host_B` (which itself is a per-not-T-guest 2-way decision F_A vs host_B). -/
private theorem hostTripleSum_T_split (T : Planar α) (F_A host_B : List (Planar α)) :
    ∀ (pre_T pre_FA pre_B remaining : List (Planar α)),
    hostTripleSum T F_A host_B pre_T pre_FA pre_B remaining =
      (Multiset.ofList (listChoices [true, false] remaining.length)).bind fun α =>
        (insertion T
            (pre_T ++ (remaining.zip α).filterMap
              (fun p => if p.snd then some p.fst else none))).bind fun T' =>
          (hostBucketSum F_A host_B pre_FA pre_B
            ((remaining.zip α).filterMap (fun p => if p.snd then none else some p.fst))).map
              fun L => T' :: L := by
  intro pre_T pre_FA pre_B remaining
  induction remaining generalizing pre_T pre_FA pre_B with
  | nil =>
    rw [hostTripleSum_nil_remaining, List.length_nil, listChoices_zero]
    show _ = (Multiset.ofList ([[]] : List (List Bool))).bind _
    rw [show (Multiset.ofList ([[]] : List (List Bool)) : Multiset (List Bool)) =
            (([] : List Bool) ::ₘ 0) from rfl]
    rw [Multiset.cons_bind, Multiset.zero_bind, add_zero]
    -- Reduce all the `[].zip []` and `List.filterMap _ []` on the RHS
    simp only [List.zip_nil_right, List.filterMap_nil, List.append_nil]
    rw [hostBucketSum_nil_remaining, product_map_append_eq_bind_map]
    refine Multiset.bind_congr fun T' _ => ?_
    rw [Multiset.map_bind]
    refine Multiset.bind_congr fun F' _ => ?_
    rw [Multiset.map_map]
    rfl
  | cons g gs ih =>
    rw [hostTripleSum_cons_remaining]
    rw [ih (pre_T ++ [g]) pre_FA pre_B,
        ih pre_T (pre_FA ++ [g]) pre_B,
        ih pre_T pre_FA (pre_B ++ [g])]
    rw [show (g :: gs).length = gs.length + 1 from rfl]
    rw [listChoices_succ_cons_bind]
    -- LHS now: 3 sums combined; RHS: bind β: F(true :: β) + F(false :: β)
    -- Combine the LHS binds via ← bind_add (twice), then prove per-β
    rw [show (∀ (s : Multiset (List Bool)) (f g h : List Bool → Multiset (List (Planar α))),
          s.bind f + s.bind g + s.bind h = s.bind fun a => f a + g a + h a) from by
        intros s f g h
        rw [← Multiset.bind_add, ← Multiset.bind_add]]
    refine Multiset.bind_congr fun β _ => ?_
    -- Per-β goal:
    -- T-add(β) + FA-add(β) + B-add(β) = F(true :: β) + F(false :: β)
    -- Compute filter_t/f on (g :: gs).zip (true :: β) and (g :: gs).zip (false :: β)
    show (insertion T ((pre_T ++ [g]) ++ (gs.zip β).filterMap
              (fun p => if p.snd then some p.fst else none))).bind (fun T' =>
            ((hostBucketSum F_A host_B pre_FA pre_B
              ((gs.zip β).filterMap (fun p => if p.snd then none else some p.fst))).map
                (fun L => T' :: L)))
        + (insertion T (pre_T ++ (gs.zip β).filterMap
              (fun p => if p.snd then some p.fst else none))).bind (fun T' =>
            ((hostBucketSum F_A host_B (pre_FA ++ [g]) pre_B
              ((gs.zip β).filterMap (fun p => if p.snd then none else some p.fst))).map
                (fun L => T' :: L)))
        + (insertion T (pre_T ++ (gs.zip β).filterMap
              (fun p => if p.snd then some p.fst else none))).bind (fun T' =>
            ((hostBucketSum F_A host_B pre_FA (pre_B ++ [g])
              ((gs.zip β).filterMap (fun p => if p.snd then none else some p.fst))).map
                (fun L => T' :: L)))
      = (insertion T (pre_T ++ ((g :: gs).zip (true :: β)).filterMap
              (fun p => if p.snd then some p.fst else none))).bind (fun T' =>
            ((hostBucketSum F_A host_B pre_FA pre_B
              (((g :: gs).zip (true :: β)).filterMap (fun p => if p.snd then none else some p.fst))).map
                (fun L => T' :: L)))
        + (insertion T (pre_T ++ ((g :: gs).zip (false :: β)).filterMap
              (fun p => if p.snd then some p.fst else none))).bind (fun T' =>
            ((hostBucketSum F_A host_B pre_FA pre_B
              (((g :: gs).zip (false :: β)).filterMap (fun p => if p.snd then none else some p.fst))).map
                (fun L => T' :: L)))
    -- Simplify (g :: gs).zip (b :: β) = (g, b) :: gs.zip β
    rw [show (g :: gs).zip (true :: β) = (g, true) :: gs.zip β from rfl,
        show (g :: gs).zip (false :: β) = (g, false) :: gs.zip β from rfl]
    -- filter_t/f on (g, b) :: ...
    simp only [List.filterMap_cons]
    show _ = (insertion T (pre_T ++ (g :: (gs.zip β).filterMap
              (fun p => if p.snd then some p.fst else none)))).bind (fun T' =>
            ((hostBucketSum F_A host_B pre_FA pre_B
              ((gs.zip β).filterMap (fun p => if p.snd then none else some p.fst))).map
                (fun L => T' :: L)))
        + (insertion T (pre_T ++ ((gs.zip β).filterMap
              (fun p => if p.snd then some p.fst else none)))).bind (fun T' =>
            ((hostBucketSum F_A host_B pre_FA pre_B
              (g :: (gs.zip β).filterMap (fun p => if p.snd then none else some p.fst))).map
                (fun L => T' :: L)))
    -- For T-add: (pre_T ++ [g]) ++ ... = pre_T ++ (g :: ...) by List.append_assoc + List.singleton_append
    rw [show (pre_T ++ [g]) ++ (gs.zip β).filterMap
              (fun p => if p.snd then some p.fst else none) =
              pre_T ++ (g :: (gs.zip β).filterMap
                (fun p => if p.snd then some p.fst else none)) from by
          rw [List.append_assoc]; rfl]
    -- For F(false :: β): hostBucketSum F_A host_B pre_FA pre_B (g :: filter_f) =
    --   hostBucketSum F_A host_B (pre_FA ++ [g]) pre_B filter_f + hostBucketSum F_A host_B pre_FA (pre_B ++ [g]) filter_f
    rw [show hostBucketSum F_A host_B pre_FA pre_B
            (g :: (gs.zip β).filterMap (fun p => if p.snd then none else some p.fst)) =
            hostBucketSum F_A host_B (pre_FA ++ [g]) pre_B
              ((gs.zip β).filterMap (fun p => if p.snd then none else some p.fst))
            + hostBucketSum F_A host_B pre_FA (pre_B ++ [g])
              ((gs.zip β).filterMap (fun p => if p.snd then none else some p.fst)) from by
          rw [hostBucketSum_cons_remaining]
          rw [show (Multiset.ofList [true, false] : Multiset Bool) = (true ::ₘ false ::ₘ 0) from rfl]
          rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
          rw [if_pos rfl, if_neg (by decide : (false : Bool) ≠ true)]]
    -- Distribute (HBS₁ + HBS₂).map (T' :: ·) = HBS₁.map (T' :: ·) + HBS₂.map (T' :: ·)
    -- and (insertion T x).bind T' => (X + Y).map ... = (insertion T x).bind T' => X.map ... + (insertion T x).bind T' => Y.map ...
    rw [show ∀ X Y : Multiset (List (Planar α)),
            (insertion T (pre_T ++ ((gs.zip β).filterMap
                (fun p => if p.snd then some p.fst else none)))).bind (fun T' =>
              ((X + Y).map (fun L => T' :: L)))
            = (insertion T (pre_T ++ ((gs.zip β).filterMap
                (fun p => if p.snd then some p.fst else none)))).bind (fun T' =>
                (X.map (fun L => T' :: L)))
              + (insertion T (pre_T ++ ((gs.zip β).filterMap
                (fun p => if p.snd then some p.fst else none)))).bind (fun T' =>
                (Y.map (fun L => T' :: L))) from by
          intros X Y
          rw [show (fun T' => ((X + Y).map (fun L => T' :: L))) =
                  (fun T' => X.map (fun L => T' :: L) + Y.map (fun L => T' :: L)) from by
                funext T'; rw [Multiset.map_add]]
          rw [Multiset.bind_add]]
    -- Now both sides are: T-add + (FA-add + B-add) = F(true :: β) + (FA-add + B-add)
    -- and they should match.
    ac_rfl

private theorem hostBucketSum_eq_insertionForest (host_A host_B guests : List (Planar α)) :
    hostBucketSum host_A host_B [] [] guests =
      insertionForest (host_A ++ host_B) guests := by
  induction host_A generalizing guests with
  | nil =>
    rw [List.nil_append]
    exact hostBucketSum_nil_A host_B guests
  | cons T F_A ih =>
    -- Apply Lemma A to reduce LHS to hostTripleSum:
    rw [hostBucketSum_eq_hostTripleSum_aux T F_A host_B [] [] guests]
    -- LHS becomes bind over listChoices [t,f] 0 = {[]}: hostTripleSum on (filter_t/f of [].zip [])
    rw [List.length_nil, listChoices_zero]
    show (Multiset.ofList ([[]] : List (List Bool))).bind _ = _
    rw [show (Multiset.ofList ([[]] : List (List Bool)) : Multiset (List Bool)) =
            (([] : List Bool) ::ₘ 0) from rfl]
    rw [Multiset.cons_bind, Multiset.zero_bind, add_zero]
    -- LHS: hostTripleSum T F_A host_B [] [] [] guests (after [].zip [] = [], filter_* on [] = [])
    show hostTripleSum T F_A host_B [] [] [] guests = insertionForest (T :: F_A ++ host_B) guests
    -- (i) Apply `hostTripleSum_T_split [] [] [] guests`:
    rw [hostTripleSum_T_split T F_A host_B [] [] [] guests]
    -- LHS = bind α: (insertion T ([] ++ filter_t)).bind T' => (hostBucketSum F_A host_B [] [] (filter_f)).map (T' :: ·)
    -- = bind α: (insertion T (filter_t)).bind T' => (hostBucketSum F_A host_B [] [] (filter_f)).map (T' :: ·)
    simp only [List.nil_append]
    -- (ii) Rewrite inner via IH `ih` (applied to filter_f result):
    conv_lhs =>
      rhs; ext α
      rhs; ext T'
      rw [ih]
    -- LHS = bind α: (insertion T (filter_t)).bind T' => (insertionForest (F_A ++ host_B) (filter_f)).map (T' :: ·)
    -- (iii) Close via `insertionForest_cons_assignment` (in reverse) for T :: (F_A ++ host_B):
    rw [show T :: F_A ++ host_B = T :: (F_A ++ host_B) from rfl]
    rw [insertionForest_cons_assignment]

/-! ## §5: Host-Perm invariance at the multiset-of-multiset level

`insertionForest` is invariant under permutation of host trees, but only at
the level where output lists are wrapped via `Multiset.ofList ∘ List.map mk`
(i.e., the level used by `Nonplanar.insertionMultiset`). The list structure
of inner outputs (which is host-position-correlated) is discarded by this
outer wrapper, allowing host trees to be permuted without changing the
multiset-of-multiset image.

The key combinatorial lemma is the swap symmetry of two adjacent host trees,
which we prove via `hostTripleSum`'s 3-bucket structure: when the F_A bucket
is a singleton `[T₂]`, swapping the T-bucket with the F_A-bucket gives a
configuration symmetric in (T₁, T₂) at the multiset level. -/

/-- Helper: `msform L = Multiset.ofList (L.map mk)`. The output level
    of `Nonplanar.insertionMultiset`'s inner map. Cons distributes:
    `msform (T :: L) = mk T ::ₘ msform L`. -/
private theorem msform_cons (T : Planar α) (L : List (Planar α)) :
    (Multiset.ofList ((T :: L).map Nonplanar.mk) : Multiset (Nonplanar α)) =
      Nonplanar.mk T ::ₘ Multiset.ofList (L.map Nonplanar.mk) := by
  rw [List.map_cons]
  rfl

/-- Symmetry of `hostTripleSum T₁ [T₂] F` under swap of T-bucket and (singleton)
    F_A-bucket, at the `Multiset.ofList ∘ List.map mk` level.

    Note the pre-arg swap: LHS's `pre_T` (for T₁) corresponds to RHS's `pre_FA`
    (still for T₁, but T₁ is now in the F_A bucket on the RHS).

    The proof goes by induction on `remaining`:
    - **nil**: leaf forms reduce via `insertionForest_singleton` (since F_A is a
      singleton). Then `Multiset.bind_bind` swaps the binds, and `Multiset.cons_swap`
      handles the output `T₁' :: T₂' :: B` vs `T₂' :: T₁' :: B`.
    - **cons**: each summand corresponds via IH to the appropriate RHS summand
      (T₁-bucket on LHS ↔ F_A-bucket on RHS, T₂-bucket on LHS ↔ T-bucket on RHS,
      F-bucket unchanged). Combination via commutativity of `+`. -/
private theorem hostTripleSum_singleton_swap_msform
    (T₁ T₂ : Planar α) (F : List (Planar α)) :
    ∀ (pre_T pre_FA pre_B remaining : List (Planar α)),
    (hostTripleSum T₁ [T₂] F pre_T pre_FA pre_B remaining).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    (hostTripleSum T₂ [T₁] F pre_FA pre_T pre_B remaining).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  intro pre_T pre_FA pre_B remaining
  induction remaining generalizing pre_T pre_FA pre_B with
  | nil =>
    rw [hostTripleSum_nil_remaining, hostTripleSum_nil_remaining]
    rw [insertionForest_singleton T₂ pre_FA, insertionForest_singleton T₁ pre_T]
    -- Collapse `(s.map f).bind g = s.bind (g ∘ f)` on both sides via conv navigation.
    conv_lhs => rw [Multiset.map_bind]; rhs; ext T₁'; rw [Multiset.bind_map]
    conv_rhs => rw [Multiset.map_bind]; rhs; ext T₂'; rw [Multiset.bind_map]
    -- LHS = bind T₁': bind T₂': (insertionForest F pre_B).map B => msform (T₁' :: [T₂'] ++ B)
    --     = bind T₁': map msform of (bind T₂': (insertionForest F pre_B).map B => T₁' :: [T₂'] ++ B)
    -- Wait — after map_bind + bind_map, we still have the outer .map msform at level 2.
    -- Let me push further.
    conv_lhs => rhs; ext T₁'; rw [Multiset.map_bind]; rhs; ext T₂'; rw [Multiset.map_map]
    conv_rhs => rhs; ext T₂'; rw [Multiset.map_bind]; rhs; ext T₁'; rw [Multiset.map_map]
    -- LHS = bind T₁': bind T₂': (insertionForest F pre_B).map (msform ∘ (T₁' :: [T₂'] ++ ·))
    -- RHS = bind T₂': bind T₁': (insertionForest F pre_B).map (msform ∘ (T₂' :: [T₁'] ++ ·))
    -- Swap LHS binds via Multiset.bind_bind.
    rw [Multiset.bind_bind]
    -- Now LHS = bind T₂': bind T₁': (insertionForest F pre_B).map (msform ∘ (T₁' :: [T₂'] ++ ·))
    -- RHS = bind T₂': bind T₁': (insertionForest F pre_B).map (msform ∘ (T₂' :: [T₁'] ++ ·))
    refine Multiset.bind_congr fun T₂' _ => ?_
    refine Multiset.bind_congr fun T₁' _ => ?_
    refine Multiset.map_congr rfl fun B _ => ?_
    -- Goal: msform (T₁' :: [T₂'] ++ B) = msform (T₂' :: [T₁'] ++ B)
    show (Multiset.ofList ((T₁' :: [T₂'] ++ B).map Nonplanar.mk) :
            Multiset (Nonplanar α)) =
         Multiset.ofList ((T₂' :: [T₁'] ++ B).map Nonplanar.mk)
    rw [show T₁' :: [T₂'] ++ B = T₁' :: T₂' :: B from rfl]
    rw [show T₂' :: [T₁'] ++ B = T₂' :: T₁' :: B from rfl]
    rw [msform_cons, msform_cons, msform_cons, msform_cons]
    exact Multiset.cons_swap _ _ _
  | cons x rest ih =>
    rw [hostTripleSum_cons_remaining, hostTripleSum_cons_remaining]
    rw [Multiset.map_add, Multiset.map_add, Multiset.map_add, Multiset.map_add]
    -- LHS_summands:
    --   1: (triple T₁ [T₂] F (pre_T ++ [x]) pre_FA pre_B rest).map _   -- x → T₁
    --   2: (triple T₁ [T₂] F pre_T (pre_FA ++ [x]) pre_B rest).map _   -- x → T₂
    --   3: (triple T₁ [T₂] F pre_T pre_FA (pre_B ++ [x]) rest).map _   -- x → F
    -- RHS_summands (with pre_T ↔ pre_FA swap):
    --   1': (triple T₂ [T₁] F (pre_FA ++ [x]) pre_T pre_B rest).map _  -- x → T₂
    --   2': (triple T₂ [T₁] F pre_FA (pre_T ++ [x]) pre_B rest).map _  -- x → T₁
    --   3': (triple T₂ [T₁] F pre_FA pre_T (pre_B ++ [x]) rest).map _  -- x → F
    rw [ih (pre_T ++ [x]) pre_FA pre_B,
        ih pre_T (pre_FA ++ [x]) pre_B,
        ih pre_T pre_FA (pre_B ++ [x])]
    -- Now LHS = (triple T₂ [T₁] F pre_FA (pre_T ++ [x]) pre_B rest).map _   -- = RHS_2'
    --        + (triple T₂ [T₁] F (pre_FA ++ [x]) pre_T pre_B rest).map _   -- = RHS_1'
    --        + (triple T₂ [T₁] F pre_FA pre_T (pre_B ++ [x]) rest).map _   -- = RHS_3'
    --      = RHS_1' + RHS_2' + RHS_3' by commutativity.
    ac_rfl

/-- **Adjacent host swap**: `insertionForest` is invariant under swapping two
    adjacent host trees, at the `Multiset.ofList ∘ List.map mk` level.

    The proof: bridge `insertionForest (T₁ :: T₂ :: F) gs` to
    `hostTripleSum T₁ [T₂] F [] [] [] gs` (via the chain
    `hostTripleSum_T_split` + `hostBucketSum_eq_insertionForest`), then apply
    `hostTripleSum_singleton_swap_msform`, then bridge back. -/
private theorem insertionForest_swap_host_msform
    (T₁ T₂ : Planar α) (F gs : List (Planar α)) :
    (insertionForest (T₁ :: T₂ :: F) gs).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    (insertionForest (T₂ :: T₁ :: F) gs).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- Bridge LHS: insertionForest (T₁ :: T₂ :: F) gs = hostTripleSum T₁ [T₂] F [] [] [] gs.
  have hL : insertionForest (T₁ :: T₂ :: F) gs =
      hostTripleSum T₁ [T₂] F [] [] [] gs := by
    rw [hostTripleSum_T_split]
    simp only [List.nil_append]
    rw [show T₁ :: T₂ :: F = T₁ :: ([T₂] ++ F) from rfl]
    rw [insertionForest_cons_assignment]
    refine Multiset.bind_congr fun α _ => ?_
    refine Multiset.bind_congr fun T₁' _ => ?_
    rw [hostBucketSum_eq_insertionForest]
  have hR : insertionForest (T₂ :: T₁ :: F) gs =
      hostTripleSum T₂ [T₁] F [] [] [] gs := by
    rw [hostTripleSum_T_split]
    simp only [List.nil_append]
    rw [show T₂ :: T₁ :: F = T₂ :: ([T₁] ++ F) from rfl]
    rw [insertionForest_cons_assignment]
    refine Multiset.bind_congr fun α _ => ?_
    refine Multiset.bind_congr fun T₂' _ => ?_
    rw [hostBucketSum_eq_insertionForest]
  rw [hL, hR]
  exact hostTripleSum_singleton_swap_msform T₁ T₂ F [] [] [] gs

/-- **Host-Perm invariance** at the multiset-of-multiset level: when host
    trees are permuted, the `(insertionForest host gs).map (Multiset.ofList ∘ List.map mk)`
    is unchanged.

    This is the key invariance used by `Nonplanar.insertionMultiset_add_host`
    (and similar Nonplanar-side lifts) to bridge `(A + B).toList.map Q.out`
    with `A.toList.map Q.out ++ B.toList.map Q.out`. -/
theorem insertionForest_perm_host_msform
    {host host' : List (Planar α)} (h : host.Perm host') (gs : List (Planar α)) :
    (insertionForest host gs).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    (insertionForest host' gs).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  induction h generalizing gs with
  | nil => rfl
  | @cons x l l' _ ih =>
    -- Use insertionForest_cons_assignment to expand both sides.
    rw [insertionForest_cons_assignment x l gs, insertionForest_cons_assignment x l' gs]
    -- Push msform through the outer bind / bind / map / map.
    rw [Multiset.map_bind, Multiset.map_bind]
    refine Multiset.bind_congr fun assn _ => ?_
    rw [Multiset.map_bind, Multiset.map_bind]
    refine Multiset.bind_congr fun T' _ => ?_
    -- Combine the two .map's: .map msform ∘ .map (T' :: ·) = .map (msform ∘ (T' :: ·)).
    rw [Multiset.map_map, Multiset.map_map]
    -- Convert (msform ∘ (T' :: ·)) = ((mk T' ::ₘ ·) ∘ msform) via msform_cons.
    rw [show ((fun L : List (Planar α) =>
              (Multiset.ofList (L.map Nonplanar.mk) : Multiset (Nonplanar α))) ∘
                (fun F' : List (Planar α) => T' :: F')) =
            ((fun M : Multiset (Nonplanar α) => Nonplanar.mk T' ::ₘ M) ∘
              (fun L : List (Planar α) =>
                (Multiset.ofList (L.map Nonplanar.mk) : Multiset (Nonplanar α)))) from by
          funext F'
          exact msform_cons T' F']
    -- Now: (insertionForest l filter_f).map ((mk T' ::ₘ ·) ∘ msform)
    --    = ((insertionForest l filter_f).map msform).map (mk T' ::ₘ ·)
    rw [← Multiset.map_map, ← Multiset.map_map]
    rw [ih]
  | @swap x y l =>
    exact insertionForest_swap_host_msform y x l gs
  | @trans l₁ l₂ l₃ _ _ ih₁ ih₂ => exact (ih₁ gs).trans (ih₂ gs)

/-! ## §6: Bit-vector ↔ powerset bridge

For a list `l : List β`, bit-vectors of length `|l|` enumerate sublists
of `l` (the elements where the bit is true). At the multiset level, the
collection of `(filter_t, filter_f)` pairs over all bit-vectors equals
the collection of `(s, ↑l - s)` over `s ∈ (↑l).powerset`. Used by
`Nonplanar.insertionMultiset_add_host` to bridge the
`hostBucketSum_assignment_rewrite` form (bind over bit-vectors) with
the `C.powerset.bind` form on the RHS. -/

/-- The complementary `filter_t / filter_f` operations on a bit-vector
    over a list `l` partition `l` (as multisets) when their lengths match:
    `↑(filter_t l assn) + ↑(filter_f l assn) = ↑l`. -/
private theorem filterMap_t_add_filterMap_f_eq_self {β : Type*}
    (l : List β) (assn : List Bool) (hlen : assn.length = l.length) :
    ((l.zip assn).filterMap (fun p => if p.snd then some p.fst else none) :
        Multiset β) +
    ((l.zip assn).filterMap (fun p => if p.snd then none else some p.fst) :
        Multiset β) =
    (↑l : Multiset β) := by
  induction l generalizing assn with
  | nil =>
    have : assn = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst this
    simp
  | cons a l_rest ih =>
    cases assn with
    | nil => simp at hlen
    | cons b assn_rest =>
      have hlen' : assn_rest.length = l_rest.length := by
        simpa [List.length_cons] using hlen
      simp only [List.zip_cons_cons, List.filterMap_cons]
      cases b with
      | true =>
        simp only [if_pos rfl]
        show (a ::ₘ ((l_rest.zip assn_rest).filterMap
                (fun p => if p.snd = true then some p.fst else none) :
                Multiset β)) +
            ((l_rest.zip assn_rest).filterMap
              (fun p => if p.snd = true then none else some p.fst) :
              Multiset β) =
            (a ::ₘ (↑l_rest : Multiset β))
        rw [Multiset.cons_add]
        congr 1
        exact ih assn_rest hlen'
      | false =>
        simp only [if_neg (by decide : (false : Bool) ≠ true)]
        show ((l_rest.zip assn_rest).filterMap
                (fun p => if p.snd = true then some p.fst else none) :
                Multiset β) +
            (a ::ₘ ((l_rest.zip assn_rest).filterMap
              (fun p => if p.snd = true then none else some p.fst) :
              Multiset β)) =
            (a ::ₘ (↑l_rest : Multiset β))
        rw [Multiset.add_cons]
        congr 1
        exact ih assn_rest hlen'

/-- Corollary: `↑(filter_f l assn) = ↑l - ↑(filter_t l assn)`, given matching length. -/
private theorem filterMap_f_eq_sub {β : Type*} [DecidableEq β]
    (l : List β) (assn : List Bool) (hlen : assn.length = l.length) :
    ((l.zip assn).filterMap (fun p => if p.snd then none else some p.fst) :
        Multiset β) =
    (↑l : Multiset β) -
    ((l.zip assn).filterMap (fun p => if p.snd then some p.fst else none) :
        Multiset β) := by
  have h := filterMap_t_add_filterMap_f_eq_self l assn hlen
  rw [← h, add_tsub_cancel_left]

/-- Length lemma: every element of `listChoices [b₁, b₂] n` has length exactly `n`.
    A re-export of the existing `mem_listChoices_length` for `[true, false]`. -/
private theorem mem_listChoices_bool_length :
    ∀ (n : Nat) (assn : List Bool),
    assn ∈ listChoices [true, false] n → assn.length = n :=
  mem_listChoices_length [true, false]

/-- **Bit-vector ↔ powerset bridge (paired form, first-component map only)**:
    enumerating bit-vectors and mapping to `↑(filter_t)` gives the powerset
    of `↑l`. (No second component yet — see paired version below.) -/
private theorem listChoices_bridge_powerset {β : Type*} [DecidableEq β]
    (l : List β) :
    (Multiset.ofList (listChoices [true, false] l.length)).map (fun assn =>
      ((l.zip assn).filterMap (fun p => if p.snd then some p.fst else none) :
          Multiset β)) =
    Multiset.powerset (↑l : Multiset β) := by
  induction l with
  | nil =>
    show (Multiset.ofList (listChoices [true, false] 0)).map _ =
         Multiset.powerset (↑([] : List β) : Multiset β)
    rw [listChoices_zero]
    rw [show (Multiset.ofList ([[]] : List (List Bool)) : Multiset (List Bool)) =
            (([] : List Bool) ::ₘ 0) from rfl]
    rw [Multiset.map_cons, Multiset.map_zero]
    rw [show (↑([] : List β) : Multiset β) = (0 : Multiset β) from rfl]
    rw [Multiset.powerset_zero]
    rfl
  | cons a l_rest ih =>
    -- LHS: bit-vector enumeration over (a :: l_rest).
    -- RHS: (a ::ₘ ↑l_rest).powerset = ↑l_rest.powerset + (↑l_rest.powerset).map (a ::ₘ ·).
    rw [show (a :: l_rest).length = l_rest.length + 1 from rfl]
    rw [listChoices_succ]
    rw [show ([true, false].flatMap
              (fun b => (listChoices [true, false] l_rest.length).map (b :: ·)) :
              List (List Bool)) =
            (listChoices [true, false] l_rest.length).map (true :: ·) ++
            (listChoices [true, false] l_rest.length).map (false :: ·) from by
          show (true :: false :: []).flatMap _ = _
          rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil]]
    rw [show (Multiset.ofList ((listChoices [true, false] l_rest.length).map (true :: ·) ++
              (listChoices [true, false] l_rest.length).map (false :: ·)) :
              Multiset (List Bool)) =
            Multiset.ofList ((listChoices [true, false] l_rest.length).map (true :: ·)) +
            Multiset.ofList ((listChoices [true, false] l_rest.length).map (false :: ·)) from by
          rw [← Multiset.coe_add]]
    rw [Multiset.map_add]
    -- For (true :: ·) branch: filter_t (a :: l_rest) (true :: assn') = a :: filter_t l_rest assn'
    -- For (false :: ·) branch: filter_t (a :: l_rest) (false :: assn') = filter_t l_rest assn'
    rw [show (Multiset.ofList ((listChoices [true, false] l_rest.length).map (true :: ·)) :
              Multiset (List Bool)) =
            (Multiset.ofList (listChoices [true, false] l_rest.length)).map (true :: ·) from rfl]
    rw [show (Multiset.ofList ((listChoices [true, false] l_rest.length).map (false :: ·)) :
              Multiset (List Bool)) =
            (Multiset.ofList (listChoices [true, false] l_rest.length)).map (false :: ·) from rfl]
    rw [Multiset.map_map, Multiset.map_map]
    -- LHS true-branch: ((lc).map ((fun assn => ((a :: l_rest).zip assn).filterMap_t) ∘ (true :: ·)))
    --             = (lc).map (fun assn' => a :: filter_t l_rest assn')
    -- LHS false-branch: (lc).map (fun assn' => filter_t l_rest assn')
    rw [show ((fun assn : List Bool =>
              (((a :: l_rest).zip assn).filterMap
                (fun p => if p.snd then some p.fst else none) : Multiset β))
              ∘ (fun assn => true :: assn)) =
            (fun assn' : List Bool =>
              (a ::ₘ (((l_rest.zip assn').filterMap
                (fun p => if p.snd then some p.fst else none)) : Multiset β))) from by
          funext assn'
          show ((((a :: l_rest).zip (true :: assn')).filterMap
                (fun p => if p.snd then some p.fst else none) : Multiset β)) =
              a ::ₘ (((l_rest.zip assn').filterMap
                (fun p => if p.snd then some p.fst else none) : Multiset β))
          rw [show (a :: l_rest).zip (true :: assn') = (a, true) :: l_rest.zip assn' from rfl]
          rw [List.filterMap_cons]
          simp only [if_pos rfl]
          rfl]
    rw [show ((fun assn : List Bool =>
              (((a :: l_rest).zip assn).filterMap
                (fun p => if p.snd then some p.fst else none) : Multiset β))
              ∘ (fun assn => false :: assn)) =
            (fun assn' : List Bool =>
              (((l_rest.zip assn').filterMap
                (fun p => if p.snd then some p.fst else none)) : Multiset β)) from by
          funext assn'
          show ((((a :: l_rest).zip (false :: assn')).filterMap
                (fun p => if p.snd then some p.fst else none) : Multiset β)) =
              (((l_rest.zip assn').filterMap
                (fun p => if p.snd then some p.fst else none)) : Multiset β)
          rw [show (a :: l_rest).zip (false :: assn') = (a, false) :: l_rest.zip assn' from rfl]
          rw [List.filterMap_cons]
          simp only [if_neg (by decide : (false : Bool) ≠ true)]]
    -- Now LHS = (lc).map (a ::ₘ filter_t l_rest) + (lc).map (filter_t l_rest)
    -- RHS: (a ::ₘ ↑l_rest).powerset = ↑l_rest.powerset + (↑l_rest.powerset).map (a ::ₘ ·)
    --     [by Multiset.powerset_cons]
    rw [show (↑(a :: l_rest) : Multiset β) = a ::ₘ ↑l_rest from rfl]
    rw [Multiset.powerset_cons]
    -- IH: (lc).map (filter_t l_rest) = ↑l_rest.powerset
    -- LHS_false matches RHS first-summand directly.
    -- LHS_true = (lc).map (a ::ₘ filter_t l_rest) = ((lc).map (filter_t l_rest)).map (a ::ₘ ·)
    --         = ↑l_rest.powerset.map (a ::ₘ ·) = RHS second-summand.
    rw [show (fun assn' : List Bool =>
              (a ::ₘ (((l_rest.zip assn').filterMap
                (fun p => if p.snd then some p.fst else none)) : Multiset β))) =
            ((fun s : Multiset β => a ::ₘ s) ∘
              (fun assn' : List Bool =>
                (((l_rest.zip assn').filterMap
                  (fun p => if p.snd then some p.fst else none)) : Multiset β))) from rfl]
    rw [← Multiset.map_map]
    rw [ih]
    rw [add_comm]

/-- **Bit-vector ↔ powerset bridge (paired form)**: enumerating bit-vectors
    and pairing `(filter_t, filter_f)` gives the powerset paired with
    complement `(s, ↑l - s)`. Derived from the single-component version +
    `filterMap_f_eq_sub`. -/
private theorem listChoices_bridge_powerset_paired {β : Type*} [DecidableEq β]
    (l : List β) :
    (Multiset.ofList (listChoices [true, false] l.length)).map
      (fun assn : List Bool =>
        let s_t : Multiset β :=
          (l.zip assn).filterMap (fun p => if p.snd then some p.fst else none)
        let s_f : Multiset β :=
          (l.zip assn).filterMap (fun p => if p.snd then none else some p.fst)
        (s_t, s_f)) =
    (Multiset.powerset (↑l : Multiset β)).map
      (fun s : Multiset β => (s, (↑l : Multiset β) - s)) := by
  -- LHS: rewrite filter_f via filterMap_f_eq_sub (using assn length matches l length).
  have h_eq_pair : ∀ assn ∈ Multiset.ofList (listChoices [true, false] l.length),
      (let s_t : Multiset β :=
          (l.zip assn).filterMap (fun p => if p.snd then some p.fst else none)
       let s_f : Multiset β :=
          (l.zip assn).filterMap (fun p => if p.snd then none else some p.fst)
       (s_t, s_f)) =
      (let s_t : Multiset β :=
          (l.zip assn).filterMap (fun p => if p.snd then some p.fst else none)
       (s_t, (↑l : Multiset β) - s_t)) := by
    intros assn h_mem
    have hlen : assn.length = l.length := by
      have h_mem' : assn ∈ listChoices [true, false] l.length := by
        rwa [Multiset.mem_coe] at h_mem
      exact mem_listChoices_bool_length l.length assn h_mem'
    simp only
    rw [filterMap_f_eq_sub l assn hlen]
  rw [Multiset.map_congr rfl h_eq_pair]
  -- LHS = (lc).map (fun assn => (filter_t assn, ↑l - filter_t assn))
  --     = ((lc).map (filter_t)).map (fun s => (s, ↑l - s))
  rw [show (fun assn : List Bool =>
            let s_t : Multiset β :=
              (l.zip assn).filterMap (fun p => if p.snd then some p.fst else none)
            (s_t, (↑l : Multiset β) - s_t)) =
          ((fun s : Multiset β => (s, (↑l : Multiset β) - s)) ∘
            (fun assn : List Bool =>
              ((l.zip assn).filterMap (fun p => if p.snd then some p.fst else none) :
                  Multiset β))) from rfl]
  rw [← Multiset.map_map]
  rw [listChoices_bridge_powerset]

/-! ## §7: Guest-multiset invariance at the msform level

`(insertionForest host gs).map msform` depends only on the multiset image
of `gs.map mk`, not on the planar representatives or order. This combines
guest-Perm invariance + guest-PlanarEquiv invariance into a single lemma
matching the level used by `Nonplanar.insertionMultiset`. -/

/-- General `Perm` lifting: if `(l₁.map f).Perm (l₂.map f)`, there exists
    a planar list `l_mid` such that `l₁.Perm l_mid` and `l_mid.map f = l₂.map f`
    AS LISTS (so `Forall₂ (mk · = mk ·) l_mid l₂` follows). -/
private theorem perm_lift_through_map {α₁ β₁ : Type*} (f : α₁ → β₁) :
    ∀ {l₂ l₁ : List α₁}, (l₁.map f).Perm (l₂.map f) →
    ∃ l_mid : List α₁, l₁.Perm l_mid ∧ l_mid.map f = l₂.map f := by
  intro l₂
  induction l₂ with
  | nil =>
    intro l₁ h
    rw [List.map_nil] at h
    have h_eq : l₁.map f = [] := h.eq_nil
    have hl₁ : l₁ = [] := List.map_eq_nil_iff.mp h_eq
    exact ⟨[], hl₁ ▸ List.Perm.refl _, by simp⟩
  | cons b l₂_rest ih =>
    intro l₁ h
    -- f b ∈ l₁.map f (by Perm).
    have hfb_mem : f b ∈ l₁.map f := by
      apply h.symm.subset
      rw [List.map_cons]
      exact List.mem_cons_self
    obtain ⟨a, ha_mem, hfa_eq⟩ := List.mem_map.mp hfb_mem
    letI : DecidableEq α₁ := Classical.decEq _
    -- l₁ Perm (a :: l₁.erase a)
    have hperm_l₁ : l₁.Perm (a :: l₁.erase a) := List.perm_cons_erase ha_mem
    -- ((a :: l₁.erase a).map f) Perm ((b :: l₂_rest).map f)
    have h' : ((a :: l₁.erase a).map f).Perm ((b :: l₂_rest).map f) :=
      (hperm_l₁.map f).symm.trans h
    rw [List.map_cons, List.map_cons] at h'
    rw [hfa_eq] at h'
    -- (f b :: (l₁.erase a).map f) Perm (f b :: l₂_rest.map f)
    have h_inner : ((l₁.erase a).map f).Perm (l₂_rest.map f) := h'.cons_inv
    obtain ⟨l_mid_rest, hperm_rest, hmap_rest⟩ := ih h_inner
    refine ⟨a :: l_mid_rest, ?_, ?_⟩
    · exact hperm_l₁.trans (hperm_rest.cons a)
    · rw [List.map_cons, List.map_cons, hfa_eq, hmap_rest]

/-- Filter_t preserves `Forall₂ PlanarEquiv` on guests. -/
private theorem filter_t_preserves_planarEquiv
    {Ts Ts' : List (Planar α)} (h : List.Forall₂ PlanarEquiv Ts Ts')
    (assn : List Bool) :
    List.Forall₂ PlanarEquiv
      ((Ts.zip assn).filterMap (fun p => if p.snd then some p.fst else none))
      ((Ts'.zip assn).filterMap (fun p => if p.snd then some p.fst else none)) := by
  induction h generalizing assn with
  | nil =>
    rw [show ([] : List (Planar α)).zip assn = [] from rfl]
    exact List.Forall₂.nil
  | @cons T T' Ts_tail Ts'_tail hd_pe _tail_pe ih =>
    cases assn with
    | nil =>
      rw [show (T :: Ts_tail).zip ([] : List Bool) = [] from rfl,
          show (T' :: Ts'_tail).zip ([] : List Bool) = [] from rfl]
      exact List.Forall₂.nil
    | cons b assn_rest =>
      rw [show (T :: Ts_tail).zip (b :: assn_rest) = (T, b) :: Ts_tail.zip assn_rest from rfl,
          show (T' :: Ts'_tail).zip (b :: assn_rest) =
              (T', b) :: Ts'_tail.zip assn_rest from rfl]
      simp only [List.filterMap_cons]
      cases b with
      | true =>
        simp only [if_pos rfl]
        exact List.Forall₂.cons hd_pe (ih assn_rest)
      | false =>
        simp only [if_neg (by decide : (false : Bool) ≠ true)]
        exact ih assn_rest

/-- Filter_f preserves `Forall₂ PlanarEquiv` on guests. -/
private theorem filter_f_preserves_planarEquiv
    {Ts Ts' : List (Planar α)} (h : List.Forall₂ PlanarEquiv Ts Ts')
    (assn : List Bool) :
    List.Forall₂ PlanarEquiv
      ((Ts.zip assn).filterMap (fun p => if p.snd then none else some p.fst))
      ((Ts'.zip assn).filterMap (fun p => if p.snd then none else some p.fst)) := by
  induction h generalizing assn with
  | nil =>
    rw [show ([] : List (Planar α)).zip assn = [] from rfl]
    exact List.Forall₂.nil
  | @cons T T' Ts_tail Ts'_tail hd_pe _tail_pe ih =>
    cases assn with
    | nil =>
      rw [show (T :: Ts_tail).zip ([] : List Bool) = [] from rfl,
          show (T' :: Ts'_tail).zip ([] : List Bool) = [] from rfl]
      exact List.Forall₂.nil
    | cons b assn_rest =>
      rw [show (T :: Ts_tail).zip (b :: assn_rest) = (T, b) :: Ts_tail.zip assn_rest from rfl,
          show (T' :: Ts'_tail).zip (b :: assn_rest) =
              (T', b) :: Ts'_tail.zip assn_rest from rfl]
      simp only [List.filterMap_cons]
      cases b with
      | true =>
        simp only [if_pos rfl]
        exact ih assn_rest
      | false =>
        simp only [if_neg (by decide : (false : Bool) ≠ true)]
        exact List.Forall₂.cons hd_pe (ih assn_rest)

/-- **Forest version of guest-PlanarEquiv invariance**: `Forall₂ PlanarEquiv`
    on guests preserves `(insertionForest F Ts).map (List.map mk)`.
    Mirrors `insertionForest_planarEquiv_host` (Insertion.lean §6) but for
    the guest list. -/
theorem insertionForest_planarEquiv_guests
    (F : List (Planar α)) {Ts Ts' : List (Planar α)}
    (h : List.Forall₂ PlanarEquiv Ts Ts') :
    (insertionForest F Ts).map (List.map Nonplanar.mk) =
    (insertionForest F Ts').map (List.map Nonplanar.mk) := by
  induction F generalizing Ts Ts' with
  | nil =>
    cases h with
    | nil => rfl
    | cons _ _ =>
      rw [insertionForest_empty_host_nonempty_guests,
          insertionForest_empty_host_nonempty_guests]
  | cons T_h F_h ih_F =>
    rw [insertionForest_cons_assignment T_h F_h Ts,
        insertionForest_cons_assignment T_h F_h Ts']
    have hlen : Ts.length = Ts'.length := List.Forall₂.length_eq h
    rw [hlen]
    rw [Multiset.map_bind, Multiset.map_bind]
    refine Multiset.bind_congr fun assn _ => ?_
    have h_ft := filter_t_preserves_planarEquiv h assn
    have h_ff := filter_f_preserves_planarEquiv h assn
    rw [Multiset.map_bind, Multiset.map_bind]
    simp only [Multiset.map_map, Function.comp, List.map_cons]
    let f_T : Nonplanar α → Multiset (List (Nonplanar α)) := fun mk_T_ins =>
      (insertionForest F_h ((Ts.zip assn).filterMap
          (fun p => if p.snd then none else some p.fst))).map
        (fun F_ins => mk_T_ins :: F_ins.map Nonplanar.mk)
    let f_T' : Nonplanar α → Multiset (List (Nonplanar α)) := fun mk_T_ins =>
      (insertionForest F_h ((Ts'.zip assn).filterMap
          (fun p => if p.snd then none else some p.fst))).map
        (fun F_ins => mk_T_ins :: F_ins.map Nonplanar.mk)
    change (insertion T_h _).bind (fun T_ins => f_T (Nonplanar.mk T_ins)) =
           (insertion T_h _).bind (fun T_ins => f_T' (Nonplanar.mk T_ins))
    rw [← Multiset.bind_map, ← Multiset.bind_map]
    rw [insertion_planarEquiv_guests T_h h_ft]
    refine Multiset.bind_congr fun mk_T_ins _ => ?_
    show (insertionForest F_h ((Ts.zip assn).filterMap
              (fun p => if p.snd then none else some p.fst))).map
            (fun F_ins => mk_T_ins :: F_ins.map Nonplanar.mk) =
         (insertionForest F_h ((Ts'.zip assn).filterMap
              (fun p => if p.snd then none else some p.fst))).map
            (fun F_ins => mk_T_ins :: F_ins.map Nonplanar.mk)
    rw [show (fun F_ins : List (Planar α) => mk_T_ins :: F_ins.map Nonplanar.mk) =
            ((fun L : List (Nonplanar α) => mk_T_ins :: L) ∘ List.map Nonplanar.mk) from rfl]
    rw [← Multiset.map_map, ← Multiset.map_map]
    rw [ih_F h_ff]

/-- **Combined guest invariance** at the multiset-of-multiset level. -/
theorem insertionForest_msform_invariance_guests
    (host : List (Planar α)) {gs1 gs2 : List (Planar α)}
    (h : (gs1.map Nonplanar.mk).Perm (gs2.map Nonplanar.mk)) :
    (insertionForest host gs1).map (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
    (insertionForest host gs2).map (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  obtain ⟨gs_mid, hperm_planar, hmap_eq⟩ := perm_lift_through_map Nonplanar.mk h
  have h_forall : List.Forall₂ PlanarEquiv gs_mid gs2 := by
    have hlen : gs_mid.length = gs2.length := by
      have := congrArg List.length hmap_eq
      simpa using this
    clear hperm_planar h
    induction gs_mid generalizing gs2 with
    | nil =>
      cases gs2 with
      | nil => exact List.Forall₂.nil
      | cons _ _ => simp at hlen
    | cons a gs_mid_rest ih =>
      cases gs2 with
      | nil => simp at hlen
      | cons b gs2_rest =>
        rw [List.map_cons, List.map_cons] at hmap_eq
        have h_head : Nonplanar.mk a = Nonplanar.mk b :=
          (List.cons.injEq _ _ _ _).mp hmap_eq |>.left
        have h_tail : gs_mid_rest.map Nonplanar.mk = gs2_rest.map Nonplanar.mk :=
          (List.cons.injEq _ _ _ _).mp hmap_eq |>.right
        have hlen_rest : gs_mid_rest.length = gs2_rest.length := by simpa using hlen
        exact List.Forall₂.cons (Nonplanar.mk_eq_mk_iff.mp h_head)
          (ih h_tail hlen_rest)
  have step1 : (insertionForest host gs1).map (List.map Nonplanar.mk) =
               (insertionForest host gs_mid).map (List.map Nonplanar.mk) :=
    insertionForest_perm_guests host hperm_planar
  have step2 : (insertionForest host gs_mid).map (List.map Nonplanar.mk) =
               (insertionForest host gs2).map (List.map Nonplanar.mk) :=
    insertionForest_planarEquiv_guests host h_forall
  have h_combined : (insertionForest host gs1).map (List.map Nonplanar.mk) =
                    (insertionForest host gs2).map (List.map Nonplanar.mk) :=
    step1.trans step2
  have hwrap : ∀ (s : Multiset (List (Planar α))),
      s.map (fun L : List (Planar α) =>
        (Multiset.ofList (L.map Nonplanar.mk) : Multiset (Nonplanar α))) =
      (s.map (List.map Nonplanar.mk)).map (fun L : List (Nonplanar α) =>
        (Multiset.ofList L : Multiset (Nonplanar α))) := by
    intro s
    rw [Multiset.map_map]
    rfl
  rw [hwrap, hwrap, h_combined]

end Pathed

end Planar

end RootedTree
