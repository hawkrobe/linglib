/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion

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

/-- `insertion T []` is the singleton `{T}` (multi-graft of no guests is the identity). -/
private theorem insertion_nil_guests (T : Planar α) :
    insertion T [] = ({T} : Multiset (Planar α)) := by
  rw [insertion_def]
  simp [listChoices_zero, multiGraft_nil]

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

private theorem hostBucketSum_eq_insertionForest (host_A host_B guests : List (Planar α)) :
    hostBucketSum host_A host_B [] [] guests =
      insertionForest (host_A ++ host_B) guests := by
  induction host_A with
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
    -- TODO: prove via `hostTripleSum_T_split` (generalized cross-form) + IH on F_A.
    -- The proof requires: (i) `hostTripleSum_T_split` substrate (~80 LOC inducting on remaining
    -- with pre's generalized, using `listChoices_succ_cons_bind` + `hostBucketSum_cons_remaining`
    -- to align T-add/FA-add/B-add with bind-α-cons-prepend over true vs false bit for g);
    -- (ii) apply `hostTripleSum_T_split` here with empty pre to get
    --      `bind α: (insertion T (filter_t)).bind T' => (hostBucketSum F_A host_B [] [] (filter_f)).map (T' :: ·)`;
    -- (iii) rewrite inner via IH `ih` (hostBucketSum F_A host_B = insertionForest (F_A ++ host_B));
    -- (iv) close via `insertionForest_cons_assignment` in reverse.
    sorry

end Pathed

end Planar

end RootedTree
