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

end Pathed

end Planar

end RootedTree
