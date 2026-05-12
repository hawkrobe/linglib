/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion

set_option autoImplicit false

/-!
# `kBucketSum`: k-way bucketed enumeration

Polymorphic substrate generalising the family of bucket-aggregator
patterns used in planar multi-graft proofs (Foissy 2021,
Marcolli-Chomsky-Berwick 2025, Oudom-Guin 2004).

For each item in `remaining`, a choice from `idx` selects a bucket;
items accumulate into the per-bucket lists `pres`. At empty
`remaining`, the leaf function `leaf : (τ → List ι) → Multiset ω`
consumes the final bucket assignment and produces the output.

This unifies the previously hand-rolled `hostBucketSum` (2 buckets,
parallel cartesian leaf), `hostTripleSum` (3 buckets, parallel triple
bind leaf), and `assocBucketSum` (2 buckets, iterated bind leaf), and
provides a one-liner pattern for future variants like the 5-bucket
aggregator needed for the deep case of `assocBucketSum`'s bridge.

## Status

`[UPSTREAM]` candidate. **Sorry-free**.
-/

namespace RootedTree

namespace Planar

namespace Pathed

universe u v w

variable {τ : Type u} {ι : Type v} {ω : Type w}

/-! ## §1: `bucketSlice` — items routed to a single bucket -/

/-- The slice of items from `Ts` whose assignment in `assn` equals `t`.
    Pairs `Ts` with `assn`, then collects items whose paired assignment
    matches the target bucket label. -/
def bucketSlice [DecidableEq τ] (Ts : List ι) (assn : List τ) (t : τ) : List ι :=
  (Ts.zip assn).filterMap fun p => if p.snd = t then some p.fst else none

@[simp] theorem bucketSlice_nil_left [DecidableEq τ] (assn : List τ) (t : τ) :
    bucketSlice ([] : List ι) assn t = [] := by
  unfold bucketSlice; simp

@[simp] theorem bucketSlice_nil_right [DecidableEq τ] (Ts : List ι) (t : τ) :
    bucketSlice Ts ([] : List τ) t = [] := by
  unfold bucketSlice; simp

theorem bucketSlice_cons_cons [DecidableEq τ]
    (x : ι) (Ts : List ι) (s : τ) (assn : List τ) (t : τ) :
    bucketSlice (x :: Ts) (s :: assn) t =
      (if s = t then [x] else []) ++ bucketSlice Ts assn t := by
  unfold bucketSlice
  rw [List.zip_cons_cons, List.filterMap_cons]
  by_cases h : s = t
  · simp [h]
  · simp [h]

/-! ## §2: `kBucketSum` — definition and basic equation lemmas -/

/-- k-way bucketed enumeration. For each item in `remaining`, bind
    over `idx` to choose a bucket; the accumulator `pres t` for that
    bucket grows by one item. At empty `remaining`, apply `leaf`. -/
def kBucketSum [DecidableEq τ] (idx : List τ)
    (leaf : (τ → List ι) → Multiset ω) (pres : τ → List ι) :
    List ι → Multiset ω
  | []         => leaf pres
  | x :: rest  =>
      (Multiset.ofList idx).bind fun t =>
        kBucketSum idx leaf (Function.update pres t (pres t ++ [x])) rest

theorem kBucketSum_nil_remaining [DecidableEq τ] (idx : List τ)
    (leaf : (τ → List ι) → Multiset ω) (pres : τ → List ι) :
    kBucketSum idx leaf pres [] = leaf pres := rfl

theorem kBucketSum_cons_remaining [DecidableEq τ] (idx : List τ)
    (leaf : (τ → List ι) → Multiset ω) (pres : τ → List ι)
    (x : ι) (rest : List ι) :
    kBucketSum idx leaf pres (x :: rest) =
      (Multiset.ofList idx).bind fun t =>
        kBucketSum idx leaf (Function.update pres t (pres t ++ [x])) rest := rfl

/-! ## §3: assignment rewrite -/

/-- **Key identity**: `kBucketSum` over remaining items `Ts` equals a
    single bind over all length-`Ts.length` assignments (drawn from
    `idx`) of the leaf applied to the accumulators augmented by the
    per-bucket slice of `Ts`. Generalises `hostBucketSum_assignment_rewrite`
    and `assocBucketSum_assignment_rewrite`. -/
theorem kBucketSum_assignment_rewrite [DecidableEq τ] (idx : List τ)
    (leaf : (τ → List ι) → Multiset ω) :
    ∀ (pres : τ → List ι) (Ts : List ι),
    kBucketSum idx leaf pres Ts =
      (Multiset.ofList (listChoices idx Ts.length)).bind fun assn =>
        leaf (fun t => pres t ++ bucketSlice Ts assn t) := by
  intro pres Ts
  induction Ts generalizing pres with
  | nil =>
    rw [kBucketSum_nil_remaining]
    simp only [List.length_nil, listChoices_zero, Multiset.coe_singleton,
               Multiset.singleton_bind, bucketSlice_nil_left, List.append_nil]
  | cons x rest ih =>
    rw [kBucketSum_cons_remaining]
    conv_rhs =>
      rw [show (x :: rest).length = rest.length + 1 from rfl, listChoices_succ]
      rw [show (Multiset.ofList (idx.flatMap fun t =>
                  (listChoices idx rest.length).map (t :: ·)) :
                Multiset (List τ)) =
              (Multiset.ofList idx).bind fun t =>
                Multiset.ofList ((listChoices idx rest.length).map (t :: ·))
              from by rw [← Multiset.coe_bind]]
      rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun t _ => ?_
    rw [show (Multiset.ofList ((listChoices idx rest.length).map (t :: ·)) :
              Multiset (List τ)) =
            (Multiset.ofList (listChoices idx rest.length)).map (t :: ·)
            from rfl]
    rw [Multiset.bind_map]
    rw [ih (Function.update pres t (pres t ++ [x]))]
    refine Multiset.bind_congr fun assn _ => ?_
    congr 1
    funext t'
    rw [bucketSlice_cons_cons]
    by_cases h : t = t'
    · subst h
      rw [if_pos rfl, Function.update_self]
      simp [List.append_assoc]
    · rw [if_neg h, Function.update_of_ne (Ne.symm h)]
      simp

end Pathed

end Planar

end RootedTree
