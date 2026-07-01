/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.GrossmanLarson
import Linglib.Core.Algebra.RootedTree.PreLie.InsertionAddHost
import Linglib.Core.Algebra.RootedTree.PreLie.InsertionCompose
import Linglib.Core.Algebra.ConnesKreimer.Shuffle

set_option autoImplicit false

/-!
# Basis-level substrate for the Grossman-Larson product
[oudom-guin-2008]
[foissy-typed-decorated-rooted-trees-2018]

Combinatorial substrate connecting the Grossman-Larson product on
`ConnesKreimer R (Nonplanar α)` to `Nonplanar.insertionMultiset` (NIM):
host distributivity, single-guest associativity, representative
invariance, and the powerset sum forms consumed by the associativity
proof in `GrossmanLarsonMonoid.lean` (which derives `mul_assoc` from the
abstract Oudom-Guin `★`-associativity via the `ckIsoSymmetricAlgebra`
bridge).

## Main results

* `Nonplanar.insertionMultiset_add_host` (Prop 2.7.iii substrate): NIM
  into a disjoint-union host decomposes over guest partitions.
* `Nonplanar.insertionMultiset_eq_of_reps`: NIM computes on any `Tree`-level
  representatives.
* `Nonplanar.insertionMultiset_singleton_assoc`: iterated single-guest
  grafting equals simultaneous grafting plus guest-nested grafting.
* `insertion_mul_distrib` (Prop 2.7.iii of [oudom-guin-2008] at basis
  level).
* `product_of'_sum_form` / `mul_of'_sum_form` / `lhs_quadruple_form` /
  `rhs_quintuple_form`: powerset sum forms of (iterated) GL products.

The deprecated direct combinatorial route to associativity (the A3.3
campaign: `insertionMultiset_assoc`, `insertion_assoc_shuffled`, the
Lemma-2.10 chain) was deleted on 2026-06-12 when the bridge route
closed; see `GrossmanLarsonMonoid.lean`.

`[UPSTREAM]` candidate (jointly with the OudomGuinCirc layer).
-/

namespace RootedTree

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### §1: Prop 2.7.iii — `∘` distributes over disjoint union via shuffle Δ

The shuffle coproduct decomposition on each forest argument C is realized
explicitly as the sum over `C.powerset` of the partition `(C₁, C - C₁)`.

The proof of Prop 2.7.iii at the GL/CK level reduces to a combinatorial
identity on `Nonplanar.insertionMultiset` (= NIM), which we state
separately and prove by descent from the `Tree`-level `insertionForest`.
-/

/-- **Deep substrate**: multi-graft into a disjoint union of host forests
    decomposes as a `Multiset.bind` over guest partitions. This is the
    combinatorial heart of Prop 2.7.iii at the basis level.

    `NIM(A + B, C) = Σ_{C₁ ⊆ C} {X_A + X_B : X_A ∈ NIM(A, C₁), X_B ∈ NIM(B, C-C₁)}`

    Proved via descent through `Tree.Pathed.hostBucketSum` and the powerset
    bridge `Tree.Pathed.listChoices_bridge_powerset_paired`, plus
    `insertionForest_msform_invariance_guests` to bridge `Tree`-level guests with
    canonical `Quotient.out` representatives. -/
theorem _root_.RootedTree.Nonplanar.insertionMultiset_add_host
    (A B C : Forest (Nonplanar α)) :
    Nonplanar.insertionMultiset (A + B) C =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       C.powerset.bind fun C₁ =>
        ((Nonplanar.insertionMultiset A C₁) ×ˢ
          (Nonplanar.insertionMultiset B (C - C₁))).map
          (fun p => p.1 + p.2)) := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- Steps 1-5: Unfold NIM, apply host-Perm bridge, hostBucketSum bridge, assignment
  -- rewrite, and push msform through the outer bind.
  unfold Nonplanar.insertionMultiset
  rw [Tree.Pathed.insertionForest_perm_host_msform
        (Nonplanar.toList_map_quotientOut_add_perm A B) (C.toList.map Quotient.out)]
  rw [← Tree.Pathed.hostBucketSum_eq_insertionForest]
  rw [Tree.Pathed.hostBucketSum_assignment_rewrite]
  rw [Multiset.map_bind, List.length_map]
  simp only [List.nil_append]
  -- Step 6: Define `msform : List (Tree α) → Multiset (Nonplanar α)` as a local
  -- abbreviation matching `Nonplanar.insertionMultiset`'s post-processing.
  set msform : List (Tree α) → Multiset (Nonplanar α) :=
    fun L => (Multiset.ofList (L.map Nonplanar.mk)) with hmsform
  -- Step 7: Strategy — define `F : Multiset × Multiset → Multiset Multiset` so:
  --   LHS_inner(assn) = F (↑filter_t (C.toList zip assn), ↑filter_f (...))
  --   RHS_inner(C₁)   = F (C₁, C - C₁)
  -- Then RHS = (C.powerset.map (s ↦ (s, C - s))).bind F = (↑lc).bind (F ∘ ...) by
  -- the powerset bridge. The remaining work is per-assn equality.
  set F : Multiset (Nonplanar α) × Multiset (Nonplanar α) →
            Multiset (Multiset (Nonplanar α)) :=
    fun pair =>
      Multiset.map (fun p : Multiset (Nonplanar α) × Multiset (Nonplanar α) => p.1 + p.2)
        (Multiset.map msform
            (Tree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList A))
              (List.map Quotient.out pair.1.toList)) ×ˢ
          Multiset.map msform
            (Tree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList B))
              (List.map Quotient.out (Multiset.toList pair.2)))) with hF
  -- Step 7a: RHS = (C.powerset.map (s ↦ (s, C - s))).bind F via `← Multiset.bind_map`.
  have h_rhs_step1 :
      ((Multiset.powerset C).bind fun C₁ => F (C₁, C - C₁)) =
      ((Multiset.powerset C).map (fun s : Multiset (Nonplanar α) => (s, C - s))).bind F := by
    rw [Multiset.bind_map]
  -- Step 7b: Apply the powerset bridge to convert
  -- `(C.powerset.map (s, C-s))` to `(↑lc).map (filter_t, filter_f)`.
  have h_rhs_step2 :
      ((Multiset.powerset C).map (fun s : Multiset (Nonplanar α) => (s, C - s))) =
      (Multiset.ofList (Tree.Pathed.listChoices [true, false] C.toList.length)).map
        (fun assn : List Bool =>
          let s_t : Multiset (Nonplanar α) :=
            (C.toList.zip assn).filterMap (fun p => if p.snd then some p.fst else none)
          let s_f : Multiset (Nonplanar α) :=
            (C.toList.zip assn).filterMap (fun p => if p.snd then none else some p.fst)
          (s_t, s_f)) := by
    rw [show C = (↑(C.toList) : Multiset (Nonplanar α)) from C.coe_toList.symm]
    rw [← Tree.Pathed.listChoices_bridge_powerset_paired (l := C.toList)]
    simp only [Multiset.coe_toList]
  -- Step 7c: Reshape RHS to (↑lc).bind (F ∘ ...) so we can match per-assn.
  show ((↑(Tree.Pathed.listChoices [true, false] C.toList.length) :
          Multiset (List Bool)).bind fun a =>
        Multiset.map msform
          (Tree.Pathed.hostBucketSum (List.map Quotient.out (Multiset.toList A))
            (List.map Quotient.out (Multiset.toList B))
            (List.filterMap (fun p => if p.snd = true then some p.fst else none)
              ((List.map Quotient.out (Multiset.toList C)).zip a))
            (List.filterMap (fun p => if p.snd = true then none else some p.fst)
              ((List.map Quotient.out (Multiset.toList C)).zip a))
            [])) =
      (Multiset.powerset C).bind fun C₁ => F (C₁, C - C₁)
  rw [h_rhs_step1, h_rhs_step2, Multiset.bind_map]
  -- Step 8: Per-assn reduction via Multiset.bind_congr.
  refine Multiset.bind_congr fun assn h_assn => ?_
  have hlen : assn.length = C.toList.length := by
    have : assn ∈ Tree.Pathed.listChoices [true, false] C.toList.length :=
      Multiset.mem_coe.mp h_assn
    exact Tree.Pathed.mem_listChoices_bool_length C.toList.length assn this
  -- Step 8a: Apply hostBucketSum_nil_remaining and combine the two `.map`s.
  rw [Tree.Pathed.hostBucketSum_nil_remaining, Multiset.map_map]
  -- Step 8b: Unfold F on the RHS and abbreviate the filter results at multiset level.
  rw [hF]
  set s_t : Multiset (Nonplanar α) :=
    (List.filterMap (fun p => if p.snd = true then some p.fst else none)
      ((Multiset.toList C).zip assn) : Multiset (Nonplanar α)) with hs_t
  set s_f : Multiset (Nonplanar α) :=
    (List.filterMap (fun p => if p.snd = true then none else some p.fst)
      ((Multiset.toList C).zip assn) : Multiset (Nonplanar α)) with hs_f
  -- Beta-reduce the let binding on the RHS via `show`.
  show ((Tree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList A))
            (List.filterMap (fun p => if p.snd = true then some p.fst else none)
              ((List.map Quotient.out (Multiset.toList C)).zip assn))) ×ˢ
        Tree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList B))
            (List.filterMap (fun p => if p.snd = true then none else some p.fst)
              ((List.map Quotient.out (Multiset.toList C)).zip assn))).map
        (msform ∘ fun p => p.fst ++ p.snd) =
      (Multiset.map msform
          (Tree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList A))
            (List.map Quotient.out s_t.toList)) ×ˢ
        Multiset.map msform
          (Tree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList B))
            (List.map Quotient.out s_f.toList))).map (fun p => p.fst + p.snd)
  -- Step 8c: Set up `Tree`-level/canonical guest lists and bridge them via Perm.
  -- LHS uses `((C.toList.map Q.out).zip assn).filterMap_t` (`Tree` level).
  -- RHS uses `s_t.toList.map Q.out` (canonical Q.out of multiset). Both have multiset
  -- image `s_t = ↑((C.toList.zip assn).filterMap_t)` after `.map mk`.
  set ft_tree : List (Tree α) :=
    List.filterMap (fun p => if p.snd = true then some p.fst else none)
      ((List.map Quotient.out (Multiset.toList C)).zip assn) with hft_tree
  set ff_tree : List (Tree α) :=
    List.filterMap (fun p => if p.snd = true then none else some p.fst)
      ((List.map Quotient.out (Multiset.toList C)).zip assn) with hff_tree
  set ft_canon : List (Tree α) := s_t.toList.map Quotient.out with hft_canon
  set ff_canon : List (Tree α) := s_f.toList.map Quotient.out with hff_canon
  -- Step 8c.1: List-level: `((l.map Q.out).zip a).filterMap_t.map mk = (l.zip a).filterMap_t`.
  have h_ft_mk_eq : ft_tree.map Nonplanar.mk =
      (((Multiset.toList C).zip assn).filterMap
        (fun p => if p.snd then some p.fst else none) : List (Nonplanar α)) := by
    have h_aux : ∀ (l : List (Nonplanar α)) (a : List Bool),
        (((l.map Quotient.out).zip a).filterMap (fun p => if p.snd = true then some p.fst else none)).map
          Nonplanar.mk = (l.zip a).filterMap (fun p => if p.snd = true then some p.fst else none) := by
      intro l a
      induction l generalizing a with
      | nil =>
        show (((([] : List (Nonplanar α)).map Quotient.out).zip a).filterMap _).map Nonplanar.mk = _
        rw [show ([] : List (Nonplanar α)).map Quotient.out = [] from rfl]
        rfl
      | cons x rest ih =>
        cases a with
        | nil =>
          rw [show ((x :: rest).map Quotient.out).zip ([] : List Bool) = [] from by
            cases (x :: rest).map Quotient.out <;> rfl]
          rfl
        | cons b a_rest =>
          rw [show (x :: rest).map Quotient.out =
                Quotient.out x :: rest.map Quotient.out from rfl]
          rw [show (Quotient.out x :: rest.map Quotient.out).zip (b :: a_rest) =
                (Quotient.out x, b) :: (rest.map Quotient.out).zip a_rest from rfl]
          rw [show (x :: rest).zip (b :: a_rest) = (x, b) :: rest.zip a_rest from rfl]
          rw [List.filterMap_cons, List.filterMap_cons]
          cases b with
          | true =>
            -- if true then some Q.out x else none = some (Q.out x); on RHS some x.
            show (Quotient.out x ::
                ((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then some p.fst else none)).map Nonplanar.mk =
                x ::
                (rest.zip a_rest).filterMap
                  (fun p => if p.snd = true then some p.fst else none)
            rw [show ((Quotient.out x ::
                ((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then some p.fst else none)).map Nonplanar.mk) =
                Nonplanar.mk (Quotient.out x) ::
                  (((rest.map Quotient.out).zip a_rest).filterMap
                    (fun p => if p.snd = true then some p.fst else none)).map Nonplanar.mk from rfl]
            rw [ih a_rest]
            congr 1
            exact x.out_eq
          | false =>
            -- if false then some else none = none; both sides skip.
            show (((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then some p.fst else none)).map Nonplanar.mk =
                (rest.zip a_rest).filterMap
                  (fun p => if p.snd = true then some p.fst else none)
            exact ih a_rest
    show (ft_tree.map Nonplanar.mk : List (Nonplanar α)) =
        ((Multiset.toList C).zip assn).filterMap (fun p => if p.snd = true then some p.fst else none)
    exact h_aux C.toList assn
  -- Step 8c.2: Same identity for filter_f.
  have h_ff_mk_eq : ff_tree.map Nonplanar.mk =
      (((Multiset.toList C).zip assn).filterMap
        (fun p => if p.snd then none else some p.fst) : List (Nonplanar α)) := by
    have h_aux : ∀ (l : List (Nonplanar α)) (a : List Bool),
        (((l.map Quotient.out).zip a).filterMap
          (fun p => if p.snd = true then none else some p.fst)).map Nonplanar.mk =
        (l.zip a).filterMap (fun p => if p.snd = true then none else some p.fst) := by
      intro l a
      induction l generalizing a with
      | nil =>
        show (((([] : List (Nonplanar α)).map Quotient.out).zip a).filterMap _).map Nonplanar.mk = _
        rw [show ([] : List (Nonplanar α)).map Quotient.out = [] from rfl]
        rfl
      | cons x rest ih =>
        cases a with
        | nil =>
          rw [show ((x :: rest).map Quotient.out).zip ([] : List Bool) = [] from by
            cases (x :: rest).map Quotient.out <;> rfl]
          rfl
        | cons b a_rest =>
          rw [show (x :: rest).map Quotient.out =
                Quotient.out x :: rest.map Quotient.out from rfl]
          rw [show (Quotient.out x :: rest.map Quotient.out).zip (b :: a_rest) =
                (Quotient.out x, b) :: (rest.map Quotient.out).zip a_rest from rfl]
          rw [show (x :: rest).zip (b :: a_rest) = (x, b) :: rest.zip a_rest from rfl]
          rw [List.filterMap_cons, List.filterMap_cons]
          cases b with
          | true =>
            -- if true then none else some = none; both sides skip.
            show (((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then none else some p.fst)).map Nonplanar.mk =
                (rest.zip a_rest).filterMap
                  (fun p => if p.snd = true then none else some p.fst)
            exact ih a_rest
          | false =>
            -- if false then none else some Q.out x = some Q.out x; on RHS some x.
            show (Quotient.out x ::
                ((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then none else some p.fst)).map Nonplanar.mk =
                x ::
                (rest.zip a_rest).filterMap
                  (fun p => if p.snd = true then none else some p.fst)
            rw [show ((Quotient.out x ::
                ((rest.map Quotient.out).zip a_rest).filterMap
                  (fun p => if p.snd = true then none else some p.fst)).map Nonplanar.mk) =
                Nonplanar.mk (Quotient.out x) ::
                  (((rest.map Quotient.out).zip a_rest).filterMap
                    (fun p => if p.snd = true then none else some p.fst)).map Nonplanar.mk from rfl]
            rw [ih a_rest]
            congr 1
            exact x.out_eq
    show (ff_tree.map Nonplanar.mk : List (Nonplanar α)) =
        ((Multiset.toList C).zip assn).filterMap (fun p => if p.snd = true then none else some p.fst)
    exact h_aux C.toList assn
  -- Step 8c.3: `(s.toList.map Q.out).map mk = s.toList` (Quotient.out_eq componentwise).
  have h_ft_canon_mk : ft_canon.map Nonplanar.mk = s_t.toList := by
    show (s_t.toList.map Quotient.out).map Nonplanar.mk = s_t.toList
    induction s_t.toList with
    | nil => rfl
    | cons hd tl ih =>
      show Nonplanar.mk (Quotient.out hd) :: ((tl.map Quotient.out).map Nonplanar.mk) =
           hd :: tl
      rw [ih]
      congr 1
      exact hd.out_eq
  have h_ff_canon_mk : ff_canon.map Nonplanar.mk = s_f.toList := by
    show (s_f.toList.map Quotient.out).map Nonplanar.mk = s_f.toList
    induction s_f.toList with
    | nil => rfl
    | cons hd tl ih =>
      show Nonplanar.mk (Quotient.out hd) :: ((tl.map Quotient.out).map Nonplanar.mk) =
           hd :: tl
      rw [ih]
      congr 1
      exact hd.out_eq
  -- Step 8c.4: Both `(ft_tree.map mk)` and `(ft_canon.map mk)` have multiset image `s_t`,
  -- hence are `Perm`-equivalent (via `Multiset.coe_eq_coe`).
  have h_ft_eq_coe : (↑(ft_tree.map Nonplanar.mk) : Multiset (Nonplanar α)) = s_t := by
    rw [h_ft_mk_eq, hs_t]
  have h_ff_eq_coe : (↑(ff_tree.map Nonplanar.mk) : Multiset (Nonplanar α)) = s_f := by
    rw [h_ff_mk_eq, hs_f]
  have h_ft_canon_eq_coe : (↑(ft_canon.map Nonplanar.mk) : Multiset (Nonplanar α)) = s_t := by
    rw [h_ft_canon_mk]; exact s_t.coe_toList
  have h_ff_canon_eq_coe : (↑(ff_canon.map Nonplanar.mk) : Multiset (Nonplanar α)) = s_f := by
    rw [h_ff_canon_mk]; exact s_f.coe_toList
  have h_ft_perm : (ft_tree.map Nonplanar.mk).Perm (ft_canon.map Nonplanar.mk) := by
    rw [← Multiset.coe_eq_coe, h_ft_eq_coe, h_ft_canon_eq_coe]
  have h_ff_perm : (ff_tree.map Nonplanar.mk).Perm (ff_canon.map Nonplanar.mk) := by
    rw [← Multiset.coe_eq_coe, h_ff_eq_coe, h_ff_canon_eq_coe]
  -- Step 8c.5: Apply guest-msform invariance to swap `Tree`-level guests for canonical.
  have h_iF_A : (Tree.Pathed.insertionForest
        (List.map Quotient.out (Multiset.toList A)) ft_tree).map msform =
      (Tree.Pathed.insertionForest
        (List.map Quotient.out (Multiset.toList A)) ft_canon).map msform :=
    Tree.Pathed.insertionForest_msform_invariance_guests _ h_ft_perm
  have h_iF_B : (Tree.Pathed.insertionForest
        (List.map Quotient.out (Multiset.toList B)) ff_tree).map msform =
      (Tree.Pathed.insertionForest
        (List.map Quotient.out (Multiset.toList B)) ff_canon).map msform :=
    Tree.Pathed.insertionForest_msform_invariance_guests _ h_ff_perm
  -- Step 8d: Use guest-msform invariance to align the canonical-guest form on the
  -- RHS back to the `Tree`-level guest form. Then both sides share `M_A` and `M_B` below.
  rw [← h_iF_A, ← h_iF_B]
  set M_A : Multiset (List (Tree α)) :=
    Tree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList A)) ft_tree with hM_A
  set M_B : Multiset (List (Tree α)) :=
    Tree.Pathed.insertionForest (List.map Quotient.out (Multiset.toList B)) ff_tree with hM_B
  -- Step 8e: Push msform through `(M_A ×ˢ M_B)`. Both sides expand via
  -- `Multiset.product = bind` and `msform (a ++ b) = msform a + msform b`.
  show (M_A.bind (fun a => M_B.map (Prod.mk a))).map (msform ∘ fun p => p.fst ++ p.snd) =
      ((M_A.map msform).bind (fun ma => (M_B.map msform).map (Prod.mk ma))).map
        (fun p => p.fst + p.snd)
  rw [Multiset.map_bind, Multiset.map_bind, Multiset.bind_map]
  refine Multiset.bind_congr fun a _ => ?_
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intros b _
  show msform (a ++ b) = msform a + msform b
  rw [hmsform]
  show (↑((a ++ b).map Nonplanar.mk) : Multiset (Nonplanar α)) =
       ↑(a.map Nonplanar.mk) + ↑(b.map Nonplanar.mk)
  rw [List.map_append, Multiset.coe_add]

/-- Generic lift of a `mk`-image `Perm` to a `Tree`-level `Perm` plus a list with
    matching `mk`-image. Inline copy of `Tree.Pathed.perm_lift_through_map`
    (private there) — pure list/Perm lemma, no rooted-tree content. -/
private theorem perm_lift_mk {l₂ l₁ : List (Tree α)}
    (h : (l₁.map Nonplanar.mk).Perm (l₂.map Nonplanar.mk)) :
    ∃ l_mid : List (Tree α),
      l₁.Perm l_mid ∧ l_mid.map Nonplanar.mk = l₂.map Nonplanar.mk := by
  induction l₂ generalizing l₁ with
  | nil =>
    rw [List.map_nil] at h
    have h_eq : l₁.map Nonplanar.mk = [] := h.eq_nil
    have hl₁ : l₁ = [] := List.map_eq_nil_iff.mp h_eq
    exact ⟨[], hl₁ ▸ List.Perm.refl _, by simp⟩
  | cons b l₂_rest ih =>
    have hfb_mem : Nonplanar.mk b ∈ l₁.map Nonplanar.mk := by
      apply h.symm.subset
      rw [List.map_cons]
      exact List.mem_cons_self
    obtain ⟨a, ha_mem, hfa_eq⟩ := List.mem_map.mp hfb_mem
    letI : DecidableEq (Tree α) := Classical.decEq _
    have hperm_l₁ : l₁.Perm (a :: l₁.erase a) := List.perm_cons_erase ha_mem
    have h' : ((a :: l₁.erase a).map Nonplanar.mk).Perm
        ((b :: l₂_rest).map Nonplanar.mk) :=
      (hperm_l₁.map Nonplanar.mk).symm.trans h
    rw [List.map_cons, List.map_cons] at h'
    rw [hfa_eq] at h'
    have h_inner : ((l₁.erase a).map Nonplanar.mk).Perm
        (l₂_rest.map Nonplanar.mk) := h'.cons_inv
    obtain ⟨l_mid_rest, hperm_rest, hmap_rest⟩ := ih h_inner
    refine ⟨a :: l_mid_rest, ?_, ?_⟩
    · exact hperm_l₁.trans (hperm_rest.cons a)
    · rw [List.map_cons, List.map_cons, hfa_eq, hmap_rest]

/-- A `mk`-equality on lists `l₁.map mk = l₂.map mk` lifts to componentwise
    `Forall₂ PermEquiv l₁ l₂`. -/
private theorem forall2_permEquiv_of_map_mk_eq :
    ∀ {l₁ l₂ : List (Tree α)},
      l₁.map Nonplanar.mk = l₂.map Nonplanar.mk →
      List.Forall₂ Tree.PermEquiv l₁ l₂
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    exact List.Forall₂.cons
      (Nonplanar.mk_eq_mk_iff.mp h.1)
      (forall2_permEquiv_of_map_mk_eq h.2)

/-- `Forall₂ PermEquiv` is symmetric (componentwise symmetry of `PermEquiv`). -/
private theorem forall2_permEquiv_symm :
    ∀ {l₁ l₂ : List (Tree α)},
      List.Forall₂ Tree.PermEquiv l₁ l₂ →
      List.Forall₂ Tree.PermEquiv l₂ l₁
  | [], [], _ => List.Forall₂.nil
  | x :: xs, y :: ys, h => by
    cases h with
    | cons hd tl => exact List.Forall₂.cons hd.symm (forall2_permEquiv_symm tl)

/-- **Representative invariance for NIM**: `Nonplanar.insertionMultiset F G`
    can be computed on ANY `Tree`-level representative lists `hosts`, `guests`
    whose `mk`-image multisets are `F` and `G` respectively — not just the
    canonical `toList.map Quotient.out` reps.

    This is the workhorse for descents that need to swap canonical reps for
    a convenient `Tree`-level list (e.g. `Q.out v :: B.toList.map Q.out` standing
    in for `(B + {v}).toList.map Q.out`). -/
theorem _root_.RootedTree.Nonplanar.insertionMultiset_eq_of_reps
    (F G : Forest (Nonplanar α)) (hosts guests : List (Tree α))
    (h_hosts : (Multiset.ofList (hosts.map Nonplanar.mk) :
      Multiset (Nonplanar α)) = F)
    (h_guests : (Multiset.ofList (guests.map Nonplanar.mk) :
      Multiset (Nonplanar α)) = G) :
    Nonplanar.insertionMultiset F G =
      (Tree.Pathed.insertionForest hosts guests).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
  -- §1: Canonical reps' mk-images recover the multiset's toList.
  have h_canon_hosts_mk :
      (F.toList.map Quotient.out).map Nonplanar.mk = F.toList := by
    induction F.toList with
    | nil => rfl
    | cons hd tl ih =>
      show Nonplanar.mk (Quotient.out hd) ::
          ((tl.map Quotient.out).map Nonplanar.mk) = hd :: tl
      rw [ih]
      congr 1
      exact hd.out_eq
  have h_canon_guests_mk :
      (G.toList.map Quotient.out).map Nonplanar.mk = G.toList := by
    induction G.toList with
    | nil => rfl
    | cons hd tl ih =>
      show Nonplanar.mk (Quotient.out hd) ::
          ((tl.map Quotient.out).map Nonplanar.mk) = hd :: tl
      rw [ih]
      congr 1
      exact hd.out_eq
  -- §2: Perm of mk-images at the host and guest level.
  have h_hosts_perm :
      (hosts.map Nonplanar.mk).Perm
        ((F.toList.map Quotient.out).map Nonplanar.mk) := by
    apply Multiset.coe_eq_coe.mp
    rw [h_hosts, h_canon_hosts_mk]
    exact F.coe_toList.symm
  -- §3: Lift the host mk-Perm to a `Tree`-level Perm + Forall₂ PermEquiv bridge.
  obtain ⟨hosts_mid, h_hosts_tree_perm, h_hosts_map_eq⟩ :=
    perm_lift_mk h_hosts_perm
  have h_hosts_forall :
      List.Forall₂ Tree.PermEquiv hosts_mid (F.toList.map Quotient.out) :=
    forall2_permEquiv_of_map_mk_eq h_hosts_map_eq
  -- §4: Unfold NIM (canonical reps) and bridge via host-Perm + host-PermEquiv.
  unfold Nonplanar.insertionMultiset
  -- Bridge from `(canon_hosts) gs_canon` back to `(hosts) guests`:
  --   canon_hosts ←(Forall₂ PermEquiv, symm)← hosts_mid ←(Perm, symm)← hosts
  -- For guests, use `insertionForest_msform_invariance_guests` directly.
  have h_guests_perm_mk :
      (guests.map Nonplanar.mk).Perm
        ((G.toList.map Quotient.out).map Nonplanar.mk) := by
    apply Multiset.coe_eq_coe.mp
    rw [h_guests, h_canon_guests_mk]
    exact G.coe_toList.symm
  -- Swap canonical hosts for `hosts_mid` (PermEquiv host invariance).
  have h_step1 :
      (Tree.Pathed.insertionForest (F.toList.map Quotient.out)
          (G.toList.map Quotient.out)).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
      (Tree.Pathed.insertionForest hosts_mid
          (G.toList.map Quotient.out)).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) := by
    have h2 := congrArg
      (Multiset.map (fun l : List (Nonplanar α) =>
        (Multiset.ofList l : Multiset (Nonplanar α))))
      (Tree.Pathed.insertionForest_permEquiv_host
        (G.toList.map Quotient.out) (forall2_permEquiv_symm h_hosts_forall))
    -- h2 : map (ofList) (iF mid gs .map (List.map mk)) = map (ofList) (iF canon gs .map (List.map mk))
    -- Collapse the inner map composition.
    rw [Multiset.map_map, Multiset.map_map] at h2
    -- h2 : map (ofList ∘ List.map mk) (iF mid gs) = map (ofList ∘ List.map mk) (iF canon gs)
    -- Goal uses `fun L => ofList (L.map mk)`. These are eta-equal; use `show`.
    show (Tree.Pathed.insertionForest (F.toList.map Quotient.out)
          (G.toList.map Quotient.out)).map
        ((fun l : List (Nonplanar α) => (Multiset.ofList l : Multiset (Nonplanar α)))
          ∘ List.map Nonplanar.mk) =
      (Tree.Pathed.insertionForest hosts_mid
          (G.toList.map Quotient.out)).map
        ((fun l : List (Nonplanar α) => (Multiset.ofList l : Multiset (Nonplanar α)))
          ∘ List.map Nonplanar.mk)
    exact h2
  -- Swap `hosts_mid` for `hosts` (`Tree`-level Perm of hosts).
  have h_step2 :
      (Tree.Pathed.insertionForest hosts_mid
          (G.toList.map Quotient.out)).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
      (Tree.Pathed.insertionForest hosts
          (G.toList.map Quotient.out)).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) :=
    Tree.Pathed.insertionForest_perm_host_msform
      h_hosts_tree_perm.symm (G.toList.map Quotient.out)
  -- Swap canonical guests for `guests` (mk-Perm of guests via the guest lemma).
  have h_step3 :
      (Tree.Pathed.insertionForest hosts
          (G.toList.map Quotient.out)).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) =
      (Tree.Pathed.insertionForest hosts guests).map
        (fun L => Multiset.ofList (L.map Nonplanar.mk)) :=
    (Tree.Pathed.insertionForest_msform_invariance_guests hosts
      h_guests_perm_mk).symm
  exact h_step1.trans (h_step2.trans h_step3)

/-- **Deep substrate**: NIM-level singleton-guest associativity.

    `(NIM A B).bind (X ↦ NIM X {v}) = NIM A (B + {v}) + (NIM B {v}).bind (X' ↦ NIM A X')`

    Proved by descent from the raw `Tree`-level identity
    `Tree.Pathed.insertionForest_bind_singleton`. The descent uses the
    representative-invariance lemma
    `Nonplanar.insertionMultiset_eq_of_reps` per-output to swap NIM applied
    to a `Tree`-level output `msform L` for the `Tree`-level engine applied to `L`. -/
theorem _root_.RootedTree.Nonplanar.insertionMultiset_singleton_assoc
    (A B : Forest (Nonplanar α)) (v : Nonplanar α) :
    (Nonplanar.insertionMultiset A B).bind
        (fun X => Nonplanar.insertionMultiset X {v}) =
      Nonplanar.insertionMultiset A (B + {v}) +
      (Nonplanar.insertionMultiset B {v}).bind
        (fun X' => Nonplanar.insertionMultiset A X') := by
  -- Canonical `Tree`-level reps.
  set A_pl : List (Tree α) := A.toList.map Quotient.out with hA_pl
  set B_pl : List (Tree α) := B.toList.map Quotient.out with hB_pl
  set ov : Tree α := Quotient.out v with hov
  -- Abbreviation for the msform post-map (`List (Tree α) → Forest (Nonplanar α)`).
  set msform : List (Tree α) → Forest (Nonplanar α) :=
    fun L => Multiset.ofList (L.map Nonplanar.mk) with hmsform
  -- Key fact: for any `Tree`-level list `L`, `(L.map mk : Multiset _) = msform L`.
  -- (Used to discharge rep-lemma hypotheses for inner NIMs.)
  have h_msform_eq : ∀ L : List (Tree α),
      (Multiset.ofList (L.map Nonplanar.mk) : Multiset (Nonplanar α)) = msform L :=
    fun L => rfl
  -- §1: LHS = ((iF A_pl B_pl).bind (fun L => iF L [ov])).map msform.
  -- Step 1a: unfold the outer NIM, then push bind through the outer .map msform.
  have h_lhs_outer : Nonplanar.insertionMultiset A B =
      (Tree.Pathed.insertionForest A_pl B_pl).map msform := rfl
  -- Step 1b: per `Tree`-level host output L, NIM (msform L) {v} = (iF L [ov]).map msform.
  have h_inner_NIM : ∀ L : List (Tree α),
      Nonplanar.insertionMultiset (msform L) {v} =
        (Tree.Pathed.insertionForest L [ov]).map msform := by
    intro L
    apply Nonplanar.insertionMultiset_eq_of_reps
    · -- hosts hyp: ofList (L.map mk) = msform L
      rfl
    · -- guests hyp: ofList ([ov].map mk) = {v}.
      show (Multiset.ofList ([Nonplanar.mk ov]) : Multiset (Nonplanar α)) = ({v} : Multiset _)
      rw [hov, show Nonplanar.mk (Quotient.out v) = v from Quotient.out_eq v]
      rfl
  -- Step 1c: collapse the LHS.
  have h_lhs :
      (Nonplanar.insertionMultiset A B).bind
        (fun X => Nonplanar.insertionMultiset X {v}) =
      ((Tree.Pathed.insertionForest A_pl B_pl).bind
        (fun L => Tree.Pathed.insertionForest L [ov])).map msform := by
    rw [h_lhs_outer, Multiset.bind_map]
    -- Goal: (iF A_pl B_pl).bind (fun L => NIM (msform L) {v})
    --     = ((iF A_pl B_pl).bind (fun L => iF L [ov])).map msform
    rw [Multiset.map_bind]
    refine Multiset.bind_congr fun L _ => ?_
    exact h_inner_NIM L
  -- §2: Apply the `Tree`-level engine and split via Multiset.map_add.
  rw [h_lhs, Tree.Pathed.insertionForest_bind_singleton, Multiset.map_add]
  -- Now the goal has two summands matching the RHS shape. Prove each.
  congr 1
  · -- Summand 1: (iF A_pl (ov :: B_pl)).map msform = NIM A (B + {v}).
    symm
    apply Nonplanar.insertionMultiset_eq_of_reps
    · -- hosts hyp: ofList (A_pl.map mk) = A.
      show (Multiset.ofList ((A.toList.map Quotient.out).map Nonplanar.mk) :
            Multiset (Nonplanar α)) = A
      rw [List.map_map]
      have h_id : A.toList.map (Nonplanar.mk ∘ Quotient.out) = A.toList :=
        (List.map_congr_left fun x _ => Quotient.out_eq x).trans (List.map_id _)
      rw [h_id]
      exact A.coe_toList
    · -- guests hyp: ofList ((ov :: B_pl).map mk) = B + {v}.
      show (Multiset.ofList ((Quotient.out v :: B.toList.map Quotient.out).map Nonplanar.mk) :
            Multiset (Nonplanar α)) = B + {v}
      rw [List.map_cons, List.map_map]
      have h_id_B : B.toList.map (Nonplanar.mk ∘ Quotient.out) = B.toList :=
        (List.map_congr_left fun x _ => Quotient.out_eq x).trans (List.map_id _)
      rw [h_id_B]
      show ((Nonplanar.mk (Quotient.out v) :: B.toList : List (Nonplanar α)) :
            Multiset (Nonplanar α)) = B + {v}
      rw [show Nonplanar.mk (Quotient.out v) = v from Quotient.out_eq v]
      -- (↑(v :: B.toList) : Multiset _) = v ::ₘ ↑B.toList = v ::ₘ B
      rw [show ((v :: B.toList : List (Nonplanar α)) : Multiset (Nonplanar α)) =
          v ::ₘ (↑B.toList : Multiset (Nonplanar α)) from rfl, B.coe_toList]
      -- Goal: v ::ₘ B = B + {v}.
      rw [add_comm B, Multiset.singleton_add]
  · -- Summand 2: ((iF B_pl [ov]).bind (fun B' => iF A_pl B')).map msform
    --          = (NIM B {v}).bind (NIM A ·)
    -- Push msform through the outer bind, then apply rep lemma per B'.
    rw [Multiset.map_bind]
    -- Goal: (iF B_pl [ov]).bind (fun B' => (iF A_pl B').map msform) = ...
    -- Per B', (iF A_pl B').map msform = NIM A (msform B') by rep lemma.
    have h_inner_NIM_A : ∀ B' : List (Tree α),
        (Tree.Pathed.insertionForest A_pl B').map msform =
          Nonplanar.insertionMultiset A (msform B') := by
      intro B'
      symm
      apply Nonplanar.insertionMultiset_eq_of_reps
      · -- hosts hyp: ofList (A_pl.map mk) = A.
        show (Multiset.ofList ((A.toList.map Quotient.out).map Nonplanar.mk) :
              Multiset (Nonplanar α)) = A
        rw [List.map_map]
        have h_id : A.toList.map (Nonplanar.mk ∘ Quotient.out) = A.toList :=
          (List.map_congr_left fun x _ => Quotient.out_eq x).trans (List.map_id _)
        rw [h_id]
        exact A.coe_toList
      · -- guests hyp: ofList (B'.map mk) = msform B'.
        rfl
    -- RHS: (NIM B {v}).bind (NIM A ·). Outer NIM B {v} unfolds to (iF B_pl [ov]).map msform
    -- via the rep lemma at the canonical reps for B (canonical) and [ov] for {v}.
    have h_outer_NIM_B :
        Nonplanar.insertionMultiset B {v} =
          (Tree.Pathed.insertionForest B_pl [ov]).map msform := by
      apply Nonplanar.insertionMultiset_eq_of_reps
      · -- hosts hyp: ofList (B_pl.map mk) = B.
        show (Multiset.ofList ((B.toList.map Quotient.out).map Nonplanar.mk) :
              Multiset (Nonplanar α)) = B
        rw [List.map_map]
        have h_id : B.toList.map (Nonplanar.mk ∘ Quotient.out) = B.toList :=
          (List.map_congr_left fun x _ => Quotient.out_eq x).trans (List.map_id _)
        rw [h_id]
        exact B.coe_toList
      · -- guests hyp: ofList ([ov].map mk) = {v}.
        show (Multiset.ofList ([Nonplanar.mk (Quotient.out v)]) :
              Multiset (Nonplanar α)) = ({v} : Multiset _)
        rw [show Nonplanar.mk (Quotient.out v) = v from Quotient.out_eq v]
        rfl
    rw [h_outer_NIM_B, Multiset.bind_map]
    -- Now both sides are (iF B_pl [ov]).bind (something). Use bind_congr.
    refine Multiset.bind_congr fun B' _ => ?_
    exact h_inner_NIM_A B'

/-- **Prop 2.7.iii** (Oudom-Guin 2004): for basis forests A, B, C, the
    multi-graft of `(A · B)` (disjoint-union product) into `C` distributes
    as a sum over partitions of C, with each part inserted into A vs B
    independently.

    `(A · B) ∘ C = Σ_{C₁ ⊆ C} (A ∘ C₁) · (B ∘ (C - C₁))`

    Proved from `insertionMultiset_add_host` + bilinearity of CK's
    disjoint-union product `·`. -/
theorem insertion_mul_distrib (A B C : Forest (Nonplanar α)) :
    insertion (R := R) (of' (A + B)) (of' C) =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       C.powerset.map fun C₁ =>
        op (unop (insertion (of' A) (of' C₁)) *
            unop (insertion (of' B) (of' (C - C₁))))).sum := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- Unfold `insertion (of' F) (of' G)` to `insertionBasis F G = (NIM F G).map of' |>.sum`.
  simp_rw [insertion_of'_of']
  unfold insertionBasis
  -- LHS: `((NIM (A+B) C).map of').sum`. RHS: nested product/sum.
  rw [Nonplanar.insertionMultiset_add_host A B C]
  -- LHS: ((powerset.bind ...).map of').sum
  rw [Multiset.map_bind, Multiset.sum_bind]
  -- Inside the bind:
  -- ((NIM A C₁) ×ˢ (NIM B (C - C₁))).map (uncurry +)).map of' |>.sum
  --   = (NIM A C₁).bind (fun X_A => (NIM B (C - C₁)).map (fun X_B => of' (X_A + X_B)))).sum
  --   = ... (op/unop = id, of' (X + Y) = of' X · of' Y)
  --   = op (unop ((NIM A C₁).map of').sum * unop ((NIM B (C - C₁)).map of').sum)
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intros C₁ _
  -- Inner equality: prove for fixed C₁.
  -- LHS_inner: (((NIM A C₁) ×ˢ (NIM B (C-C₁))).map (fun p => p.1 + p.2)).map of' |>.sum
  -- RHS_inner: op (unop ((NIM A C₁).map of' |>.sum) * unop ((NIM B (C-C₁)).map of' |>.sum))
  rw [Multiset.map_map]
  -- Reduce to a CK-level identity.
  set M_A := Nonplanar.insertionMultiset A C₁ with hM_A
  set M_B := Nonplanar.insertionMultiset B (C - C₁) with hM_B
  -- Retype LHS to CK using definitional equality `GrossmanLarson R α = CK R (Nonplanar α)`:
  show (((M_A ×ˢ M_B).map (fun p =>
        (ConnesKreimer.of' (R := R) (p.1 + p.2) :
          ConnesKreimer R (Nonplanar α))))).sum =
      ((M_A.map (fun F' => ConnesKreimer.of' (R := R) F')).sum) *
      ((M_B.map (fun F' => ConnesKreimer.of' (R := R) F')).sum)
  -- Distribute of' (X + Y) = of' X * of' Y in CK.
  simp_rw [ConnesKreimer.of'_add]
  -- Helper: bilinearity of `Σ (·) · Σ (·)` over Multiset.product, by induction on M_A.
  clear hM_A
  induction M_A using Multiset.induction with
  | empty =>
    simp only [Multiset.zero_product, Multiset.map_zero, Multiset.sum_zero, zero_mul]
  | cons a s ih =>
    simp only [Multiset.cons_product, Multiset.map_add, Multiset.sum_add,
               Multiset.map_map, Function.comp_def, Multiset.map_cons,
               Multiset.sum_cons]
    -- Inner: ((M_B.map (Prod.mk a)).map (fun p => of' p.1 * of' p.2)).sum
    --      = (M_B.map (fun b => of' a * of' b)).sum = of' a * S_B
    rw [Multiset.sum_map_mul_left]
    -- Apply IH to the second summand.
    rw [ih]
    -- Goal: of' a * S_B + (s.map of').sum * S_B = (of' a + (s.map of').sum) * S_B
    rw [add_mul]

/-! ### §3: Cocommutativity of the shuffle sum

The sum-over-`powerset` is symmetric under the partition swap
`(C₁, C - C₁) ↔ (C - C₁, C₁)`, since `Multiset.powerset` is closed under
complement. This is the "cocommutativity of Δ" component of Lemma 2.10.
-/

/-- **Cocommutativity of shuffle Δ**: a sum over `C.powerset` is invariant
    under the partition swap.

    Specifically: `Σ_{C₁ ⊆ C} f(C₁, C - C₁) = Σ_{C₁ ⊆ C} f(C - C₁, C₁)`
    where the implicit complementation is a bijection on `C.powerset`.

    Used in Lemma 2.10's chain to reindex one of the three triple-partition
    sums for `B_(2) ∘ C` matching. -/
theorem powerset_partition_swap {β : Type*} [AddCommMonoid β]
    (C : Forest (Nonplanar α)) (f : Forest (Nonplanar α) → Forest (Nonplanar α) → β) :
    (letI : DecidableEq (Nonplanar α) := Classical.decEq _
     C.powerset.map fun C₁ => f C₁ (C - C₁)).sum =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       C.powerset.map fun C₁ => f (C - C₁) C₁).sum :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  Multiset.powerset_partition_swap C f

/-! ### §4: Closing `mul_assoc_basis` via Oudom-Guin Lemma 2.10's chain

The 6-line algebraic chain:
```
(A * B) * C = (((A ∘ B_(1)) B_(2)) ∘ C_(1)) C_(2)         — def of *
            = ((A ∘ B_(1)) ∘ C_(1))(B_(2) ∘ C_(2)) C_(3)   — insertion_mul_distrib
            = (A ∘ ((B_(1) ∘ C_(1)) C_(2)))(B_(2) ∘ C_(3)) C_(4)  — insertion_assoc_shuffled
            = (A ∘ ((B_(1) ∘ C_(1)) C_(3)))(B_(2) ∘ C_(2)) C_(4)  — powerset_partition_swap (on C-trio)
            = A * ((B ∘ C_(1)) C_(2))                              — def of *
            = A * (B * C)
```

The trio re-indexing on C uses `powerset_partition_swap` to swap the
"goes into B_(1)" piece of C with the "goes into B_(2)" piece, which
re-pairs the four-way C-partition into the right form for the RHS.
-/

/-! ### §4a: Generalized building blocks

The chain manipulates GL elements that are themselves *sums* of basis
vectors (the output of `insertion`, a sum-over-partition, ...). To keep
the chain's rewrites compositional, we lift two basis-form identities to
LinearMap-general form via standard linearity arguments.

The lifts are routine `Finsupp.induction_linear` (zero / additive /
scalar-of-basis) reductions to the basis form. -/

/-- Push `X * of' G` to the explicit powerset sum form for ANY `X`.
    Generalization of `of'_mul_of'` + `productForest` unfolding to non-basis
    LEFT factor.

    Stated via `product` (the bilinear underlying map of `*`) to avoid
    Finsupp/GrossmanLarson type-alias mismatches in the induction. -/
theorem product_of'_sum_form (X : GrossmanLarson R α) (G : Forest (Nonplanar α)) :
    product X (of' G) =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       G.powerset.map fun G₁ =>
        op (unop (insertion X (of' G₁)) *
            unop (of' (G - G₁)))).sum := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  refine Finsupp.induction_linear (M := R) X ?_ ?_ ?_
  · -- X = 0
    have h_prod_zero : (product : GrossmanLarson R α →ₗ[R] _) 0 (of' G) =
        (0 : GrossmanLarson R α) := by
      rw [(product : GrossmanLarson R α →ₗ[R] _).map_zero]
      rfl
    -- Convert goal to match (the 0 cast issue): explicit show.
    show (product : GrossmanLarson R α →ₗ[R] _) (0 : GrossmanLarson R α) (of' G) = _
    rw [h_prod_zero]
    symm
    apply Multiset.sum_eq_zero
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨G₁, _, hG₁_eq⟩ := hx
    rw [← hG₁_eq]
    have h_ins0 : insertion (R := R) (0 : GrossmanLarson R α) (of' G₁) = 0 := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' G₁)).map_zero
      exact this
    -- `0 : GL` and `0 : Forest →₀ R` are the same; pass through.
    show op (unop (insertion (0 : GrossmanLarson R α) (of' G₁)) *
        unop (of' (R := R) (G - G₁))) = 0
    rw [h_ins0]
    show op ((0 : ConnesKreimer R (Nonplanar α)) *
        unop (of' (R := R) (G - G₁))) = 0
    rw [zero_mul]; rfl
  · -- additive
    intro X₁ X₂ ih₁ ih₂
    -- Use the underlying AddMonoidHom of the LinearMap to apply map_add.
    have h_prod_add : product (X₁ + X₂) (of' G) =
        product X₁ (of' G) + product X₂ (of' G) :=
      AddMonoidHom.map_add
        ((product : GrossmanLarson R α →ₗ[R] _).flip (of' G)).toAddMonoidHom X₁ X₂
    rw [h_prod_add, ih₁, ih₂, ← Multiset.sum_map_add]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro G₁ _
    -- Goal is at the inner level; X₁ + X₂ in insertion is on Finsupp.
    show op (unop (insertion (X₁ : GrossmanLarson R α) (of' G₁)) *
              unop (of' (R := R) (G - G₁))) +
        op (unop (insertion (X₂ : GrossmanLarson R α) (of' G₁)) *
            unop (of' (R := R) (G - G₁))) =
        op (unop (insertion ((X₁ + X₂ : GrossmanLarson R α)) (of' G₁)) *
            unop (of' (R := R) (G - G₁)))
    have h_split_ins : insertion (R := R) ((X₁ + X₂) : GrossmanLarson R α) (of' G₁) =
        insertion (R := R) (X₁ : GrossmanLarson R α) (of' G₁) +
        insertion (R := R) (X₂ : GrossmanLarson R α) (of' G₁) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' G₁)).map_add
          (X₁ : GrossmanLarson R α) (X₂ : GrossmanLarson R α)
      exact this
    rw [h_split_ins]
    show op (unop (insertion (X₁ : GrossmanLarson R α) (of' G₁)) *
              unop (of' (R := R) (G - G₁))) +
        op (unop (insertion (X₂ : GrossmanLarson R α) (of' G₁)) *
            unop (of' (R := R) (G - G₁))) =
        op ((unop (insertion (X₁ : GrossmanLarson R α) (of' G₁)) +
             unop (insertion (X₂ : GrossmanLarson R α) (of' G₁))) *
             unop (of' (R := R) (G - G₁)))
    rw [add_mul]; rfl
  · -- single basis: reduce to of'_mul_of'.
    intro A c
    -- Single A c = c • (single A 1) = c • of' A (via Finsupp.smul_single_one).
    show product ((Finsupp.single A c : GrossmanLarson R α)) (of' G) = _
    rw [show ((Finsupp.single A c : Forest (Nonplanar α) →₀ R) :
            GrossmanLarson R α) = c • (of' A : GrossmanLarson R α)
        from (Finsupp.smul_single_one A c).symm]
    rw [product.map_smul, LinearMap.smul_apply]
    -- Goal: c • product (of' A) (of' G) = (sum form with c • of' A)
    show c • ((of' A : GrossmanLarson R α) * of' G) = _
    rw [of'_mul_of']
    show c • productForest (of' (R := R) A) G =
        (G.powerset.map fun G₁ =>
          op (unop (insertion (c • (of' (R := R) A : GrossmanLarson R α)) (of' G₁)) *
              unop (of' (R := R) (G - G₁)))).sum
    show c • (G.powerset.map fun G₁ =>
              op (unop (insertion (of' (R := R) A) (of' G₁)) *
                  unop (of' (R := R) (G - G₁)))).sum =
        (G.powerset.map fun G₁ =>
          op (unop (insertion (c • (of' (R := R) A : GrossmanLarson R α)) (of' G₁)) *
              unop (of' (R := R) (G - G₁)))).sum
    rw [Multiset.smul_sum, Multiset.map_map]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro G₁ _
    have h_smul : insertion (R := R) (c • (of' A : GrossmanLarson R α)) (of' G₁) =
        c • insertion (R := R) (of' A) (of' G₁) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' G₁)).map_smul c (of' A)
      exact this
    rw [h_smul]
    show c • op (unop (insertion (of' (R := R) A) (of' G₁)) *
                  unop (of' (R := R) (G - G₁))) =
        op ((c • unop (insertion (of' (R := R) A) (of' G₁))) *
            unop (of' (R := R) (G - G₁)))
    rw [smul_mul_assoc]; rfl

/-- Corollary: `mul_of'_sum_form` (the `*` form, given by `mul_def`). -/
theorem mul_of'_sum_form (X : GrossmanLarson R α) (G : Forest (Nonplanar α)) :
    X * of' G =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       G.powerset.map fun G₁ =>
        op (unop (insertion X (of' G₁)) *
            unop (of' (G - G₁)))).sum :=
  product_of'_sum_form X G

/-- LEFT-form distributivity of `*` over `Multiset.sum`:
    `(of' A) * (Σ s) = Σ ((of' A) * s_i)`. The Grossman-Larson product
    `*` is bilinear (via `product : GL →ₗ[R] GL →ₗ[R] GL`), so pushing
    through `Multiset.sum` is straightforward — the `Mul` instance
    rewires `*` as `product`, and `product (of' A)` is a `LinearMap`.

    Mirror of `insertion_sum_right` but for the GL product. Used in
    Lemma 2.10's chain to expand `(of' A) * (B * C)` after substituting
    `B * C` as a sum-form. -/
theorem of'_mul_sum_form (A : Forest (Nonplanar α))
    (s : Multiset (GrossmanLarson R α)) :
    (of' A : GrossmanLarson R α) * s.sum = (s.map (fun X => of' A * X)).sum := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.sum_zero, Multiset.map_zero, Multiset.sum_zero]
    show product (of' A) (0 : GrossmanLarson R α) = 0
    exact (product (of' A : GrossmanLarson R α)).map_zero
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
    show product (of' A) (a + s.sum) = product (of' A) a + (s.map _).sum
    rw [(product (of' A : GrossmanLarson R α)).map_add]
    -- Goal: product (of' A) a + product (of' A) s.sum = product (of' A) a + (s.map (fun X => of' A * X)).sum
    -- IH: (of' A) * s.sum = (s.map ...).sum. (of' A) * s.sum = product (of' A) s.sum by `mul_def`.
    show (product (of' A : GrossmanLarson R α)) a +
         ((of' A : GrossmanLarson R α) * s.sum) = _
    rw [ih]

/-- `insertion` distributes over a `Multiset.sum` in its first argument
    (since the LinearMap on the first arg pushes through Multiset.sum). -/
theorem insertion_sum_left (s : Multiset (GrossmanLarson R α))
    (G : GrossmanLarson R α) :
    insertion (R := R) s.sum G = (s.map (fun X => insertion X G)).sum := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.sum_zero, Multiset.map_zero, Multiset.sum_zero]
    show ((insertion : GrossmanLarson R α →ₗ[R] _).flip G) 0 = 0
    exact LinearMap.map_zero _
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
    show ((insertion : GrossmanLarson R α →ₗ[R] _).flip G) (a + s.sum) = _
    rw [LinearMap.map_add]
    show insertion a G + insertion s.sum G =
         insertion a G + (s.map (fun X => insertion X G)).sum
    rw [ih]

/-- `insertion` distributes over a `Multiset.sum` in its second argument. -/
theorem insertion_sum_right (F : GrossmanLarson R α)
    (s : Multiset (GrossmanLarson R α)) :
    insertion (R := R) F s.sum = (s.map (fun Y => insertion F Y)).sum := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.sum_zero, Multiset.map_zero, Multiset.sum_zero]
    exact LinearMap.map_zero _
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
        LinearMap.map_add, ih]

/-- Generalized `insertion_mul_distrib`: the bracketed LEFT factor of
    `μ(X, of' Y)` may be any GL element. Reduces by linearity in `X` to
    the basis case `insertion_mul_distrib`. -/
theorem insertion_mul_distrib_gen
    (X : GrossmanLarson R α) (Y C : Forest (Nonplanar α)) :
    insertion (R := R) (op (unop X * unop (of' Y))) (of' C) =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       C.powerset.map fun C₁ =>
        op (unop (insertion X (of' C₁)) *
            unop (insertion (of' Y) (of' (C - C₁))))).sum := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  refine Finsupp.induction_linear X ?_ ?_ ?_
  · -- X = 0 case: both sides reduce to 0.
    -- LHS = insertion (op (0 * unop (of' Y))) (of' C) = insertion 0 (of' C) = 0
    -- RHS = each summand `op(0 * ...) = 0`, hence sum = 0.
    show insertion (R := R) (op (unop (0 : GrossmanLarson R α) *
            unop (of' (R := R) Y))) (of' C) = _
    rw [show unop (0 : GrossmanLarson R α) =
        (0 : ConnesKreimer R (Nonplanar α)) from rfl]
    rw [zero_mul]
    rw [show op (0 : ConnesKreimer R (Nonplanar α)) =
            (0 : GrossmanLarson R α) from rfl]
    have h_ins0_C : insertion (R := R) (0 : GrossmanLarson R α) (of' C) =
        (0 : GrossmanLarson R α) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' C)).map_zero
      exact this
    rw [h_ins0_C]
    symm
    apply Multiset.sum_eq_zero
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨C₁, _, hC₁_eq⟩ := hx
    rw [← hC₁_eq]
    show op (unop (insertion (R := R) (0 : GrossmanLarson R α) (of' C₁)) *
              unop (insertion (of' (R := R) Y) (of' (C - C₁)))) = 0
    have h_ins0 : insertion (R := R) (0 : GrossmanLarson R α) (of' C₁) =
        (0 : GrossmanLarson R α) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' C₁)).map_zero
      exact this
    rw [h_ins0]
    show op ((0 : ConnesKreimer R (Nonplanar α)) *
        unop (insertion (of' (R := R) Y) (of' (C - C₁)))) = 0
    rw [zero_mul]; rfl
  · -- X = X₁ + X₂ additive case
    intro X₁ X₂ ih₁ ih₂
    rw [show unop (X₁ + X₂) = unop X₁ + unop X₂ from rfl, add_mul]
    rw [show op (unop X₁ * unop (of' (R := R) Y) +
                 unop X₂ * unop (of' (R := R) Y) : ConnesKreimer R (Nonplanar α)) =
            op (unop X₁ * unop (of' (R := R) Y)) +
            op (unop X₂ * unop (of' (R := R) Y)) from rfl]
    rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_add, LinearMap.add_apply,
        ih₁, ih₂, ← Multiset.sum_map_add]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro C₁ _
    -- Now: RHS_inner_X₁(C₁) + RHS_inner_X₂(C₁) = RHS_inner_(X₁+X₂)(C₁)
    -- Rewrite insertion (X₁+X₂) on RHS via bilinearity.
    have h_split : insertion (R := R) (X₁ + X₂) (of' C₁) =
        insertion (R := R) X₁ (of' C₁) + insertion (R := R) X₂ (of' C₁) := by
      have := ((insertion : GrossmanLarson R α →ₗ[R]
        GrossmanLarson R α →ₗ[R] GrossmanLarson R α).flip (of' C₁)).map_add X₁ X₂
      exact this
    rw [h_split]
    show op (unop (insertion X₁ (of' C₁)) *
            unop (insertion (of' (R := R) Y) (of' (C - C₁)))) +
        op (unop (insertion X₂ (of' C₁)) *
            unop (insertion (of' (R := R) Y) (of' (C - C₁)))) =
        op ((unop (insertion X₁ (of' C₁)) +
             unop (insertion X₂ (of' C₁))) *
             unop (insertion (of' (R := R) Y) (of' (C - C₁))))
    rw [add_mul]; rfl
  · -- single A c basis case
    intro A c
    rw [show (Finsupp.single A c : GrossmanLarson R α) = c • (of' A : GrossmanLarson R α)
        from (Finsupp.smul_single_one A c).symm]
    rw [show unop (c • (of' A : GrossmanLarson R α)) =
            c • unop (of' (R := R) A) from rfl]
    rw [smul_mul_assoc]
    rw [show op (c • (unop (of' (R := R) A) * unop (of' (R := R) Y))) =
            c • op (unop (of' (R := R) A) * unop (of' (R := R) Y)) from rfl]
    rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_smul, LinearMap.smul_apply]
    -- op (unop (of' A) * unop (of' Y)) = of' (A + Y)
    rw [show op (unop (of' (R := R) A) * unop (of' (R := R) Y)) =
            (of' (R := R) (A + Y) : GrossmanLarson R α) from by
          show (ConnesKreimer.of' (R := R) A : ConnesKreimer R (Nonplanar α)) *
                ConnesKreimer.of' (R := R) Y = ConnesKreimer.of' (R := R) (A + Y)
          rw [← ConnesKreimer.of'_add]]
    rw [insertion_mul_distrib A Y C]
    rw [Multiset.smul_sum, Multiset.map_map]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro C₁ _
    rw [(insertion : GrossmanLarson R α →ₗ[R] _).map_smul, LinearMap.smul_apply]
    show c • op (unop (insertion (of' (R := R) A) (of' C₁)) *
                  unop (insertion (of' (R := R) Y) (of' (C - C₁)))) =
        op ((c • unop (insertion (of' (R := R) A) (of' C₁))) *
            unop (insertion (of' (R := R) Y) (of' (C - C₁))))
    rw [smul_mul_assoc]; rfl

/-! ### §4b: Lemma 2.10's chain — `mul_assoc_basis` proved

The chain expands `(of'A * of'B) * of'C` step-by-step:

1. `(of'A * of'B) * of'C = productForest (of'A * of'B) C` (by `mul_of'`)
2. `of'A * of'B = productForest (of'A) B` (by `of'_mul_of'`); expand both
   levels of `productForest` to nested sums.
3. Apply `insertion_mul_distrib_gen` to split each `insertion(μ(...), of'C₁)`
   along a sub-partition `C₂ ⊆ C₁`.
4. Apply `insertion_assoc_shuffled` (basis form is enough — the LEFT
   factor at this point is `insertion (of' A) (of' B₁)`, which only
   becomes a sum after the assoc-rewrite of `insertion_assoc_shuffled_gen`,
   but here we're at fixed `B₁` so the basis form applies).
5. After all these rewrites, the LHS has a four-way C-partition:
   `C₂, C₁ - C₂, C - C₁` plus another implicit `B`-derived split.
6. Re-index the C-partition via `powerset_partition_swap`.
7. Similarly expand the RHS, observe that after `powerset_partition_swap`
   the two expressions are *syntactically* the same multiset sum. -/

/-! #### Helpers for the chain proof

Each helper expresses one stage of the LHS or RHS expansion. -/

/-- Basis-form rewrite: `(of' F₁) * (of' F₂)` as a sum of basis vectors `of' (X + (F₂ - B₁))`
    indexed by `B₁ ⊆ F₂` and `X ∈ NIM F₁ B₁`. Uses `mul_of'_sum_form` then
    `insertion_of'_of'` and `of'_add` to collapse to a forest sum. -/
theorem of'_mul_of'_nim_form (F₁ F₂ : Forest (Nonplanar α)) :
    (of' F₁ : GrossmanLarson R α) * of' F₂ =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       F₂.powerset.bind fun B₁ =>
        (Nonplanar.insertionMultiset F₁ B₁).map
          fun X => (of' (R := R) (X + (F₂ - B₁)) : GrossmanLarson R α)).sum := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  rw [mul_of'_sum_form, Multiset.sum_bind]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro B₁ _
  -- Inner: op (unop (insertion (of' F₁) (of' B₁)) * unop (of' (F₂ - B₁)))
  --      = ((NIM F₁ B₁).map (fun X => of' (X + (F₂ - B₁)))).sum
  rw [insertion_of'_of']
  unfold insertionBasis
  -- Goal: op (unop (((NIM F₁ B₁).map of').sum) * unop (of' (F₂ - B₁))) = ...
  show ((((Nonplanar.insertionMultiset F₁ B₁).map
            (fun F' => (ConnesKreimer.of' (R := R) F' :
              ConnesKreimer R (Nonplanar α)))).sum *
          (ConnesKreimer.of' (R := R) (F₂ - B₁) :
            ConnesKreimer R (Nonplanar α))) :
            ConnesKreimer R (Nonplanar α)) =
      ((Nonplanar.insertionMultiset F₁ B₁).map
        (fun X => (ConnesKreimer.of' (R := R) (X + (F₂ - B₁)) :
          ConnesKreimer R (Nonplanar α)))).sum
  rw [← Multiset.sum_map_mul_right]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro X _
  show (ConnesKreimer.of' (R := R) X : ConnesKreimer R (Nonplanar α)) *
        ConnesKreimer.of' (R := R) (F₂ - B₁) =
      ConnesKreimer.of' (R := R) (X + (F₂ - B₁))
  rw [ConnesKreimer.of'_add]

/-- Right-distributivity of `*` over `Multiset.sum`:
    `s.sum * of' G = (s.map (fun X => X * of' G)).sum`. Mirror of `of'_mul_sum_form`
    but for the right side. -/
private theorem sum_mul_of' (s : Multiset (GrossmanLarson R α))
    (G : Forest (Nonplanar α)) :
    s.sum * (of' G : GrossmanLarson R α) = (s.map (fun X => X * of' G)).sum := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.sum_zero, Multiset.map_zero, Multiset.sum_zero]
    show product (0 : GrossmanLarson R α) (of' G) = 0
    show ((product : GrossmanLarson R α →ₗ[R] _).flip (of' G)) 0 = 0
    exact LinearMap.map_zero _
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
    show product (a + s.sum) (of' G) = product a (of' G) + (s.map _).sum
    show ((product : GrossmanLarson R α →ₗ[R] _).flip (of' G)) (a + s.sum) = _
    rw [LinearMap.map_add]
    show product a (of' G) + product s.sum (of' G) = _
    show product a (of' G) + s.sum * (of' G : GrossmanLarson R α) = _
    rw [ih]

/-- Basis-form rewrite of LHS `((of' F₁) * of' F₂) * of' F₃` as a quadruple-bind
    sum. The outer two binds come from the Foissy-form expansion; the inner
    two come from `insertionMultiset_add_host` applied to `NIM (X + (F₂-B₁)) C₁`.
    Public: consumed by `GrossmanLarsonMonoid.lean` to identify the
    associativity LHS / RHS at the multiset-indexing level (R-generic). -/
theorem lhs_quadruple_form (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    ((of' F₁ : GrossmanLarson R α) * of' F₂) * of' F₃ =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       F₂.powerset.bind fun B₁ =>
        (Nonplanar.insertionMultiset F₁ B₁).bind fun X =>
          F₃.powerset.bind fun C₁ =>
            (C₁.powerset.bind fun D =>
              ((Nonplanar.insertionMultiset X D) ×ˢ
                (Nonplanar.insertionMultiset (F₂ - B₁) (C₁ - D))).map
                  fun p => (of' (R := R) (p.1 + p.2 + (F₃ - C₁)) :
                    GrossmanLarson R α))).sum := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- Step 1: rewrite (A * B) using of'_mul_of'_nim_form.
  rw [of'_mul_of'_nim_form]
  -- Step 2: push `(...) * of' F₃` through the outer sums.
  rw [sum_mul_of']
  -- Step 3: rearrange map-bind to bind-map.
  rw [show ((F₂.powerset.bind fun B₁ =>
              (Nonplanar.insertionMultiset F₁ B₁).map
                fun X => (of' (R := R) (X + (F₂ - B₁)) :
                  GrossmanLarson R α)).map fun X => X * of' F₃) =
          F₂.powerset.bind fun B₁ =>
            (Nonplanar.insertionMultiset F₁ B₁).map
              fun X => (of' (R := R) (X + (F₂ - B₁)) :
                GrossmanLarson R α) * of' F₃ from by
        rw [Multiset.map_bind]
        apply Multiset.bind_congr
        intros B₁ _
        rw [Multiset.map_map]
        rfl]
  rw [Multiset.sum_bind, Multiset.sum_bind]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro B₁ _
  -- For each B₁: ((NIM F₁ B₁).map (X => of'(X+(F₂-B₁)) * of' F₃)).sum
  --            = ((NIM F₁ B₁).bind (X => F₃.powerset.bind (C₁ => ...))).sum
  rw [Multiset.sum_bind]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro X _
  -- Goal: of' (X + (F₂-B₁)) * of' F₃ = (F₃.powerset.bind (C₁ => ...)).sum
  rw [of'_mul_of'_nim_form]
  -- Goal: (F₃.powerset.bind (fun C₁ => (NIM (X + (F₂-B₁)) C₁).map (Y => of' (Y + (F₃-C₁))))).sum
  --     = (F₃.powerset.bind (fun C₁ => (C₁.powerset.bind (D => ...)))).sum
  rw [Multiset.sum_bind, Multiset.sum_bind]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro C₁ _
  -- Now: NIM (X + (F₂-B₁)) C₁ = C₁.powerset.bind (D => (NIM X D) ×ˢ (NIM (F₂-B₁) (C₁-D)) |>.map (fun p => p.1 + p.2))
  -- via insertionMultiset_add_host.
  rw [Nonplanar.insertionMultiset_add_host]
  -- LHS_inner: ((C₁.powerset.bind (D => ...)).map (Y => of' (Y + (F₃-C₁)))).sum
  -- RHS_inner: ((C₁.powerset.bind (D => ((NIM X D) ×ˢ (NIM (F₂-B₁) (C₁-D))).map (fun p => of' (p.1 + p.2 + (F₃-C₁))))).sum
  rw [Multiset.map_bind, Multiset.sum_bind, Multiset.sum_bind]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro D _
  rw [Multiset.map_map]
  rfl

/-- Basis-form rewrite of RHS `(of' F₁) * ((of' F₂) * of' F₃)` as a quintuple-bind
    sum (after applying `Multiset.powerset_add` to `(Z + (F₃-C₁')).powerset`):

    Σ_{C₁' ⊆ F₃, Z ∈ NIM F₂ C₁', P_Z ⊆ Z, P_F ⊆ F₃-C₁', W ∈ NIM F₁ (P_Z+P_F)}
      of' (W + (Z - P_Z) + ((F₃-C₁') - P_F))

    Public: consumed by `GrossmanLarsonMonoid.lean`, paired with
    `lhs_quadruple_form` to derive R-generic associativity. -/
theorem rhs_quintuple_form (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    (of' F₁ : GrossmanLarson R α) * (of' F₂ * of' F₃) =
      (letI : DecidableEq (Nonplanar α) := Classical.decEq _
       F₃.powerset.bind fun C₁' =>
        (Nonplanar.insertionMultiset F₂ C₁').bind fun Z =>
          Z.powerset.bind fun P_Z =>
            (F₃ - C₁').powerset.bind fun P_F =>
              (Nonplanar.insertionMultiset F₁ (P_Z + P_F)).map
                fun W => (of' (R := R) (W + ((Z - P_Z) + ((F₃ - C₁') - P_F))) :
                  GrossmanLarson R α)).sum := by
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  -- Step 1: rewrite of' F₂ * of' F₃ via of'_mul_of'_nim_form.
  rw [of'_mul_of'_nim_form]
  -- Step 2: push of' F₁ * (.).sum through using of'_mul_sum_form.
  rw [of'_mul_sum_form]
  -- Step 3: collapse map-bind to bind-map.
  rw [show ((F₃.powerset.bind fun C₁' =>
              (Nonplanar.insertionMultiset F₂ C₁').map
                fun Z => (of' (R := R) (Z + (F₃ - C₁')) :
                  GrossmanLarson R α)).map fun X => of' F₁ * X) =
          F₃.powerset.bind fun C₁' =>
            (Nonplanar.insertionMultiset F₂ C₁').map fun Z =>
              (of' F₁ : GrossmanLarson R α) * of' (R := R) (Z + (F₃ - C₁')) from by
        rw [Multiset.map_bind]
        apply Multiset.bind_congr
        intros C₁' _
        rw [Multiset.map_map]
        rfl]
  rw [Multiset.sum_bind, Multiset.sum_bind]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro C₁' _
  -- Inner: ((NIM F₂ C₁').map (Z => of' F₁ * of' (Z + (F₃-C₁')))).sum
  --       = ((NIM F₂ C₁').bind (Z => Z.powerset.bind (P_Z => (F₃-C₁').powerset.bind (...)))).sum
  rw [Multiset.sum_bind]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro Z hZ
  -- Goal: of' F₁ * of' (Z + (F₃-C₁')) = ...
  rw [of'_mul_of'_nim_form]
  -- Goal LHS: ((Z + (F₃-C₁')).powerset.bind (P => (NIM F₁ P).map (W => of' (W + ((Z+(F₃-C₁')) - P))))).sum
  -- Apply Multiset.powerset_add Z (F₃-C₁') to split P.
  rw [Multiset.powerset_add]
  -- After: (Z.powerset.bind (P_Z => (F₃-C₁').powerset.map (P_F => P_Z + P_F))).bind (P => ...)
  rw [Multiset.bind_assoc]
  rw [Multiset.sum_bind, Multiset.sum_bind]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro P_Z hP_Z
  -- Now: ((F₃-C₁').powerset.map (P_F => P_Z + P_F)).bind (P => (NIM F₁ P).map (W => of' (W + ...)))
  rw [Multiset.bind_map]
  rw [Multiset.sum_bind, Multiset.sum_bind]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intro P_F hP_F
  -- Goal: (NIM F₁ (P_Z + P_F)).map (W => of' (W + ((Z + (F₃-C₁')) - (P_Z + P_F)))).sum
  --     = (NIM F₁ (P_Z + P_F)).map (W => of' (W + ((Z - P_Z) + ((F₃-C₁') - P_F)))).sum
  -- Use tsub_add_tsub_comm.
  have hP_Z_le : P_Z ≤ Z := Multiset.mem_powerset.mp hP_Z
  have hP_F_le : P_F ≤ F₃ - C₁' := Multiset.mem_powerset.mp hP_F
  have h_sub : (Z + (F₃ - C₁')) - (P_Z + P_F) = (Z - P_Z) + ((F₃ - C₁') - P_F) :=
    (tsub_add_tsub_comm hP_Z_le hP_F_le).symm
  rw [h_sub]

end GrossmanLarson

end RootedTree
