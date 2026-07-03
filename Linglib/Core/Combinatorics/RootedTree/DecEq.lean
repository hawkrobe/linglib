/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.Multiset.Rel
import Linglib.Core.Combinatorics.RootedTree.Nonplanar

/-!
# Decidable equality of nonplanar rose trees

Two rose trees represent the same nonplanar tree exactly when they are equal up to
reordering the children of every vertex (`RoseTree.PermEquiv`). This file shows that the
relation is decidable, and computably so: the decision procedure reduces in the kernel,
so concrete `Nonplanar` equalities close by `decide`.

## Main definitions

- `RoseTree.eqv`: Boolean comparison of two ordered trees up to child reordering — equal
  root values, and child lists matching as multisets under `eqv` (greedy matching).

## Main results

- `RoseTree.eqv_iff_permEquiv`: `eqv` decides `PermEquiv`.
- `RoseTree.instDecidableRelPermEquiv`: the resulting `DecidableRel PermEquiv`.
- `RootedTree.Nonplanar.instDecidableEq`: decidable equality on the quotient, via
  `Quotient.decidableEq`.

## Implementation notes

`eqvMulti` is the generic greedy matcher `List.isPermBy` at `eqv`
(`eqvMulti_eq_isPermBy`); it is redefined mutually with `eqv` only so the termination
checker sees the structural descent. Soundness and completeness of the matcher live
generically in `Core/Data/Multiset/Rel.lean`; what remains here is that `eqv` is an
equivalence. Symmetry and transitivity of `eqv` are mutually entangled at the children
level (completeness of the matcher needs both), so they are proven together by induction
on a size bound (`eqv_symm_trans`).

Strict, order-sensitive equality of the underlying ordered trees is already decidable
(`RoseTree.instDecidableEq`); this file only adds the decider for the quotient relation.

`[UPSTREAM]` candidate.
-/

namespace RoseTree

variable {α : Type*} [DecidableEq α]

/-! ### Deciding `PermEquiv`: equality up to child reordering -/

mutual
/-- `eqv t s` decides whether `t` and `s` are equal up to child reordering, i.e.
    `PermEquiv` (see `eqv_iff_permEquiv`): equal root values, and child lists matching as
    multisets under `eqv`. Computable from `DecidableEq α` alone. -/
def eqv : RoseTree α → RoseTree α → Bool
  | .node a cs, .node b ds => decide (a = b) && eqvMulti cs ds
/-- Greedy multiset matching of child lists: `List.isPermBy eqv`, inlined for
    termination. -/
private def eqvMulti : List (RoseTree α) → List (RoseTree α) → Bool
  | [], ds => ds.isEmpty
  | c :: cs, ds =>
    match ds.findIdx? (eqv c) with
    | some i => eqvMulti cs (ds.eraseIdx i)
    | none => false
end

/-! #### Correctness of the greedy matcher

`eqvMulti` is `List.isPermBy eqv`, so the generic soundness and completeness of the
greedy matcher (`Core/Data/Multiset/Rel.lean`) reduce both directions of
`eqv_iff_permEquiv` to the equivalence properties of `eqv`. -/

/-- `eqv` as a `Prop`-valued relation. -/
private abbrev Eqv (c d : RoseTree α) : Prop := eqv c d = true

/-- `eqvMulti` is the generic greedy matcher at `eqv`. -/
private theorem eqvMulti_eq_isPermBy :
    ∀ cs ds : List (RoseTree α), eqvMulti cs ds = List.isPermBy eqv cs ds
  | [], _ => rfl
  | c :: cs, ds => by
    rw [eqvMulti, List.isPermBy]
    cases ds.findIdx? (eqv c) with
    | none => rfl
    | some i => exact eqvMulti_eq_isPermBy cs (ds.eraseIdx i)

/-- Soundness of `eqvMulti` against `Multiset.Rel`, hypothesis-free. -/
private theorem rel_of_eqvMulti {cs ds : List (RoseTree α)} (h : eqvMulti cs ds = true) :
    Multiset.Rel Eqv (↑cs : Multiset (RoseTree α)) ↑ds :=
  List.rel_of_isPermBy (eqvMulti_eq_isPermBy cs ds ▸ h)

/-- Completeness of `eqvMulti` against `Multiset.Rel`, given symmetry and transitivity
    of `eqv` on a predicate `P` covering the children. -/
private theorem eqvMulti_of_rel {P : RoseTree α → Prop}
    (Ssymm : ∀ x y, P x → P y → eqv x y = true → eqv y x = true)
    (Strans : ∀ x y z, P x → P y → P z → eqv x y = true → eqv y z = true → eqv x z = true)
    {cs ds : List (RoseTree α)} (hPcs : ∀ x ∈ cs, P x) (hPds : ∀ x ∈ ds, P x)
    (h : Multiset.Rel Eqv (↑cs : Multiset (RoseTree α)) ↑ds) : eqvMulti cs ds = true := by
  rw [eqvMulti_eq_isPermBy]
  exact List.isPermBy_of_rel Ssymm Strans hPcs hPds h

/-- `eqv` on two nodes: equal root values and children matching under `eqvMulti`. -/
private theorem eqv_node_iff {a b : α} {cs ds : List (RoseTree α)} :
    eqv (.node a cs) (.node b ds) = true ↔ a = b ∧ eqvMulti cs ds = true := by
  rw [eqv, Bool.and_eq_true, decide_eq_true_eq]

/-- Symmetry and transitivity of `eqv`, proven together by induction on a size bound:
    completeness of the matcher at a node needs both symmetry and transitivity on the
    (strictly smaller) children, which the induction hypothesis supplies. -/
private theorem eqv_symm_trans :
    ∀ N, (∀ t s : RoseTree α, sizeOf t < N → sizeOf s < N →
            (eqv t s = true → eqv s t = true)) ∧
         (∀ t s u : RoseTree α, sizeOf t < N → sizeOf s < N → sizeOf u < N →
            (eqv t s = true → eqv s u = true → eqv t u = true)) := by
  intro N
  induction N with
  | zero =>
    exact ⟨fun t s hst _ => absurd hst (Nat.not_lt_zero _),
           fun t s u hst _ _ => absurd hst (Nat.not_lt_zero _)⟩
  | succ N ih =>
    refine ⟨?_, ?_⟩
    · rintro ⟨a, cs⟩ ⟨b, ds⟩ hst hss hts
      rw [eqv_node_iff] at hts
      obtain ⟨hab, hmulti⟩ := hts
      have hcsN : ∀ x ∈ cs, sizeOf x < N := fun x hx =>
        lt_of_lt_of_le (sizeOf_lt_of_mem hx) (Nat.lt_succ_iff.mp hst)
      have hdsN : ∀ x ∈ ds, sizeOf x < N := fun x hx =>
        lt_of_lt_of_le (sizeOf_lt_of_mem hx) (Nat.lt_succ_iff.mp hss)
      rw [eqv_node_iff]
      refine ⟨hab.symm, eqvMulti_of_rel ih.1 ih.2 hdsN hcsN (Multiset.rel_symm_on ?_
        (rel_of_eqvMulti hmulti))⟩
      exact fun x hx y hy => ih.1 x y (hcsN x (Multiset.mem_coe.mp hx))
        (hdsN y (Multiset.mem_coe.mp hy))
    · rintro ⟨a, cs⟩ ⟨b, ds⟩ ⟨c, es⟩ hst hss hsu hts hsu'
      rw [eqv_node_iff] at hts
      obtain ⟨hab, hm1⟩ := hts
      rw [eqv_node_iff] at hsu'
      obtain ⟨hbc, hm2⟩ := hsu'
      have hcsN : ∀ x ∈ cs, sizeOf x < N := fun x hx =>
        lt_of_lt_of_le (sizeOf_lt_of_mem hx) (Nat.lt_succ_iff.mp hst)
      have hdsN : ∀ x ∈ ds, sizeOf x < N := fun x hx =>
        lt_of_lt_of_le (sizeOf_lt_of_mem hx) (Nat.lt_succ_iff.mp hss)
      have hesN : ∀ x ∈ es, sizeOf x < N := fun x hx =>
        lt_of_lt_of_le (sizeOf_lt_of_mem hx) (Nat.lt_succ_iff.mp hsu)
      rw [eqv_node_iff]
      refine ⟨hab.trans hbc, eqvMulti_of_rel ih.1 ih.2 hcsN hesN (Multiset.rel_trans_on ?_
        (rel_of_eqvMulti hm1) (rel_of_eqvMulti hm2))⟩
      exact fun x hx y hy z hz => ih.2 x y z (hcsN x (Multiset.mem_coe.mp hx))
        (hdsN y (Multiset.mem_coe.mp hy)) (hesN z (Multiset.mem_coe.mp hz))

/-- Symmetry of `eqv`. -/
private theorem eqv_symm {t s : RoseTree α} (h : eqv t s = true) : eqv s t = true :=
  (eqv_symm_trans (max (sizeOf t) (sizeOf s) + 1)).1 t s
    (Nat.lt_succ_of_le (le_max_left _ _)) (Nat.lt_succ_of_le (le_max_right _ _)) h

/-- Transitivity of `eqv`. -/
private theorem eqv_trans {t s u : RoseTree α} (h1 : eqv t s = true) (h2 : eqv s u = true) :
    eqv t u = true :=
  (eqv_symm_trans (max (sizeOf t) (max (sizeOf s) (sizeOf u)) + 1)).2 t s u
    (Nat.lt_succ_of_le (le_max_left _ _))
    (Nat.lt_succ_of_le (le_trans (le_max_left _ _) (le_max_right _ _)))
    (Nat.lt_succ_of_le (le_trans (le_max_right _ _) (le_max_right _ _))) h1 h2

/-- `eqv` is reflexive. -/
private theorem eqv_refl : ∀ (t : RoseTree α), eqv t t = true
  | .node a cs => by
    rw [eqv_node_iff]
    refine ⟨rfl, ?_⟩
    rw [eqvMulti_eq_isPermBy]
    exact List.isPermBy_refl cs fun c hc => eqv_refl c
termination_by t => sizeOf t
decreasing_by exact sizeOf_lt_of_mem hc

/-- `eqvMulti`, unconditionally: symmetry and transitivity of `eqv` are now globally
    available. -/
private theorem eqvMulti_of_rel' {cs ds : List (RoseTree α)}
    (h : Multiset.Rel Eqv (↑cs : Multiset (RoseTree α)) ↑ds) : eqvMulti cs ds = true :=
  eqvMulti_of_rel (P := fun _ => True) (fun _ _ _ _ hxy => eqv_symm hxy)
    (fun _ _ _ _ _ _ hxy hyz => eqv_trans hxy hyz)
    (fun _ _ => trivial) (fun _ _ => trivial) h

/-- `eqv` respects a single `PermStep`. -/
private theorem eqv_step {t s : RoseTree α} (h : PermStep t s) : eqv t s = true := by
  induction h with
  | @swapAtRoot a l r pre post =>
    rw [eqv_node_iff]
    refine ⟨rfl, eqvMulti_of_rel' ?_⟩
    have hcoe : ((pre ++ l :: r :: post : List (RoseTree α)) : Multiset (RoseTree α))
        = ↑(pre ++ r :: l :: post) :=
      Multiset.coe_eq_coe.mpr ((List.Perm.swap r l post).append_left pre)
    rw [hcoe]
    exact Multiset.rel_refl_of_refl_on fun x _ => eqv_refl x
  | @recurse a pre old new post _ ih =>
    rw [eqv_node_iff]
    refine ⟨rfl, eqvMulti_of_rel' (Multiset.rel_coe_iff_exists.mpr
      ⟨pre ++ new :: post,
        List.rel_append (List.forall₂_same.mpr fun x _ => eqv_refl x)
          (List.Forall₂.cons ih (List.forall₂_same.mpr fun x _ => eqv_refl x)),
        List.Perm.refl _⟩)⟩

/-- `PermEquiv → eqv`, by `EqvGen` induction. -/
private theorem permEquiv_to_eqv {t s : RoseTree α} (h : PermEquiv t s) : eqv t s = true := by
  induction h with
  | rel _ _ hstep => exact eqv_step hstep
  | refl t => exact eqv_refl t
  | symm _ _ _ ih => exact eqv_symm ih
  | trans _ _ _ _ _ ih1 ih2 => exact eqv_trans ih1 ih2

mutual
/-- `eqv → PermEquiv`, by structural induction. -/
private theorem eqv_to_permEquiv : ∀ (t s : RoseTree α), eqv t s = true → PermEquiv t s
  | .node a cs, .node b ds, h => by
    rw [eqv_node_iff] at h
    obtain ⟨hab, hmulti⟩ := h
    subst hab
    obtain ⟨ds', hf, hperm⟩ := Multiset.rel_coe_iff_exists.mp (rel_of_eqvMulti hmulti)
    exact (permEquiv_node_componentwise
      (eqv_forall₂_to_permEquiv cs ds' hf)).trans (permEquiv_root_perm hperm)
private theorem eqv_forall₂_to_permEquiv :
    ∀ (cs ds' : List (RoseTree α)),
      List.Forall₂ (fun c d => eqv c d = true) cs ds' → List.Forall₂ PermEquiv cs ds'
  | [], [], _ => List.Forall₂.nil
  | c :: cs, d :: ds', h => by
    obtain ⟨hcd, hrest⟩ := List.forall₂_cons.mp h
    exact List.Forall₂.cons (eqv_to_permEquiv c d hcd)
      (eqv_forall₂_to_permEquiv cs ds' hrest)
end

/-- `eqv` decides `PermEquiv`: two ordered trees are `eqv`-related iff they are equal up
    to reordering the children of every vertex.

    `(→)` is structural induction (`eqv_to_permEquiv`), reading the greedy match back
    through `permEquiv_node_componentwise` and `permEquiv_root_perm`; `(←)` is `EqvGen`
    induction (`permEquiv_to_eqv`), using that `eqv` is an equivalence and respects each
    `PermStep`. -/
theorem eqv_iff_permEquiv {t s : RoseTree α} : eqv t s = true ↔ PermEquiv t s :=
  ⟨eqv_to_permEquiv t s, permEquiv_to_eqv⟩

/-- `PermEquiv` is decidable, computably so: decided by `eqv`, which reduces in the
    kernel. -/
instance instDecidableRelPermEquiv : DecidableRel (PermEquiv (α := α)) :=
  fun _ _ => decidable_of_iff _ eqv_iff_permEquiv

instance instDecidableRelEquiv : DecidableRel ((· ≈ ·) : RoseTree α → RoseTree α → Prop) :=
  instDecidableRelPermEquiv

end RoseTree

namespace RootedTree.Nonplanar

variable {α : Type*} [DecidableEq α]

/-- Equality of nonplanar trees — equality up to child reordering — is decidable and
    computable: `Quotient.decidableEq` over `RoseTree.eqv` on representatives, which
    reduces in the kernel, so concrete `Nonplanar` equalities close by `decide`. -/
instance instDecidableEq : DecidableEq (Nonplanar α) :=
  inferInstanceAs (DecidableEq (Quotient (RoseTree.instSetoid (α := α))))

end RootedTree.Nonplanar
