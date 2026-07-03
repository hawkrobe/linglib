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

`eqv.go` is the generic greedy matcher `List.isPermBy` at `eqv` (`go_eq_isPermBy`); it
is re-inlined in the definition only so the recursion compiles structurally — kernel
reduction (hence `decide`) needs `brecOn`, not `WellFounded.fix`, so the recursion cannot
route through the opaque `isPermBy`. Soundness and completeness of the matcher live
generically in `Core/Data/Multiset/Rel.lean`, and correctness here is a single
size-bounded induction (`eqv_iff_mk_eq`): the inductive hypothesis converts `eqv` on
children to equality of `mk`-images, so the matcher's symmetry/transitivity hypotheses
are discharged by `Eq.symm`/`Eq.trans`, and `Nonplanar.mk_node_eq_mk_node_iff` (from
`congrArg` on the lifted `value`/`children` destructors) inverts the node.

Strict, order-sensitive equality of the underlying ordered trees is already decidable
(`RoseTree.instDecidableEq`); this file only adds the decider for the quotient relation.

`[UPSTREAM]` candidate.
-/

namespace RoseTree

open RootedTree

variable {α : Type*} [DecidableEq α] {cs ds : List (RoseTree α)} {t s : RoseTree α}

/-! ### Deciding `PermEquiv`: equality up to child reordering -/

/-- `eqv t s` decides whether `t` and `s` are equal up to child reordering
    (`eqv_iff_permEquiv`). -/
def eqv : RoseTree α → RoseTree α → Bool
  | .node a cs, .node b ds => decide (a = b) && go cs ds
where
  /-- Greedy multiset matching of child lists: `List.isPermBy eqv`. -/
  go : List (RoseTree α) → List (RoseTree α) → Bool
    | [], ds => ds.isEmpty
    | c :: cs, ds =>
      match ds.findIdx? (eqv c) with
      | some i => go cs (ds.eraseIdx i)
      | none => false

/-! #### Correctness of the greedy matcher

`eqv.go` is `List.isPermBy eqv`, so the generic soundness and completeness of the
greedy matcher (`Core/Data/Multiset/Rel.lean`) reduce `eqv_iff_permEquiv` to one
size-bounded induction against `mk`-equality. -/

/-- `eqv` as a `Prop`-valued relation. -/
private abbrev Eqv (c d : RoseTree α) : Prop := eqv c d = true

/-- `eqv.go` is the generic greedy matcher at `eqv`. -/
private theorem go_eq_isPermBy :
    ∀ cs ds : List (RoseTree α), eqv.go cs ds = List.isPermBy eqv cs ds
  | [], _ => rfl
  | c :: cs, ds => by
    rw [eqv.go, List.isPermBy]
    cases ds.findIdx? (eqv c) with
    | none => rfl
    | some i => exact go_eq_isPermBy cs (ds.eraseIdx i)

/-- Soundness of `eqv.go` against `Multiset.Rel`, hypothesis-free. -/
private theorem rel_of_go (h : eqv.go cs ds = true) :
    Multiset.Rel Eqv (↑cs : Multiset (RoseTree α)) ↑ds :=
  List.rel_of_isPermBy (go_eq_isPermBy cs ds ▸ h)

/-- Completeness of `eqv.go` against `Multiset.Rel`, given symmetry and transitivity
    of `eqv` on a predicate `P` covering the children. -/
private theorem go_of_rel {P : RoseTree α → Prop}
    (Ssymm : ∀ x y, P x → P y → eqv x y = true → eqv y x = true)
    (Strans : ∀ x y z, P x → P y → P z → eqv x y = true → eqv y z = true → eqv x z = true)
    (hPcs : ∀ x ∈ (↑cs : Multiset (RoseTree α)), P x)
    (hPds : ∀ x ∈ (↑ds : Multiset (RoseTree α)), P x)
    (h : Multiset.Rel Eqv (↑cs : Multiset (RoseTree α)) ↑ds) : eqv.go cs ds = true := by
  rw [go_eq_isPermBy]
  exact List.isPermBy_of_rel Ssymm Strans (fun x hx => hPcs x (Multiset.mem_coe.mpr hx))
    (fun x hx => hPds x (Multiset.mem_coe.mpr hx)) h

/-- `eqv` on two nodes: equal root values and children matching under `eqv.go`. -/
private theorem eqv_node_iff {a b : α} :
    eqv (.node a cs) (.node b ds) = true ↔ a = b ∧ eqv.go cs ds = true := by
  rw [eqv, Bool.and_eq_true, decide_eq_true_eq]

omit [DecidableEq α] in
/-- Children of a node below `N + 1` are below `N`. -/
private theorem sizeOf_children_lt {a : α} {N : ℕ} (h : sizeOf (RoseTree.node a cs) < N + 1) :
    ∀ x ∈ (↑cs : Multiset (RoseTree α)), sizeOf x < N := fun _ hx =>
  lt_of_lt_of_le (sizeOf_lt_of_mem (Multiset.mem_coe.mp hx)) (Nat.lt_succ_iff.mp h)

/-- `eqv` decides equality in the quotient, by induction on a size bound: on the
    children, the inductive hypothesis converts `eqv` to equality of `mk`-images, whose
    symmetry and transitivity discharge the completeness hypotheses of the matcher,
    while `Nonplanar.mk_node_eq_mk_node_iff` inverts `mk`-equality at the node. -/
private theorem eqv_iff_mk_eq :
    ∀ N, ∀ t s : RoseTree α, sizeOf t < N → sizeOf s < N →
      (eqv t s = true ↔ Nonplanar.mk t = Nonplanar.mk s) := by
  intro N
  induction N with
  | zero => exact fun _ _ hst _ => absurd hst (Nat.not_lt_zero _)
  | succ N ih =>
    rintro ⟨a, cs⟩ ⟨b, ds⟩ hst hss
    have hcsN := sizeOf_children_lt hst
    have hdsN := sizeOf_children_lt hss
    rw [eqv_node_iff, Nonplanar.mk_node_eq_mk_node_iff,
        ← Multiset.map_coe, ← Multiset.map_coe, ← Multiset.rel_eq, Multiset.rel_map]
    refine and_congr_right fun _ => ⟨fun h => (rel_of_go h).mono
      (fun x hx y hy hxy => (ih x y (hcsN x hx) (hdsN y hy)).mp hxy), fun h => ?_⟩
    exact go_of_rel (P := (sizeOf · < N))
      (fun x y hx hy hxy => (ih y x hy hx).mpr ((ih x y hx hy).mp hxy).symm)
      (fun x y z hx hy hz h1 h2 =>
        (ih x z hx hz).mpr (((ih x y hx hy).mp h1).trans ((ih y z hy hz).mp h2)))
      hcsN hdsN (h.mono fun x hx y hy hxy => (ih x y (hcsN x hx) (hdsN y hy)).mpr hxy)

/-- `eqv` decides `PermEquiv`: two ordered trees are `eqv`-related iff they are equal up
    to reordering the children of every vertex. Composite of `eqv_iff_mk_eq` (at a
    sum-of-sizes bound) with `Nonplanar.mk_eq_mk_iff`. -/
theorem eqv_iff_permEquiv : eqv t s = true ↔ PermEquiv t s :=
  ((eqv_iff_mk_eq (sizeOf t + sizeOf s + 1) t s (by omega) (by omega)).trans
    Nonplanar.mk_eq_mk_iff)

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
