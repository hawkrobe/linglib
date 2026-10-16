/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.Perm
public import Linglib.Core.Data.UnorderedTree.Basic

/-!
# Decidable equality of nonplanar rose trees

Two rose trees represent the same nonplanar tree exactly when they are equal up to
reordering the children of every vertex (`RoseTree.Perm`). This file shows that the
relation is decidable, and computably so: the decision procedure reduces in the kernel,
so concrete `UnorderedTree` equalities close by `decide`.

## Main definitions

- `RoseTree.eqv`: Boolean comparison of two ordered trees up to child reordering — equal
  root values, and child lists matching as multisets under `eqv` (greedy matching).

## Main results

- `RoseTree.eqv_iff_perm`: `eqv` decides `Perm`.
- `RoseTree.instDecidableRelPerm`: the resulting `DecidableRel Perm`.
- `UnorderedTree.instDecidableEq`: decidable equality on the quotient, via
  `Quotient.decidableEq`.

## Implementation notes

`eqv` must recurse structurally for kernel reduction (`decide` needs `brecOn`, not
`WellFounded.fix`), and passing `eqv` to `List.isPermBy` is not structural, so the greedy matcher
is inlined as `eqv.go`. `go_eq_isPermBy` reconnects the two, and `List.isPermBy_iff_perm_map`
then reduces `eqv_iff_perm` to one structural induction: by the inductive hypothesis, `eqv`
computes equality of `mk`-images on the children.

`[UPSTREAM]` candidate.
-/

@[expose] public section

namespace RoseTree

open UnorderedTree

variable {α : Type*} [DecidableEq α] {t s : RoseTree α}

/-! ### Deciding `Perm`: equality up to child reordering -/

/-- `eqv t s` decides whether `t` and `s` are equal up to child reordering
(`eqv_iff_perm`). -/
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

private theorem go_eq_isPermBy :
    ∀ cs ds : List (RoseTree α), eqv.go cs ds = List.isPermBy eqv cs ds
  | [], _ => rfl
  | c :: cs, ds => by
    rw [eqv.go, List.isPermBy]
    cases ds.findIdx? (eqv c) with
    | none => rfl
    | some i => exact go_eq_isPermBy cs (ds.eraseIdx i)

/-- Two ordered trees are `eqv`-related iff they are equal up to reordering the children of
every vertex. -/
theorem eqv_iff_perm : eqv t s ↔ Perm t s := by
  rw [← mk_eq_mk_iff]
  induction t generalizing s with
  | node a cs ih =>
    obtain ⟨b, ds⟩ := s
    rw [eqv, Bool.and_eq_true, decide_eq_true_eq, go_eq_isPermBy, mk_node_eq_mk_node_iff,
      Multiset.coe_eq_coe, List.isPermBy_iff_perm_map fun x hx _ _ ↦ ih x hx]

/-- `Perm` is decided by `eqv`, which reduces in the kernel. -/
instance instDecidableRelPerm : DecidableRel (Perm (α := α)) :=
  fun _ _ ↦ decidable_of_iff _ eqv_iff_perm

instance : DecidableRel ((· ≈ ·) : RoseTree α → RoseTree α → Prop) :=
  instDecidableRelPerm

end RoseTree

namespace UnorderedTree

variable {α : Type*} [DecidableEq α]

/-- Equality of nonplanar trees is decided by `RoseTree.eqv` on representatives
(`Quotient.decidableEq`), so concrete `UnorderedTree` equalities close by `decide`. -/
instance instDecidableEq : DecidableEq (UnorderedTree α) :=
  inferInstanceAs (DecidableEq (Quotient (RoseTree.isSetoid (α := α))))

end UnorderedTree
