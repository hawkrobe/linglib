/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.List.Chain

/-!
# Subregular Languages: Boundary Augmentation

Boundary augmentation of strings and a boundary-vacuity predicate relating the
chain-membership of a padded string to that of its unpadded core. The strictly-local,
locally-testable, and tier-relativized classes are built on this infrastructure
[lambert-2022] [heinz-rogers-2010] [rogers-pullum-2011]. The contiguous `k`-factors
the hierarchy quantifies over are a generic list combinator and live in
`Core/Data/List/Factors.lean` (`List.kFactors`).

## Main definitions

* `Subregular.Augmented α` — the boundary-augmented alphabet `List (Option α)`,
  with `none` the boundary marker.
* `Subregular.boundary k w` — `w` injected into `Augmented α` and padded with
  `k - 1` boundary markers on each side.
* `Subregular.IsBoundaryVacuous R` — `R` holds whenever either argument is the
  boundary marker `none`.

## Main results

* `Subregular.IsBoundaryVacuous.isChain_boundary_two_iff` — boundary padding does
  not change `IsChain`-membership for a boundary-vacuous relation.

## Implementation notes

The standard subregular convention extends the alphabet with two edge markers
`⋊`, `⋉` and studies the `k`-factors of `⋊ᵏ⁻¹ · w · ⋉ᵏ⁻¹`. We instead use the
one-fresh-symbol extension `Option α` (`none` = boundary, `some a` = original
symbol): a single marker suffices because boundary symbols only ever occur at
fixed positions, so the two edges are never confused.
-/

namespace Subregular

variable {α : Type*}

/-! ### Boundary augmentation -/

/-- The boundary-augmented alphabet: original symbols (`some a`) plus the
boundary marker `none`. -/
abbrev Augmented (α : Type*) := List (Option α)

section Boundary

variable (k : ℕ) (w : List α)

/-- `w` padded with `k - 1` boundary markers (`none`) on each side. -/
def boundary : Augmented α :=
  List.replicate (k - 1) none ++ w.map some ++ List.replicate (k - 1) none

@[simp] lemma boundary_one : boundary 1 w = w.map some := by
  simp [boundary]

lemma length_boundary : (boundary k w).length = w.length + 2 * (k - 1) := by
  simp [boundary]; omega

end Boundary

/-! ### Boundary-vacuous relations -/

/-- A relation on `Option α` is **boundary-vacuous** when `none` satisfies it on
either side (`R none u`, `R u none`) — so only `(some a, some b)` pairs can
witness a violation. Subregular edge constraints (OCP, no-clash, no-lapse) all
share this shape. -/
structure IsBoundaryVacuous (R : Option α → Option α → Prop) : Prop where
  none_left : ∀ u, R none u
  none_right : ∀ u, R u none

namespace IsBoundaryVacuous

variable {R : Option α → Option α → Prop}

/-- 2-boundary padding preserves `IsChain` for a boundary-vacuous relation. -/
lemma isChain_boundary_two_iff (hR : IsBoundaryVacuous R) (ys : List α) :
    (boundary 2 ys).IsChain R ↔ (ys.map some).IsChain R := by
  show (none :: (ys.map some ++ [none])).IsChain R ↔ _
  rw [List.isChain_cons_iff_of_forall_rel hR.none_left,
      List.isChain_append_singleton_iff_of_forall_rel hR.none_right]

end IsBoundaryVacuous

end Subregular
