import Linglib.Core.Algebra.ConnesKreimer.Bialgebra

/-!
# Verification: substrate refactor restores coassoc properties

After the `IsNotTrace` substrate refactor, we verify that the cardinalities and
structural properties needed for `lhs_eq_sum_DoubleCut (.node l r)` to hold are
now satisfied.

## Pre-refactor problem (now fixed)

Before the refactor, `CutShape` allowed `bothCut`, `onlyLeftCut`, `onlyRightCut`
on any `.node l r` regardless of whether `l` or `r` was a `.trace` marker.
Iterating Δ on the remainder of an outer cut therefore extracted `.trace`
markers and produced REMAINDERS-OF-REMAINDERS with `.trace (.trace _)` nesting.
This created RHS triple-tensors that LHS could not produce, breaking coassoc.

## Post-refactor invariant

The extracting cuts now require `IsNotTrace` hypotheses. So for any tree T'
whose children are all `.trace` markers, the only valid `CutShape` is
`bothRecurse atTrace atTrace` (no extraction). Hence `comulTree T'` is
**primitive**: `forestToHc{T'} ⊗ 1 + 1 ⊗ forestToHc{T'}`.

This restores the cardinality match (LHS = RHS for T = .node leaf leaf), as
verified below.

## Checks

For T = .node (.leaf a) (.leaf b):
- Pre-refactor `Fintype.card (DoubleCut T) = 21` (had 7 extra triples involving
  doubly-traced trees that LHS could not match).
- Post-refactor, the doubly-traced trees no longer appear because cutting at
  trace children is forbidden. `DoubleCut T` cardinality drops to 14 — matching
  the LHS data count.

(See git history at the time of substrate refactor for the pre/post comparison.)
-/

namespace ConnesKreimer.CoassocCheck

abbrev Atom := ULift (Fin 2)

abbrev a : Atom := ⟨0⟩
abbrev b : Atom := ⟨1⟩

abbrev T : TraceTree Atom Unit := .node (.leaf a) (.leaf b)
abbrev Tprime : TraceTree Atom Unit :=
  .node (.trace ()) (.trace ())

/-! ## Post-refactor cardinality

After the `IsNotTrace` restriction, `CutShape T'` for `T' = .node (.trace _)
(.trace _)` has only ONE constructor (`bothRecurse atTrace atTrace`), so
`AugCutShape T'` has 2 elements. -/

example : Fintype.card (CutShape Tprime) = 1 := by decide
example : Fintype.card (AugCutShape Tprime) = 2 := by decide

-- The single CutShape on Tprime is the empty cut. The extracting ctors
-- (bothCut/onlyLeftCut/onlyRightCut) are absurd on Tprime since both children
-- are .trace markers (`IsNotTrace` would be False).
example (C : CutShape Tprime) : C = CutShape.empty Tprime := by
  cases C with
  | bothCut hl _ => exact hl.elim
  | onlyLeftCut hl _ => exact hl.elim
  | onlyRightCut hr _ => exact hr.elim
  | bothRecurse cl cr => cases cl; cases cr; rfl

-- Hence comulTree Tprime is PRIMITIVE: forestToHc{Tprime} ⊗ 1 + 1 ⊗ forestToHc{Tprime}.
-- (Verified algebraically: the only summand in the cut sum has cutForest = 0,
-- remainder = Tprime, giving 1 ⊗ forestToHc{Tprime}.)

/-! ## DoubleCut cardinality drops to match LHS

Pre-refactor: `Fintype.card (DoubleCut T) = 21` (LHS had 14, mismatch).
Post-refactor: with the restriction, the inner AugCutShapes on the various
remainders are smaller, and the total DoubleCut count matches the LHS-side
sections count.

For T = .node (.leaf a) (.leaf b):
  remainder bothCut         = .node (.trace .leaf a) (.trace .leaf b),
    AugCutShape size = 2 (only bothRecurse atTrace atTrace + extractWhole)
  remainder onlyLeftCut     = .node (.trace .leaf a) (.leaf b),
    AugCutShape size = 3 (onlyRightCut atTrace atLeaf, bothRecurse atTrace atLeaf,
    extractWhole)
  remainder onlyRightCut    = .node (.leaf a) (.trace .leaf b),
    AugCutShape size = 3 (symmetric)
  remainder bothRecurse atLeaf atLeaf = T,  AugCutShape size = 5

DoubleCut T total: 1 (extractWhole) + 2 + 3 + 3 + 5 = 14. -/

example : Fintype.card (DoubleCut T) = 14 := by decide

/-! ## LHS side count: 14 (matches!)

The LHS-natural data is `Σ ac : AugCutShape T, Sections((cutForest_aug ac).map comulTreeMS)`.
For T = .node (.leaf a) (.leaf b):

  ac = extractWhole_T:  cutForest_aug = {T},                      5 sections
  ac = real bothCut:    cutForest_aug = {leaf a, leaf b},  2*2 =  4 sections
  ac = real onlyLeftCut atLeaf:  cutForest_aug = {leaf a},        2 sections
  ac = real onlyRightCut atLeaf: cutForest_aug = {leaf b},        2 sections
  ac = real bothRecurse atLeaf atLeaf: cutForest_aug = 0,         1 section

  LHS total: 5 + 4 + 2 + 2 + 1 = 14.

Matches DoubleCut T cardinality. So `lhs_eq_sum_DoubleCut (.node l r)` is now
provable in principle (the bijection exists). -/

end ConnesKreimer.CoassocCheck
