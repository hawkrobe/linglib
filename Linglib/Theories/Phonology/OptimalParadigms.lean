import Linglib.Theories.Phonology.Correspondence

/-!
# Optimal Paradigms
@cite{mccarthy-2005}

Optimal Paradigms (OP) extends Optimality Theory by evaluating **whole
inflectional paradigms** as candidates rather than individual forms.
Faithfulness constraints can require uniformity between all members of
a paradigm, enabling category-neutral derivation of noun-verb phonological
asymmetries from differences in paradigm structure alone.

## Architecture

OP does not require new evaluation machinery. The existing `mkTableau`
is polymorphic in the candidate type `C` — setting `C := List Form` gives
paradigm-level evaluation for free. This module provides two **constraint
combinators** that lift form-level ingredients to paradigm-level constraints:

1. `liftPerMember`: lifts a per-form violation count to a per-paradigm sum
2. `liftPairwise`: lifts a per-pair comparison to a paradigm-level violation
   sum (the mechanism behind OP-MAX-V and other OP constraints)

These are the core of OP. The Majority Rules prediction — that a paradigm
member equivocal between two forms will align with the majority group —
falls out of `liftPairwise` applied to paradigms where one group of
members outnumbers the other.

## Connection to Correspondence Theory

OP constraints are output-to-output (OO) faithfulness constraints
(@cite{mccarthy-prince-1995}) applied *symmetrically* across all paradigm
members. `mkOPMaxV` is the pairwise lift of OO-MAX: the `vowelMismatch`
function passed to it is structurally analogous to `Corr.maxViol` in
`Correspondence.lean`, restricted to vocalic positions.

## Empirical status

@cite{marco-rasin-2026} show that OP cannot simultaneously predict the
distribution of schwa in verbs, nouns, and adjectives in Judeo-Tripolitanian
Arabic: adjectives pattern phonologically with verbs but paradigmatically
with nouns — contradicting OP's prediction that phonological behavior
tracks paradigm structure. See
`Phenomena.PhonologicalAlternation.Studies.MarcoRasin2026` for the
formalization.
-/

namespace Phonology.OptimalParadigms

open Core.OT (NamedConstraint ConstraintFamily)
open Phonology.Correspondence (Corr CorrDomain)

-- ============================================================================
-- § 1: Paradigm-Level Constraint Combinators
-- ============================================================================

/-- Lift a per-form violation count to a per-paradigm constraint by summing
    violations across all members. Used for markedness constraints that
    evaluate each paradigm member independently.

    Example: `*CCC` penalizes tri-consonantal clusters in each member;
    the paradigm-level violation is the total across all members. -/
def liftPerMember {Form : Type} (name : String) (family : ConstraintFamily)
    (viol : Form → Nat) : NamedConstraint (List Form) :=
  { name, family, eval := fun paradigm => (paradigm.map viol).sum }

/-- Lift a per-pair comparison to a paradigm-level constraint by summing
    over all ordered pairs. This is the mechanism behind OP constraints:
    every pair of paradigm members is compared, and violations are summed.

    Using ordered pairs (via `List.product`) matches @cite{mccarthy-2005}'s
    violation counting: for each pair ⟨m₁, m₂⟩ where m₁ has a vowel in
    a position where m₂ does not, OP-MAX-V is violated once. Symmetry
    ensures each unordered pair contributes violations in both directions. -/
def liftPairwise {Form : Type} (name : String) (family : ConstraintFamily)
    (compare : Form → Form → Nat) : NamedConstraint (List Form) :=
  { name, family
    eval := fun paradigm =>
      ((paradigm.product paradigm).map (fun (a, b) => compare a b)).sum }

-- ============================================================================
-- § 2: OP-MAX-V (the central OP constraint)
-- ============================================================================

/-- Build an OP-MAX-V constraint: penalizes paradigm non-uniformity with
    respect to vowel positions.

    `vowelMismatch a b` counts positions where form `a` has a vowel and
    form `b` does not. The full constraint sums this over all ordered pairs
    in the paradigm.

    Conceptually, this is the pairwise lift of OO-MAX restricted to
    vocalic positions. When the forms are modeled as `Corr` (output-to-output
    correspondence), `vowelMismatch` reduces to `Corr.maxViol` on the
    vowel tier. -/
def mkOPMaxV {Form : Type} (vowelMismatch : Form → Form → Nat) :
    NamedConstraint (List Form) :=
  liftPairwise "OP-MAX-V" .faithfulness vowelMismatch

-- ============================================================================
-- § 3: Majority Rules
-- ============================================================================

/-- The Majority Rules condition (@cite{mccarthy-2005}): when a paradigm
    member is equivocal between two forms (both satisfy higher-ranked
    markedness constraints equally), OP predicts it will align with the
    group containing more members.

    `majority groupA groupB` holds when group A outnumbers group B.
    Under OP, the equivocal member will surface with group A's form,
    because aligning with the larger group minimizes total pairwise
    OP-MAX-V violations. -/
def majorityRules (groupA groupB : Nat) : Bool :=
  groupA > groupB

/-- When one group is larger, the equivocal member's OP-MAX-V violations
    are minimized by aligning with the majority.

    If `a` members have form X and `b` members have form Y, and one
    equivocal member chooses form X, the OP-MAX-V violations from
    cross-group pairs are `(a + 1) * b * 2`. Choosing Y instead gives
    `a * (b + 1) * 2`. The former is smaller iff `a > b` (since
    `(a+1)*b = ab + b < ab + a = a*(b+1)` when `a > b`). -/
theorem majority_minimizes_violations (a b : Nat) (h : a > b) :
    (a + 1) * b < a * (b + 1) := by
  -- (a+1)*b = a*b + b; a*(b+1) = a*b + a; since a > b, a*b+b < a*b+a
  rw [Nat.add_mul, Nat.mul_add]; omega

end Phonology.OptimalParadigms
