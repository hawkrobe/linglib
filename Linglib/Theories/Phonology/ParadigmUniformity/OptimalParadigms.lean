import Linglib.Theories.Phonology.ParadigmUniformity.Defs
import Linglib.Theories.Phonology.OptimalityTheory.Correspondence

/-!
# Optimal Paradigms — McCarthy 2005
@cite{mccarthy-2005}

The paper-specific OP anchoring of the generic `liftPairwise`
combinator from `ParadigmUniformity/Defs.lean`. OP evaluates
**inflectional paradigms** as candidates rather than individual forms;
faithfulness applies symmetrically across every member-pair, with no
distinguished base. The Majority Rules prediction — that a paradigm
member equivocal between two forms aligns with the majority group —
falls out of `liftPairwise` arithmetic.

## Architecture

OP does not require new evaluation machinery. The existing `mkTableau`
is polymorphic in the candidate type `C` — setting `C := List Form`
gives paradigm-level evaluation for free. The two combinators
`liftPerMember` / `liftPairwise` (factored into
`ParadigmUniformity.Defs`) are reused across PU theories that differ
only in their anchoring choice.

## Connection to Correspondence Theory

OP constraints are output-to-output (OO) faithfulness constraints
(@cite{mccarthy-prince-1995}) applied *symmetrically* across all
paradigm members. `mkOPMaxV` is the symmetric pairwise lift of
OO-MAX restricted to vowel positions; the `vowelMismatch` function
passed to it is structurally analogous to `Corr.maxViol` in
`Correspondence.lean`.

## Empirical status

@cite{marco-rasin-2026} show that OP cannot simultaneously predict the
distribution of schwa in verbs, nouns, and adjectives in
Judeo-Tripolitanian Arabic: adjectives pattern phonologically with
verbs but paradigmatically with nouns — contradicting OP's prediction
that phonological behavior tracks paradigm structure. See
`Phenomena/Phonology/Studies/MarcoRasin2026.lean`.
-/

namespace Phonology.ParadigmUniformity

open Core.Constraint.OT (NamedConstraint ConstraintFamily)
open Phonology.Correspondence (Corr CorrDomain)

-- ============================================================================
-- § 1: OP-MAX-V
-- ============================================================================

/-- Build an OP-MAX-V constraint: penalises paradigm non-uniformity with
    respect to vowel positions.

    `vowelMismatch a b` counts positions where form `a` has a vowel and
    form `b` does not. The full constraint sums this over all ordered
    pairs in the paradigm.

    Conceptually, this is the symmetric pairwise lift of OO-MAX
    restricted to vocalic positions. When the forms are modelled as
    `Corr` (output-to-output correspondence), `vowelMismatch` reduces
    to `Corr.maxViol` on the vowel tier. -/
def mkOPMaxV {Form : Type} (vowelMismatch : Form → Form → Nat) :
    NamedConstraint (List Form) :=
  liftPairwise "OP-MAX-V" .faithfulness vowelMismatch

-- ============================================================================
-- § 2: Majority Rules
-- ============================================================================

/-- The Majority Rules condition (@cite{mccarthy-2005}): when a paradigm
    member is equivocal between two forms (both satisfy higher-ranked
    markedness constraints equally), OP predicts it will align with the
    group containing more members.

    `majority groupA groupB` holds when group A outnumbers group B.
    Under OP, the equivocal member surfaces with group A's form,
    because aligning with the larger group minimises total pairwise
    OP-MAX-V violations. -/
def majorityRules (groupA groupB : Nat) : Prop :=
  groupA > groupB

instance (a b : Nat) : Decidable (majorityRules a b) := by
  unfold majorityRules; infer_instance

/-- When one group is larger, the equivocal member's OP-MAX-V violations
    are minimised by aligning with the majority.

    If `a` members have form X and `b` members have form Y, and one
    equivocal member chooses form X, the OP-MAX-V violations from
    cross-group pairs are `(a + 1) * b * 2`. Choosing Y instead gives
    `a * (b + 1) * 2`. The former is smaller iff `a > b` (since
    `(a+1)*b = ab + b < ab + a = a*(b+1)` when `a > b`). -/
theorem majority_minimizes_violations (a b : Nat) (h : a > b) :
    (a + 1) * b < a * (b + 1) := by
  rw [Nat.add_mul, Nat.mul_add]; omega

end Phonology.ParadigmUniformity
