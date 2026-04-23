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

OP-MAX-V is **derived from `Corr.maxViol`** via a tier projection:
`vowelMismatch a b := (Corr.parallel (proj a) (proj b)).maxViol .lhs .rhs`
where `proj : Form → List Vowel` extracts the vocalic tier. This makes
the docstring claim "OP-MAX-V reduces to MAX-IO on the vowel tier"
true by construction rather than by stipulation.

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
open Phonology.Correspondence (Corr)

-- ============================================================================
-- § 1: OP-MAX-V derived from `Corr.maxViol` via tier projection
-- ============================================================================

/-- Vowel mismatch between two forms, derived from `Corr.maxViol` on the
    vowel-tier projection. The structural realization of "OP-MAX-V is
    MAX-IO on the vowel tier": no stipulated callback, the count comes
    from the unifying `Corr` substrate. -/
def vowelMismatchFromTier {Form Vowel : Type}
    (proj : Form → List Vowel) (a b : Form) : ℕ :=
  (Corr.parallel (proj a) (proj b)).maxViol .lhs .rhs

/-- Build an OP-MAX-V constraint from a tier projection. The symmetric
    pairwise lift of OO-MAX restricted to vocalic positions, with the
    underlying violation count derived from `Corr.maxViol` rather than
    stipulated.

    For backward compatibility, `mkOPMaxV` (below) still accepts an
    abstract `vowelMismatch : Form → Form → Nat` callback; the new
    `mkOPMaxVFromTier` should be preferred for new study files. -/
def mkOPMaxVFromTier {Form Vowel : Type} (proj : Form → List Vowel) :
    NamedConstraint (List Form) :=
  liftPairwise "OP-MAX-V" .faithfulness (vowelMismatchFromTier proj)

/-- Build an OP-MAX-V constraint with an abstract vowel-mismatch callback.
    Kept for compatibility with study files that supply paper-specific
    mismatch counts. New code should use `mkOPMaxVFromTier`. -/
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
