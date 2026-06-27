import Linglib.Phonology.Constraints.Lift

/-!
# Optimal Paradigms — McCarthy 2005
[mccarthy-2005] [kenstowicz-1996]

Optimal Paradigms (OP) evaluates **inflectional paradigms** as candidates
rather than individual forms: output-output faithfulness applies *symmetrically*
across every member-pair, with no distinguished base. OP is McCarthy's
successor to the Base-Identity / Uniform Exponence programme ([kenstowicz-1996]),
which first stated the symmetric all-pairs paradigm-uniformity constraint that
`Constraints.liftPairwise` packages.

This file holds the OP *substrate* — the paper's framework apparatus, anchored to
its originating paper and consumed by later study files. OP needs no new
evaluation machinery: the existing tableau infrastructure is polymorphic in the
candidate type `C`, so setting `C := List Form` gives paradigm-level evaluation
for free. The OP-specific content is just the choice of constraint
(`mkOPMaxV`) and the Majority Rules prediction (`majority_minimizes_violations`).

## Main definitions

* `mkOPMaxV` — an OP-MAX-V constraint: symmetric pairwise OO-faithfulness on the
  vowel tier, built from `Constraints.liftPairwise`.
* `majorityRules` / `majority_minimizes_violations` — the Majority Rules
  prediction: an equivocal paradigm member aligns with the larger group.

## Empirical status

[marco-rasin-2026] argue OP cannot simultaneously predict the distribution of
schwa in verbs, nouns, and adjectives in Judeo-Tripolitanian Arabic — adjectives
pattern phonologically with verbs but paradigmatically with nouns, contradicting
OP's prediction that phonological behaviour tracks paradigm structure. See
`Studies/MarcoRasin2026.lean`, which consumes `mkOPMaxV` from this file.

## TODO: the base-selection axis

OP is the *no-base* corner of paradigm uniformity (symmetric over all members);
TCT ([benua-1997]) stipulates a base; Albright's Single Surface Base
([albright-2002]) *learns* one. These are three instantiations of one
base-choice interface (`selectBase : Paradigm → Option Member`) that this module
does not yet expose — the contemporary "how is the base chosen / is PU learned"
debate. An [albright-2002]-anchored study with a base-informativeness functional
would make OP, TCT, and Albright comparable instances rather than disjoint files.
-/

namespace McCarthy2005

open Constraints

/-! ### OP-MAX-V -/

/-- An OP-MAX-V constraint: the symmetric pairwise lift of OO-MAX restricted to
    the vocalic tier, summing a vowel-mismatch count over every paradigm
    member-pair. OP faithfulness is *output-output* (intra-paradigm); the
    mismatch callback supplies the tier-restricted comparison. -/
def mkOPMaxV {Form : Type*} (vowelMismatch : Form → Form → Nat) :
    NamedConstraint (List Form) :=
  liftPairwise "OP-MAX-V" .faithfulness vowelMismatch

/-! ### Majority Rules -/

/-- The Majority Rules condition ([mccarthy-2005]): when a paradigm member is
    equivocal between two forms (both satisfy higher-ranked markedness equally),
    OP predicts it aligns with the group containing more members.

    `majorityRules groupA groupB` holds when group A outnumbers group B; under OP
    the equivocal member then surfaces with group A's form, because aligning with
    the larger group minimises total pairwise OP-MAX-V violations. -/
def majorityRules (groupA groupB : Nat) : Prop := groupA > groupB

instance (a b : Nat) : Decidable (majorityRules a b) := by
  unfold majorityRules; infer_instance

/-- When one group is larger, the equivocal member's OP-MAX-V violations are
    minimised by aligning with the majority. If `a` members have form X and `b`
    have form Y, choosing X gives `(a + 1) * b` cross-group pairs while choosing
    Y gives `a * (b + 1)`; the former is smaller iff `a > b`. -/
theorem majority_minimizes_violations (a b : Nat) (h : majorityRules a b) :
    (a + 1) * b < a * (b + 1) := by
  unfold majorityRules at h; rw [Nat.add_mul, Nat.mul_add]; omega

end McCarthy2005
