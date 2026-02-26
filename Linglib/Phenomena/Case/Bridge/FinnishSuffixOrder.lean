import Linglib.Core.Lexical.MorphRule

/-!
# Finnish Suffix Order vs. Bybee's Relevance Hierarchy @cite{karlsson-2018}

Finnish nominal morphology follows a strict suffix order (Karlsson 2018, Ch. 7):

    STEM + NUMBER + CASE + POSSESSIVE + CLITIC

Example: *talo-i-ssa-ni-kin* ('in my houses too')
- talo (stem: 'house')
- -i- (number: plural)
- -ssa (case: inessive)
- -ni (possessive: 1sg)
- -kin (clitic: 'too')

## Bybee's hierarchy and nominal morphology

Bybee's (1985) relevance hierarchy was designed for **verbal** morphology:

    stem < derivation < valence < voice < aspect < tense < mood < negation < agreement

Finnish nominal suffix order cannot be directly stated in these terms because
Bybee's categories are verb-centric. The nominal categories (number, case)
don't have fixed positions in the verbal hierarchy.

However, linglib's extended `MorphCategory` type includes `number` (rank 3)
and `agreement` (rank 8). Finnish nominal morphology *does* respect the
relative ordering of these: number (rank 3) appears closer to the stem
than possessive agreement (rank 8), consistent with Bybee's prediction
that more semantically relevant categories appear closer to the stem.

## What this file tests

This file verifies that the subset of Finnish nominal suffix slots that
map to Bybee categories respects the relevance hierarchy, and documents
the gap: case has no `MorphCategory` and therefore no Bybee rank.

## References

- Karlsson, F. (2018). *Finnish: A Comprehensive Grammar*. Routledge. Ch. 7.
- Bybee, J. L. (1985). *Morphology: A Study of the Relation between
  Meaning and Form*. Benjamins.
-/

namespace Phenomena.Case.Bridge.FinnishSuffixOrder

open Core.Morphology (MorphCategory respectsRelevanceHierarchy)

-- ============================================================================
-- § 1: Finnish Nominal Suffix Slots
-- ============================================================================

/-- A morpheme slot in Finnish nominal morphology. -/
inductive NominalSlot where
  | stem
  | number      -- plural marker -i-, -j-
  | case_       -- 15 case suffixes
  | possessive  -- -ni, -si, -nsA, -mme, -nne
  | clitic      -- -kin, -kAAn, -pA, -hAn
  deriving DecidableEq, BEq, Repr

/-- Finnish nominal suffix order (Karlsson §7.1). -/
def finnishNominalOrder : List NominalSlot :=
  [.stem, .number, .case_, .possessive, .clitic]

-- ============================================================================
-- § 2: Mapping to Bybee Categories
-- ============================================================================

/-- Map nominal slots to Bybee `MorphCategory` where possible.
    Case has no Bybee equivalent — this is the gap. -/
def slotToBybeeCat : NominalSlot → Option MorphCategory
  | .stem       => some .stem
  | .number     => some .number
  | .case_      => none          -- no Bybee category for case
  | .possessive => some .agreement
  | .clitic     => none          -- clitics are outside Bybee's scope

/-- The Bybee-mappable subset of Finnish nominal slots, in suffix order. -/
def bybeeSlots : List MorphCategory :=
  finnishNominalOrder.filterMap slotToBybeeCat

-- ============================================================================
-- § 3: Verification Theorems
-- ============================================================================

/-- Finnish nominal morphology has exactly 5 suffix slots. -/
theorem five_slots : finnishNominalOrder.length = 5 := by native_decide

/-- Only 3 of 5 nominal slots have Bybee equivalents (stem, number, agreement). -/
theorem three_bybee_mappable : bybeeSlots.length = 3 := by native_decide

/-- The Bybee-mappable slots are: stem, number, agreement. -/
theorem bybee_slots_are :
    bybeeSlots = [.stem, .number, .agreement] := by native_decide

/-- The Bybee-mappable nominal slots respect the relevance hierarchy:
    stem (0) < number (3) < agreement (8). -/
theorem nominal_respects_bybee :
    respectsRelevanceHierarchy bybeeSlots = true := by native_decide

/-- Case has no Bybee category — this is the gap that Finnish nominal
    morphology reveals in Bybee's verb-centric hierarchy. -/
theorem case_no_bybee_category :
    slotToBybeeCat .case_ = none := rfl

/-- Clitic is also outside Bybee's scope. -/
theorem clitic_no_bybee_category :
    slotToBybeeCat .clitic = none := rfl

/-- Number (rank 3) is more stem-relevant than possessive agreement (rank 8),
    consistent with number appearing closer to the stem in Finnish. -/
theorem number_closer_than_agreement :
    MorphCategory.relevanceRank .number <
    MorphCategory.relevanceRank .agreement := by decide

end Phenomena.Case.Bridge.FinnishSuffixOrder
