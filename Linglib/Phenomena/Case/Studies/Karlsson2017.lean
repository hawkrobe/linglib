import Linglib.Core.Case
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Core.Lexical.MorphRule

/-!
# Finnish Case System @cite{karlsson-2017}
@cite{krifka-1989}

The Finnish partitive case is the primary formal link between case marking
and aspectual interpretation in the language (@cite{karlsson-2017}, Chs. 9, 12–13).
The case of the direct object determines — or reflects — the telicity of
the VP:

- **Accusative/genitive object** → telic (bounded, resultative):
  *Luin kirja-n.* 'I read the book (completely).'

- **Partitive object** → atelic (unbounded, irresultative):
  *Luin kirja-a.* 'I read the book / was reading the book (partially).'

The partitive also appears obligatorily under negation:
  *En lukenut kirja-a.* 'I didn't read the book.'

This is the first bridge in linglib connecting `Core.Case` to
`Semantics.Tense.Aspect.LexicalAspect.Telicity`, making the case–aspect
interaction formally verifiable.

## Theoretical significance

Finnish partitive is evidence for the **Incremental Theme** hypothesis: the object's referential properties (bounded vs.
unbounded) compose with the verb's event structure to determine VP-level
telicity. The case morphology makes this composition visible.

-/

namespace Phenomena.Case.Studies.Karlsson2017

open Semantics.Tense.Aspect.LexicalAspect (Telicity)

-- ============================================================================
-- § 1: Case–Aspect Mapping
-- ============================================================================

/-- The case of the Finnish direct object maps to VP telicity.
    Accusative/genitive → telic; partitive → atelic. -/
def objectCaseToTelicity : Core.Case → Option Telicity
  | .acc | .gen => some .telic     -- bounded object → telic VP
  | .part      => some .atelic    -- unbounded object → atelic VP
  | _          => none            -- not an object case

/-- Context in which partitive case is obligatory (Karlsson §12.3). -/
inductive PartitiveLicensor where
  /-- Negation: *en lukenut kirja-a* -/
  | negation
  /-- Unbounded quantity: *join vettä* ('I drank water') -/
  | unboundedQuantity
  /-- Irresultative action: *luin kirjaa* ('I was reading the book') -/
  | irresultative
  deriving DecidableEq, Repr

/-- A partitive licensing datum: object case + licensing context + telicity. -/
structure PartitiveDatum where
  finnish : String
  gloss : String
  objectCase : Core.Case
  licensor : Option PartitiveLicensor
  vpTelicity : Telicity
  deriving Repr, BEq

-- ============================================================================
-- § 2: Data
-- ============================================================================

/-- Accusative object, telic VP: 'I read the book (completely).' -/
def readBookComplete : PartitiveDatum :=
  { finnish := "Luin kirjan"
  , gloss := "I read the book (completely)"
  , objectCase := .acc
  , licensor := none
  , vpTelicity := .telic }

/-- Partitive object, atelic VP (irresultative): 'I was reading the book.' -/
def readBookPartial : PartitiveDatum :=
  { finnish := "Luin kirjaa"
  , gloss := "I was reading the book (partially)"
  , objectCase := .part
  , licensor := some .irresultative
  , vpTelicity := .atelic }

/-- Partitive under negation: 'I didn't read the book.' -/
def readBookNegated : PartitiveDatum :=
  { finnish := "En lukenut kirjaa"
  , gloss := "I didn't read the book"
  , objectCase := .part
  , licensor := some .negation
  , vpTelicity := .atelic }

/-- Partitive with mass noun (unbounded quantity): 'I drank water.' -/
def drankWater : PartitiveDatum :=
  { finnish := "Join vettä"
  , gloss := "I drank (some) water"
  , objectCase := .part
  , licensor := some .unboundedQuantity
  , vpTelicity := .atelic }

def allData : List PartitiveDatum :=
  [readBookComplete, readBookPartial, readBookNegated, drankWater]

-- ============================================================================
-- § 3: Bridge Theorems
-- ============================================================================

/-- Accusative object maps to telic VP. -/
theorem acc_telic : objectCaseToTelicity .acc = some .telic := rfl

/-- Partitive object maps to atelic VP. -/
theorem part_atelic : objectCaseToTelicity .part = some .atelic := rfl

/-- Genitive object (used for total objects in some environments) maps
    to telic, same as accusative. -/
theorem gen_telic : objectCaseToTelicity .gen = some .telic := rfl

/-- For every datum, the `objectCaseToTelicity` mapping agrees with the
    annotated `vpTelicity`. -/
theorem mapping_agrees_with_data :
    allData.all (fun d =>
      objectCaseToTelicity d.objectCase == some d.vpTelicity) = true := by
  native_decide

/-- All partitive data have atelic VP interpretation. -/
theorem partitive_implies_atelic :
    (allData.filter (·.objectCase == .part)).all
      (·.vpTelicity == .atelic) = true := by native_decide

/-- All accusative data have telic VP interpretation. -/
theorem accusative_implies_telic :
    (allData.filter (·.objectCase == .acc)).all
      (·.vpTelicity == .telic) = true := by native_decide

/-- Every partitive datum has a licensor (negation, quantity, or aspect). -/
theorem partitive_has_licensor :
    (allData.filter (·.objectCase == .part)).all
      (fun d => d.licensor.isSome) = true := by native_decide

-- ============================================================================
-- Part II: Suffix Order vs. Bybee's Relevance Hierarchy
-- ============================================================================

open Core.Morphology (MorphCategory respectsRelevanceHierarchy)

-- ============================================================================
-- § 5: Finnish Nominal Suffix Slots
-- ============================================================================

/-- A morpheme slot in Finnish nominal morphology. -/
inductive NominalSlot where
  | stem
  | number      -- plural marker -i-, -j-
  | case_       -- 15 case suffixes
  | possessive  -- -ni, -si, -nsA, -mme, -nne
  | clitic      -- -kin, -kAAn, -pA, -hAn
  deriving DecidableEq, Repr

/-- Finnish nominal suffix order (Karlsson §7.1). -/
def finnishNominalOrder : List NominalSlot :=
  [.stem, .number, .case_, .possessive, .clitic]

-- ============================================================================
-- § 6: Mapping to Bybee Categories
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
-- § 7: Suffix Order Verification
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

end Phenomena.Case.Studies.Karlsson2017
