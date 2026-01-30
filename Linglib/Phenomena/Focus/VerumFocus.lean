/-
# Verum Focus: Empirical Data

Theory-neutral data on verum focus (VERUM) and its interaction with
negative yes/no questions.

## The Phenomenon

Verum focus (Höhle 1992) is focus on the truth/polarity of a proposition,
signaling that the speaker is addressing whether p should be added to
the Common Ground.

  "Does John DRINK?" (focus on truth, not on 'drink')
  "John DOES drink." (emphatic affirmation)

## Key Properties

1. **Preposed negation**: "Doesn't John drink?" vs "Does John not drink?"
2. **Epistemic implicature**: Preposed negation forces positive bias
3. **PI/NI ambiguity**: "Isn't Jane coming {too/either}?" (Ladd 1981)
4. **VERUM sources**: Preposed negation, "really", focus on auxiliary

## References

- Höhle, T. (1992). Über Verum-Fokus im Deutschen.
- Ladd, D.R. (1981). A First Look at the Semantics and Pragmatics of
  Negative Questions and Tag Questions.
- Romero, M. & Han, C.-H. (2004). On Negative Yes/No Questions.
-/

import Linglib.Phenomena.Basic

namespace Phenomena.Focus.VerumFocus

-- ============================================================================
-- Part 1: Basic Verum Focus Data
-- ============================================================================

/-- A verum focus datum records a sentence with its verum interpretation -/
structure VerumFocusDatum where
  /-- The sentence -/
  sentence : String
  /-- Does this have verum focus? -/
  hasVerumFocus : Bool
  /-- Source of verum focus (if any) -/
  verumSource : Option String  -- "preposed_neg", "really", "aux_focus", etc.
  /-- Epistemic bias (positive, negative, or none) -/
  epistemicBias : Option String
  /-- Notes -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

/-- Preposed vs non-preposed negation contrast (Romero & Han 2004 core data) -/
def preposedNegation : VerumFocusDatum := {
  sentence := "Doesn't John drink?"
  hasVerumFocus := true
  verumSource := some "preposed_neg"
  epistemicBias := some "positive"
  notes := "Preposed negation necessarily triggers VERUM. Speaker expected 'yes'."
  source := "Romero & Han (2004)"
}

def nonPreposedNegation : VerumFocusDatum := {
  sentence := "Does John not drink?"
  hasVerumFocus := false
  verumSource := none
  epistemicBias := none
  notes := "Non-preposed negation: neutral information-seeking question possible."
  source := "Romero & Han (2004)"
}

/-- Adverb "really" as VERUM source -/
def reallyVerum : VerumFocusDatum := {
  sentence := "Does John really drink?"
  hasVerumFocus := true
  verumSource := some "really"
  epistemicBias := some "positive"
  notes := "'Really' contributes VERUM. Speaker expected 'yes' but doubts."
  source := "Romero & Han (2004)"
}

/-- Focus on auxiliary as VERUM source -/
def auxFocusVerum : VerumFocusDatum := {
  sentence := "DOES John drink?"
  hasVerumFocus := true
  verumSource := some "aux_focus"
  epistemicBias := some "positive"
  notes := "Pitch accent on auxiliary signals verum focus."
  source := "Höhle (1992)"
}

/-- Focused NOT (negation focus) -/
def notFocusVerum : VerumFocusDatum := {
  sentence := "Does John NOT drink?"
  hasVerumFocus := true
  verumSource := some "not_focus"
  epistemicBias := some "negative"
  notes := "Pitch accent on NOT: speaker expected 'no' (negative bias)."
  source := "Romero & Han (2004)"
}

-- ============================================================================
-- Part 2: Ladd's PI/NI Ambiguity (Positive/Negative Epistemic Implicature)
-- ============================================================================

/-- Ladd's (1981) ambiguity: same form, opposite implicatures -/
structure LaddAmbiguityDatum where
  /-- The question form -/
  question : String
  /-- Positive-implicature variant (with PPIs like "too") -/
  piVariant : String
  /-- Negative-implicature variant (with NPIs like "either") -/
  niVariant : String
  /-- PI interpretation -/
  piReading : String
  /-- NI interpretation -/
  niReading : String
  /-- Notes -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

/-- Classic Ladd example -/
def laddJaneComing : LaddAmbiguityDatum := {
  question := "Isn't Jane coming ___?"
  piVariant := "Isn't Jane coming too?"
  niVariant := "Isn't Jane coming either?"
  piReading := "I thought Jane was coming. [double-check p]"
  niReading := "I thought Jane wasn't coming. [double-check ¬p]"
  notes := "PPIs (too) → PI; NPIs (either) → NI. Demonstrates p/¬p structural ambiguity."
  source := "Ladd (1981)"
}

/-- Another Ladd example with some/any -/
def laddSomeAny : LaddAmbiguityDatum := {
  question := "Wasn't there ___ pizza left?"
  piVariant := "Wasn't there some pizza left?"
  niVariant := "Wasn't there any pizza left?"
  piReading := "I thought there was pizza. [surprised if none]"
  niReading := "I thought there wasn't pizza. [surprised if some]"
  notes := "Some (PPI) → PI; any (NPI) → NI."
  source := "Ladd (1981)"
}

/-- Already/yet contrast -/
def laddAlreadyYet : LaddAmbiguityDatum := {
  question := "Hasn't John ___ left?"
  piVariant := "Hasn't John already left?"
  niVariant := "Hasn't John left yet?"
  piReading := "I expected John to have left. [double-check p]"
  niReading := "I expected John not to have left. [double-check ¬p]"
  notes := "Already (PPI) → PI; yet (NPI) → NI."
  source := "Romero & Han (2004)"
}

-- ============================================================================
-- Part 3: VERUM Scope and LF Structure
-- ============================================================================

/-- LF structure for PI vs NI questions -/
structure LFStructureDatum where
  /-- Surface form -/
  surface : String
  /-- Reading type -/
  readingType : String  -- "PI" or "NI"
  /-- LF representation -/
  lf : String
  /-- Paraphrase -/
  paraphrase : String
  /-- Notes -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

/-- PI question LF: negation scopes over VERUM -/
def piQuestionLF : LFStructureDatum := {
  surface := "Isn't Jane coming too?"
  readingType := "PI"
  lf := "[Q [not [VERUM [Jane is coming]]]]"
  paraphrase := "Is it not for-sure-CG that Jane is coming?"
  notes := "VERUM below negation. Speaker asks: shouldn't we add p to CG?"
  source := "Romero & Han (2004)"
}

/-- NI question LF: VERUM scopes over negation -/
def niQuestionLF : LFStructureDatum := {
  surface := "Isn't Jane coming either?"
  readingType := "NI"
  lf := "[Q [VERUM [not [Jane is coming]]]]"
  paraphrase := "Is it for-sure-CG that Jane is not coming?"
  notes := "VERUM above negation. Speaker asks: should we add ¬p to CG?"
  source := "Romero & Han (2004)"
}

-- ============================================================================
-- Part 4: Cross-linguistic Data
-- ============================================================================

/-- Cross-linguistic verum focus data -/
structure CrossLinguisticDatum where
  /-- Language -/
  language : String
  /-- Sentence -/
  sentence : String
  /-- Gloss -/
  gloss : String
  /-- Translation -/
  translation : String
  /-- Verum marking strategy -/
  verumStrategy : String
  /-- Notes -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

/-- German: clitic position determines PI vs NI -/
def germanVerum : CrossLinguisticDatum := {
  language := "German"
  sentence := "Hat Hans nicht schon angerufen?"
  gloss := "Has Hans not already called?"
  translation := "Hasn't Hans already called?"
  verumStrategy := "clitic_position"
  notes := "German uses clitic position to disambiguate. 'nicht' placement matters."
  source := "Romero & Han (2004)"
}

/-- Spanish: tampoco/también for NI/PI -/
def spanishVerum : CrossLinguisticDatum := {
  language := "Spanish"
  sentence := "¿No viene María también/tampoco?"
  gloss := "Not comes María too/either?"
  translation := "Isn't María coming too/either?"
  verumStrategy := "polarity_item"
  notes := "Spanish uses PPIs/NPIs like English to disambiguate."
  source := "Romero & Han (2004)"
}

/-- Korean: morphological marking -/
def koreanVerum : CrossLinguisticDatum := {
  language := "Korean"
  sentence := "Chelswu-ka an o-ni?"
  gloss := "Chelswu-NOM not come-Q?"
  translation := "Isn't Chelswu coming?"
  verumStrategy := "morphological"
  notes := "Korean 'an' negation with question particle. Bias depends on context."
  source := "Romero & Han (2004)"
}

/-- Bulgarian: separate negation and question particles -/
def bulgarianVerum : CrossLinguisticDatum := {
  language := "Bulgarian"
  sentence := "Ne dojde li Ivan?"
  gloss := "Not came Q Ivan?"
  translation := "Didn't Ivan come?"
  verumStrategy := "particle_order"
  notes := "Bulgarian negation-question particle order encodes bias."
  source := "Romero & Han (2004)"
}

/-- Modern Greek: dhen vs mi negation -/
def greekVerum : CrossLinguisticDatum := {
  language := "Modern Greek"
  sentence := "Dhen irthe o Yannis?"
  gloss := "Not came the Yannis?"
  translation := "Didn't Yannis come?"
  verumStrategy := "negation_choice"
  notes := "'Dhen' (indicative neg) vs 'mi' (subjunctive neg) affects bias."
  source := "Romero & Han (2004)"
}

-- ============================================================================
-- Part 5: Unbalanced Partition Data
-- ============================================================================

/-- Data on balanced vs unbalanced question partitions -/
structure PartitionDatum where
  /-- The question -/
  question : String
  /-- Is the partition balanced ({p, ¬p})? -/
  balanced : Bool
  /-- Partition cells (if unbalanced, what are they?) -/
  partitionDescription : String
  /-- Which cell is "pronounced" (asked about)? -/
  pronouncedCell : String
  /-- Notes -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

/-- Neutral question: balanced partition -/
def balancedPartition : PartitionDatum := {
  question := "Does John drink?"
  balanced := true
  partitionDescription := "{John drinks, John doesn't drink}"
  pronouncedCell := "p (surface form)"
  notes := "Standard yes/no question. Balanced partition, no bias."
  source := "Romero & Han (2004)"
}

/-- PI question: unbalanced partition -/
def piUnbalancedPartition : PartitionDatum := {
  question := "Doesn't John drink? [PI reading]"
  balanced := false
  partitionDescription := "{FOR-SURE-CG(p), ¬FOR-SURE-CG(p)}"
  pronouncedCell := "¬FOR-SURE-CG(p)"
  notes := "VERUM creates unbalanced partition. Pronounced ¬FOR-SURE-CG(p) implicates belief in p."
  source := "Romero & Han (2004)"
}

/-- NI question: unbalanced partition (different direction) -/
def niUnbalancedPartition : PartitionDatum := {
  question := "Doesn't John drink? [NI reading]"
  balanced := false
  partitionDescription := "{FOR-SURE-CG(¬p), ¬FOR-SURE-CG(¬p)}"
  pronouncedCell := "FOR-SURE-CG(¬p)"
  notes := "VERUM scopes over negation. Pronounced FOR-SURE-CG(¬p) implicates belief in ¬p."
  source := "Romero & Han (2004)"
}

-- ============================================================================
-- Part 6: Generalization Data
-- ============================================================================

/-- Romero & Han's Generalization 1 -/
def generalization1 : String :=
  "Preposed negation yes/no questions necessarily carry a positive epistemic " ++
  "implicature. Non-preposed negation yes/no questions do not necessarily carry " ++
  "an epistemic implicature."

/-- Romero & Han's Generalization 2 (Ladd's p/¬p ambiguity) -/
def generalization2 : String :=
  "Preposed negation yes/no questions are potentially ambiguous between two readings: " ++
  "PI-reading (double-check p, licenses PPIs) and NI-reading (double-check ¬p, licenses NPIs)."

-- ============================================================================
-- Part 7: Collected Data
-- ============================================================================

/-- All basic verum focus data -/
def verumFocusData : List VerumFocusDatum := [
  preposedNegation,
  nonPreposedNegation,
  reallyVerum,
  auxFocusVerum,
  notFocusVerum
]

/-- All Ladd ambiguity data -/
def laddAmbiguityData : List LaddAmbiguityDatum := [
  laddJaneComing,
  laddSomeAny,
  laddAlreadyYet
]

/-- All LF structure data -/
def lfStructureData : List LFStructureDatum := [
  piQuestionLF,
  niQuestionLF
]

/-- All cross-linguistic data -/
def crossLinguisticData : List CrossLinguisticDatum := [
  germanVerum,
  spanishVerum,
  koreanVerum,
  bulgarianVerum,
  greekVerum
]

/-- All partition data -/
def partitionData : List PartitionDatum := [
  balancedPartition,
  piUnbalancedPartition,
  niUnbalancedPartition
]

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Data Types
- `VerumFocusDatum`: Basic verum focus with source and bias
- `LaddAmbiguityDatum`: PI vs NI question pairs
- `LFStructureDatum`: LF representations showing VERUM/negation scope
- `CrossLinguisticDatum`: Cross-linguistic verum strategies
- `PartitionDatum`: Balanced vs unbalanced question partitions

### Key Examples
- Preposed vs non-preposed negation contrast
- Ladd's "Isn't Jane coming {too/either}?" ambiguity
- Cross-linguistic data: German, Spanish, Korean, Bulgarian, Greek

### Theoretical Neutrality

This module records WHAT the data is. Theoretical analyses include:
- **Romero & Han (2004)**: VERUM as conversational epistemic operator
- **Ladd (1981)**: p/¬p structural ambiguity
- **van Rooy & Šafářová (2003)**: Decision-theoretic bias (see Polarity.lean)

All theories must account for:
1. Preposed negation forces epistemic implicature
2. PI vs NI readings (Ladd's ambiguity)
3. Cross-linguistic variation in verum marking
4. Polarity item licensing under PI/NI readings

### Promissory Notes: Future Theoretical Work

**VERUM Operator** (`Theories/Montague/Questions/VerumFocus.lean`):
- `FOR-SURE-CG_x(p)` = ∀w' ∈ Epi_x(w)[∀w'' ∈ Conv_x(w')[p ∈ CG_w'']]
- Unbalanced partition semantics
- Scope interactions with negation

**Connection to Polarity.lean**:
- van Rooy & Šafářová explain WHICH question to use (decision theory)
- Romero & Han explain WHY preposed negation forces bias (VERUM)
-/

end Phenomena.Focus.VerumFocus
