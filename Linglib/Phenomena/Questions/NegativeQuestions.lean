/-
# Negative Questions: Empirical Data

Theory-neutral data on negative yes/no questions and epistemic bias.

## The Phenomenon

Negative questions exhibit systematic asymmetries in interpretation:

1. Preposed vs non-preposed negation:
   - "Doesn't John drink?" → speaker expects "yes" (positive bias)
   - "Does John not drink?" → neutral information-seeking possible

2. PI/NI ambiguity (Ladd 1981):
   - "Isn't Jane coming too?" → positive implicature (PI)
   - "Isn't Jane coming either?" → negative implicature (NI)

3. Cross-linguistic variation in how languages mark epistemic bias

## Theoretical Analyses

Different theories explain these facts:
- Verum Focus (Höhle 1992, Romero & Han 2004): Covert VERUM operator
- Decision Theory (van Rooy & Šafářová 2003): Utility-based question choice
- Structural ambiguity (Ladd 1981): p/¬p scope ambiguity

This file records the phenomena; theories belong in Theories/.

## Related Files

- `Focus/PolarityStress.lean` - Prosodic stress on auxiliaries/negation
- `Polarity/` - NPI/PPI licensing in these contexts

## References

- Ladd, D.R. (1981). A First Look at the Semantics and Pragmatics of
  Negative Questions and Tag Questions.
- Romero, M. & Han, C.-H. (2004). On Negative Yes/No Questions.
- van Rooy, R. & Šafářová, M. (2003). On Polar Questions.
-/

import Linglib.Core.Word

namespace Phenomena.Questions.NegativeQuestions

-- Part 1: Negative Question Data

/-- A negative question datum records epistemic bias -/
structure NegativeQuestionDatum where
  /-- The sentence -/
  sentence : String
  /-- Negation position -/
  negationPosition : String  -- "preposed", "non_preposed", "none"
  /-- Epistemic bias (positive, negative, or none) -/
  epistemicBias : Option String
  /-- Notes -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

/-- Preposed negation forces positive bias -/
def preposedNegation : NegativeQuestionDatum := {
  sentence := "Doesn't John drink?"
  negationPosition := "preposed"
  epistemicBias := some "positive"
  notes := "Preposed negation forces positive bias. Speaker expected 'yes'."
  source := "Romero & Han (2004)"
}

/-- Non-preposed negation allows neutral reading -/
def nonPreposedNegation : NegativeQuestionDatum := {
  sentence := "Does John not drink?"
  negationPosition := "non_preposed"
  epistemicBias := none
  notes := "Non-preposed negation: neutral information-seeking question possible."
  source := "Romero & Han (2004)"
}

/-- Adverb "really" triggers positive bias -/
def reallyBias : NegativeQuestionDatum := {
  sentence := "Does John really drink?"
  negationPosition := "none"
  epistemicBias := some "positive"
  notes := "'Really' signals speaker checking expected positive answer."
  source := "Romero & Han (2004)"
}

-- Part 2: Ladd's PI/NI Ambiguity

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

-- Part 3: Cross-linguistic Data

/-- Cross-linguistic negative question data -/
structure CrossLinguisticDatum where
  /-- Language -/
  language : String
  /-- Sentence -/
  sentence : String
  /-- Gloss -/
  gloss : String
  /-- Translation -/
  translation : String
  /-- How the language marks bias -/
  biasStrategy : String
  /-- Notes -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

/-- German: clitic position determines PI vs NI -/
def germanNegQ : CrossLinguisticDatum := {
  language := "German"
  sentence := "Hat Hans nicht schon angerufen?"
  gloss := "Has Hans not already called?"
  translation := "Hasn't Hans already called?"
  biasStrategy := "clitic_position"
  notes := "German uses clitic position to disambiguate. 'nicht' placement matters."
  source := "Romero & Han (2004)"
}

/-- Spanish: tampoco/también for NI/PI -/
def spanishNegQ : CrossLinguisticDatum := {
  language := "Spanish"
  sentence := "¿No viene María también/tampoco?"
  gloss := "Not comes María too/either?"
  translation := "Isn't María coming too/either?"
  biasStrategy := "polarity_item"
  notes := "Spanish uses PPIs/NPIs like English to disambiguate."
  source := "Romero & Han (2004)"
}

/-- Korean: morphological marking -/
def koreanNegQ : CrossLinguisticDatum := {
  language := "Korean"
  sentence := "Chelswu-ka an o-ni?"
  gloss := "Chelswu-NOM not come-Q?"
  translation := "Isn't Chelswu coming?"
  biasStrategy := "morphological"
  notes := "Korean 'an' negation with question particle. Bias depends on context."
  source := "Romero & Han (2004)"
}

/-- Bulgarian: separate negation and question particles -/
def bulgarianNegQ : CrossLinguisticDatum := {
  language := "Bulgarian"
  sentence := "Ne dojde li Ivan?"
  gloss := "Not came Q Ivan?"
  translation := "Didn't Ivan come?"
  biasStrategy := "particle_order"
  notes := "Bulgarian negation-question particle order encodes bias."
  source := "Romero & Han (2004)"
}

/-- Modern Greek: dhen vs mi negation -/
def greekNegQ : CrossLinguisticDatum := {
  language := "Modern Greek"
  sentence := "Dhen irthe o Yannis?"
  gloss := "Not came the Yannis?"
  translation := "Didn't Yannis come?"
  biasStrategy := "negation_choice"
  notes := "'Dhen' (indicative neg) vs 'mi' (subjunctive neg) affects bias."
  source := "Romero & Han (2004)"
}

-- Part 4: Question Partition Data

/-- Data on balanced vs unbalanced question partitions -/
structure PartitionDatum where
  /-- The question -/
  question : String
  /-- Is the partition balanced ({p, ¬p})? -/
  balanced : Bool
  /-- Partition cells description -/
  partitionDescription : String
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
  notes := "Standard yes/no question. Balanced partition, no bias."
  source := "Romero & Han (2004)"
}

/-- Negative question with positive bias: unbalanced -/
def piUnbalancedPartition : PartitionDatum := {
  question := "Doesn't John drink? [PI reading]"
  balanced := false
  partitionDescription := "Speaker expects positive answer"
  notes := "Preposed negation creates unbalanced partition favoring 'yes'."
  source := "Romero & Han (2004)"
}

/-- Negative question with negative bias: unbalanced -/
def niUnbalancedPartition : PartitionDatum := {
  question := "Doesn't John drink? [NI reading]"
  balanced := false
  partitionDescription := "Speaker expects negative answer"
  notes := "NI reading creates unbalanced partition favoring 'no'."
  source := "Romero & Han (2004)"
}

-- Part 5: Generalizations

/-- Romero & Han's Generalization 1 -/
def generalization1 : String :=
  "Preposed negation yes/no questions necessarily carry a positive epistemic " ++
  "implicature. Non-preposed negation yes/no questions do not necessarily carry " ++
  "an epistemic implicature."

/-- Romero & Han's Generalization 2 (Ladd's p/¬p ambiguity) -/
def generalization2 : String :=
  "Preposed negation yes/no questions are potentially ambiguous between two readings: " ++
  "PI-reading (double-check p, licenses PPIs) and NI-reading (double-check ¬p, licenses NPIs)."

-- Part 6: Collected Data

/-- All basic negative question data -/
def negativeQuestionData : List NegativeQuestionDatum := [
  preposedNegation,
  nonPreposedNegation,
  reallyBias
]

/-- All Ladd ambiguity data -/
def laddAmbiguityData : List LaddAmbiguityDatum := [
  laddJaneComing,
  laddSomeAny,
  laddAlreadyYet
]

/-- All cross-linguistic data -/
def crossLinguisticData : List CrossLinguisticDatum := [
  germanNegQ,
  spanishNegQ,
  koreanNegQ,
  bulgarianNegQ,
  greekNegQ
]

/-- All partition data -/
def partitionData : List PartitionDatum := [
  balancedPartition,
  piUnbalancedPartition,
  niUnbalancedPartition
]

end Phenomena.Questions.NegativeQuestions
