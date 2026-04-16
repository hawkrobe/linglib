import Linglib.Theories.Semantics.Questions.VerumFocus
import Linglib.Core.Lexical.Word

/-!
# Romero & Han (2004): Negative Yes/No Questions and Epistemic Bias
@cite{romero-han-2004}

## Core Contribution

Preposed negation in yes/no questions forces an epistemic implicature via
the VERUM operator (FOR-SURE-CG). The Ladd PI/NI ambiguity is scope ambiguity:

- PI: [Q [not [VERUM [p]]]] → speaker believes p, double-checking
- NI: [Q [VERUM [not [p]]]] → speaker believes ¬p, double-checking

## Data

Negative question data, Ladd's ambiguity examples, and cross-linguistic
bias-marking strategies. Originally in `NegativeQuestions.lean`; moved here
for provenance tracking.

## Connection to Existing Infrastructure

- `Theories/Semantics/Questions/VerumFocus.lean`: formal VERUM semantics
- `Phenomena/Questions/Studies/Holmberg2016.lean`: complementary analysis —
  R&H explains *structural source of bias*, @cite{holmberg-2016} explains
  *cross-linguistic answer variation*
-/

namespace RomeroHan2004

open Semantics.Questions.VerumFocus

-- ════════════════════════════════════════════════════════════════
-- § 1. Negative question data
-- ════════════════════════════════════════════════════════════════

/-- A negative question datum records epistemic bias. -/
structure NegativeQuestionDatum where
  /-- The sentence -/
  sentence : String
  /-- Negation position -/
  negationPosition : String  -- "preposed", "non_preposed", "none"
  /-- Epistemic bias (positive, negative, or none) -/
  epistemicBias : Option String
  /-- Notes -/
  notes : String := ""
  deriving Repr

/-- Preposed negation forces positive bias. -/
def preposedNegation : NegativeQuestionDatum :=
  { sentence := "Doesn't John drink?"
  , negationPosition := "preposed"
  , epistemicBias := some "positive"
  , notes := "Preposed negation forces positive bias. Speaker expected 'yes'."
  }

/-- Non-preposed negation allows neutral reading. -/
def nonPreposedNegation : NegativeQuestionDatum :=
  { sentence := "Does John not drink?"
  , negationPosition := "non_preposed"
  , epistemicBias := none
  , notes := "Non-preposed negation: neutral information-seeking question possible."
  }

/-- Adverb "really" triggers positive bias. -/
def reallyBias : NegativeQuestionDatum :=
  { sentence := "Does John really drink?"
  , negationPosition := "none"
  , epistemicBias := some "positive"
  , notes := "'Really' signals speaker checking expected positive answer."
  }

/-- Preposed negation necessarily triggers VERUM (bridge to VerumFocus theory). -/
theorem preposed_triggers_verum :
    necessarilyTriggersVerum .preposedNegation = true := rfl

/-- "Really" also triggers VERUM. -/
theorem really_triggers_verum :
    necessarilyTriggersVerum .reallyAdverb = true := rfl

-- ════════════════════════════════════════════════════════════════
-- § 2. Ladd's PI/NI ambiguity
-- ════════════════════════════════════════════════════════════════

/-! @cite{ladd-1981}: the same negative question form is ambiguous between
    positive-implicature (PI) and negative-implicature (NI) readings,
    disambiguated by polarity items. -/

/-- A Ladd ambiguity datum: same form, opposite implicatures. -/
structure LaddAmbiguityDatum where
  /-- The question template -/
  question : String
  /-- Positive-implicature variant (with PPIs like "too") -/
  piVariant : String
  /-- Negative-implicature variant (with NPIs like "either") -/
  niVariant : String
  /-- PI interpretation -/
  piReading : String
  /-- NI interpretation -/
  niReading : String
  deriving Repr

/-- Classic Ladd example: too vs either. -/
def laddJaneComing : LaddAmbiguityDatum :=
  { question := "Isn't Jane coming ___?"
  , piVariant := "Isn't Jane coming too?"
  , niVariant := "Isn't Jane coming either?"
  , piReading := "I thought Jane was coming. [double-check p]"
  , niReading := "I thought Jane wasn't coming. [double-check ¬p]"
  }

/-- Some vs any. -/
def laddSomeAny : LaddAmbiguityDatum :=
  { question := "Wasn't there ___ pizza left?"
  , piVariant := "Wasn't there some pizza left?"
  , niVariant := "Wasn't there any pizza left?"
  , piReading := "I thought there was pizza. [surprised if none]"
  , niReading := "I thought there wasn't pizza. [surprised if some]"
  }

/-- Already vs yet. -/
def laddAlreadyYet : LaddAmbiguityDatum :=
  { question := "Hasn't John ___ left?"
  , piVariant := "Hasn't John already left?"
  , niVariant := "Hasn't John left yet?"
  , piReading := "I expected John to have left. [double-check p]"
  , niReading := "I expected John not to have left. [double-check ¬p]"
  }

/-- PPIs diagnose PI readings; NPIs diagnose NI readings.
    Bridge to the VerumFocus polarity item licensing theory. -/
theorem ppi_diagnoses_pi : isLicensed too .PI = true := rfl
theorem npi_diagnoses_ni : isLicensed either .NI = true := rfl
theorem ppi_blocks_ni : isLicensed too .NI = false := rfl
theorem npi_blocks_pi : isLicensed either .PI = false := rfl

-- ════════════════════════════════════════════════════════════════
-- § 3. Cross-linguistic bias marking
-- ════════════════════════════════════════════════════════════════

/-- Cross-linguistic negative question data. -/
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
  deriving Repr

/-- German: clitic position determines PI vs NI. -/
def germanNegQ : CrossLinguisticDatum :=
  { language := "German"
  , sentence := "Hat Hans nicht schon angerufen?"
  , gloss := "Has Hans not already called?"
  , translation := "Hasn't Hans already called?"
  , biasStrategy := "clitic_position"
  }

/-- Spanish: tampoco/también for NI/PI. -/
def spanishNegQ : CrossLinguisticDatum :=
  { language := "Spanish"
  , sentence := "¿No viene María también/tampoco?"
  , gloss := "Not comes María too/either?"
  , translation := "Isn't María coming too/either?"
  , biasStrategy := "polarity_item"
  }

/-- Korean: morphological marking. -/
def koreanNegQ : CrossLinguisticDatum :=
  { language := "Korean"
  , sentence := "Chelswu-ka an o-ni?"
  , gloss := "Chelswu-NOM not come-Q?"
  , translation := "Isn't Chelswu coming?"
  , biasStrategy := "morphological"
  }

/-- Bulgarian: separate negation and question particles. -/
def bulgarianNegQ : CrossLinguisticDatum :=
  { language := "Bulgarian"
  , sentence := "Ne dojde li Ivan?"
  , gloss := "Not came Q Ivan?"
  , translation := "Didn't Ivan come?"
  , biasStrategy := "particle_order"
  }

/-- Modern Greek: dhen vs mi negation. -/
def greekNegQ : CrossLinguisticDatum :=
  { language := "Modern Greek"
  , sentence := "Dhen irthe o Yannis?"
  , gloss := "Not came the Yannis?"
  , translation := "Didn't Yannis come?"
  , biasStrategy := "negation_choice"
  }

-- ════════════════════════════════════════════════════════════════
-- § 4. Generalizations
-- ════════════════════════════════════════════════════════════════

/-- Generalization 1: preposed negation forces positive epistemic implicature. -/
def generalization1 : String :=
  "Preposed negation yes/no questions necessarily carry a positive epistemic " ++
  "implicature. Non-preposed negation yes/no questions do not necessarily carry " ++
  "an epistemic implicature."

/-- Generalization 2: Ladd's p/¬p ambiguity. -/
def generalization2 : String :=
  "Preposed negation yes/no questions are potentially ambiguous between two readings: " ++
  "PI-reading (double-check p, licenses PPIs) and NI-reading (double-check ¬p, licenses NPIs)."

end RomeroHan2004
