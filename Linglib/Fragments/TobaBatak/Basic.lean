import Linglib.Features.Reflex
import Linglib.Syntax.Extraction
import Linglib.Syntax.Voice.Basic

/-!
# Toba Batak Fragment [erlewine-2018]

Morphosyntactic data for Toba Batak (Austronesian, Sumatra) relevant
to the extraction restriction and pivot system.

Toba Batak is predicate-initial, with an extraction restriction: only the
"pivot" — the voice-determined, clause-peripheral argument — can undergo
Ā-movement. Analyses of the restriction live in the studies that propose
them ([cole-hermon-2008], [erlewine-2018]).

## Voice System

Unlike Philippine-type Austronesian languages (Tagalog, Seediq), Toba
Batak does not have a full voice/Case system with multiple voices. Two
voice prefixes determine which argument is the pivot (= subject):

- **Actor Voice (AV)**, *mang-*: agent is the pivot
- **Object Voice (OV)**, *di-*: patient/theme is the pivot

-/

open Extraction (ExtractionTarget ExtractionMarkingStrategy)

namespace TobaBatak

-- ============================================================================
-- § 1: Voice
-- ============================================================================

/-- Toba Batak voice: determines which argument is the pivot. -/
inductive Voice where
  /-- Actor voice: the agent is the pivot (clause-final) -/
  | av
  /-- Object voice: the patient/theme is the pivot -/
  | ov
  deriving Repr, DecidableEq

/-- Which argument role is the pivot for a given voice? -/
def Voice.pivotRole : Voice → ThetaRole
  | .av => .agent
  | .ov => .patient

/-- The voice prefix, *mang-* (with its phonologically conditioned variants) or *di-*. -/
def Voice.affix : Voice → String
  | .av => "mang-"
  | .ov => "di-"

-- ============================================================================
-- § 2: Extraction Judgment
-- ============================================================================

/-- Whether extraction of a given argument is grammatical. -/
inductive ExtractionJudgment where
  | grammatical
  | ungrammatical
  deriving Repr, DecidableEq

-- ============================================================================
-- § 3: Extraction Data Type
-- ============================================================================

/-- A Toba Batak extraction datum: voice choice + extracted element + judgment. -/
structure ExtractionDatum where
  /-- Which voice the clause is in -/
  voice : Voice
  /-- What is being extracted (DP argument or adjunct) -/
  extracted : Extraction.Extractee
  /-- Whether the extraction is grammatical -/
  judgment : ExtractionJudgment
  /-- Description -/
  description : String := ""
  deriving Repr

/-- Is the extracted element the pivot for the given voice?
    Adjuncts are never pivots (they don't participate in Case licensing). -/
def ExtractionDatum.extractsPivot (d : ExtractionDatum) : Bool :=
  match d.extracted with
  | .dpArg role => role == d.voice.pivotRole
  | .adjunct => false

-- ============================================================================
-- § 4: Monoclausal Data ([erlewine-2018], §2)
-- ============================================================================

/-- AV + agent extraction: grammatical (agent is pivot in AV). -/
def avAgentExtraction : ExtractionDatum :=
  { voice := .av, extracted := .dpArg .agent, judgment := .grammatical
    description := "AV + agent (pivot): 'Ise man-uhor buku i?' (Who bought the book?) [= (1a)/(7a)]" }

/-- AV + patient extraction: ungrammatical (patient is not pivot in AV). -/
def avPatientExtraction : ExtractionDatum :=
  { voice := .av, extracted := .dpArg .patient, judgment := .ungrammatical
    description := "AV + patient (non-pivot): *'Aha man-uhor si Poltak?' (*What did Poltak buy?) [= (1a)/(8a)]" }

/-- OV + patient extraction: grammatical (patient is pivot in OV). -/
def ovPatientExtraction : ExtractionDatum :=
  { voice := .ov, extracted := .dpArg .patient, judgment := .grammatical
    description := "OV + patient (pivot): 'Aha di-tuhor si Poltak?' (What did Poltak buy?) [= (2b)/(8b)]" }

/-- OV + agent extraction: ungrammatical (agent is not pivot in OV). -/
def ovAgentExtraction : ExtractionDatum :=
  { voice := .ov, extracted := .dpArg .agent, judgment := .ungrammatical
    description := "OV + agent (non-pivot): *'Ise di-tuhor buku i?' (*Who bought the book?) [= (7b)]" }

/-- AV + adjunct extraction: grammatical (adjuncts don't need Case). -/
def avAdjunctExtraction : ExtractionDatum :=
  { voice := .av, extracted := .adjunct, judgment := .grammatical
    description := "AV + adjunct: 'Andigan si Poltak man-uhor buku?' (When did Poltak buy a book?) [= (1b)]" }

/-- OV + adjunct extraction: grammatical (adjuncts don't need Case). -/
def ovAdjunctExtraction : ExtractionDatum :=
  { voice := .ov, extracted := .adjunct, judgment := .grammatical
    description := "OV + adjunct: non-DP extraction unrestricted regardless of voice [= (9)/(35)]" }

/-- All monoclausal extraction data. -/
def extractionData : List ExtractionDatum :=
  [ avAgentExtraction, avPatientExtraction
  , ovPatientExtraction, ovAgentExtraction
  , avAdjunctExtraction, ovAdjunctExtraction ]

-- ============================================================================
-- § 5: Extraction Marking
-- ============================================================================

namespace Extraction

/-- Reflex hosts for Toba Batak extraction marking. -/
inductive Site where
  | verb
  deriving DecidableEq, Repr

/-- Only the pivot (= surface subject) can be extracted; the AV vs OV
    voice alternation on the verb determines which thematic role
    occupies the pivot, so subject extraction is marked by the verb's
    voice form. -/
def realize : ExtractionTarget → List (Features.Reflex Site)
  | .subject => [.morpheme .verb]
  | _ => []

/-- WALS-style label: voice alternation marks extraction. -/
def strategy : ExtractionMarkingStrategy := .voiceAlternation

end Extraction

-- ============================================================================
-- § 6: Voice System
-- ============================================================================

namespace VoiceSystem

/-! Toba Batak voice system: two-way symmetrical (AV/OV).

    Unlike Philippine-type languages (Tagalog: 4+ voices including
    locative, instrumental), Toba Batak has only actor and object
    voice. The system is symmetrical — neither voice is morphologically
    basic.

    Language: "Toba Batak".
    Notes: Two-way symmetrical system ([erlewine-2018]). -/

/-- The voices of the Toba Batak system. -/
def voices : List _root_.Voice.VoiceEntry :=
  [ ⟨"Actor Voice", .agent⟩, ⟨"Object Voice", .patient⟩ ]

/-- System symmetry: symmetrical (neither voice is morphologically basic). -/
def symmetry : _root_.Voice.VoiceSystemSymmetry := .symmetrical

end VoiceSystem

theorem tb_voice_system_symmetrical :
    VoiceSystem.symmetry = .symmetrical := rfl

theorem tb_voice_count :
    _root_.Voice.voiceCount VoiceSystem.voices = 2 := rfl

theorem tb_is_active_passive :
    _root_.Voice.isActivePassive VoiceSystem.voices := by decide

theorem tb_promotes_agent :
    _root_.Voice.promotesRole VoiceSystem.voices .agent := by decide

end TobaBatak
