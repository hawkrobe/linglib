import Linglib.Theories.Interfaces.Morphosyntax.Extraction
import Linglib.Phenomena.ArgumentStructure.VoiceSystem

/-!
# Toba Batak Fragment @cite{erlewine-2018}

Morphosyntactic data for Toba Batak (Austronesian, Sumatra) relevant
to the extraction restriction and pivot system.

Toba Batak has predicate-initial word order (derived by predicate
fronting) and an extraction restriction: only the "pivot" — the
voice-determined, clause-peripheral argument — can undergo Ā-movement.

## Voice System

Unlike Philippine-type Austronesian languages (Tagalog, Seediq), Toba
Batak does not have a full voice/Case system with multiple voices. Two
voice morphemes determine which argument is the pivot (= subject):

- **Actor Voice (AV)**: agent is the pivot
- **Object Voice (OV)**: patient/theme is the pivot

The restriction on extraction follows from nominal licensing: only the
pivot (Case-licensed by T's [PROBE:D] in Spec,TP) can undergo
Ā-movement; a non-pivot DP fronted to Spec,CP would lack a Case
licensor. This is NOT a voice-as-Case system in
the Philippine sense; it is a structural consequence of how probing
and Case assignment interact with predicate fronting.

-/

namespace Fragments.TobaBatak

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
def Voice.pivotRole : Voice → Interfaces.ArgumentRole
  | .av => .agent
  | .ov => .patient

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
  extracted : Interfaces.Extractee
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
-- § 4: Monoclausal Data (@cite{erlewine-2018}, §2)
-- ============================================================================

/-- AV + agent extraction: grammatical (agent is pivot in AV). -/
def avAgentExtraction : ExtractionDatum :=
  { voice := .av, extracted := .dpArg .agent, judgment := .grammatical
    description := "AV + agent (pivot): 'Ise man-uhor buku i?' (Who bought the book?) [= (1a)/(7a)]" }

/-- AV + patient extraction: ungrammatical (patient is not pivot in AV). -/
def avPatientExtraction : ExtractionDatum :=
  { voice := .av, extracted := .dpArg .patient, judgment := .ungrammatical
    description := "AV + patient (non-pivot): *'Aha man-uhor si Poltak?' (*What did Poltak buy?) [= (1a)/(8a)]" }

/-- AV + oblique extraction: ungrammatical (oblique is never pivot). -/
def avObliqueExtraction : ExtractionDatum :=
  { voice := .av, extracted := .dpArg .oblique, judgment := .ungrammatical
    description := "AV + oblique (non-pivot) [predicted, not directly tested in §2]" }

/-- OV + patient extraction: grammatical (patient is pivot in OV). -/
def ovPatientExtraction : ExtractionDatum :=
  { voice := .ov, extracted := .dpArg .patient, judgment := .grammatical
    description := "OV + patient (pivot): 'Aha di-tuhor si Poltak?' (What did Poltak buy?) [= (2b)/(8b)]" }

/-- OV + agent extraction: ungrammatical (agent is not pivot in OV). -/
def ovAgentExtraction : ExtractionDatum :=
  { voice := .ov, extracted := .dpArg .agent, judgment := .ungrammatical
    description := "OV + agent (non-pivot): *'Ise di-tuhor buku i?' (*Who bought the book?) [= (7b)]" }

/-- OV + oblique extraction: ungrammatical (oblique is never pivot). -/
def ovObliqueExtraction : ExtractionDatum :=
  { voice := .ov, extracted := .dpArg .oblique, judgment := .ungrammatical
    description := "OV + oblique (non-pivot) [predicted, not directly tested in §2]" }

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
  [ avAgentExtraction, avPatientExtraction, avObliqueExtraction
  , ovPatientExtraction, ovAgentExtraction, ovObliqueExtraction
  , avAdjunctExtraction, ovAdjunctExtraction ]

-- ============================================================================
-- § 5: Extraction Profile
-- ============================================================================

/-- Toba Batak extraction profile: structural restriction (pivot-only). -/
def tbExtractionProfile : Interfaces.ExtractionProfile :=
  { language := "Toba Batak"
    strategy := .structuralRestriction
    markedPositions := [.subject]
    distinguishesPosition := true
    notes := "Only the pivot (= surface subject) can be extracted; " ++
             "voice alternation (AV/OV) determines which thematic " ++
             "role occupies the pivot, but the extractable structural " ++
             "position is always subject. Restriction derived from " ++
             "predicate fronting + nominal licensing: non-pivot DPs " ++
             "in Spec,CP lack a Case licensor (@cite{erlewine-2018}, §4)" }

-- ============================================================================
-- § 6: Voice System Profile
-- ============================================================================

/-- Toba Batak voice system: two-way symmetrical (AV/OV).

    Unlike Philippine-type languages (Tagalog: 4+ voices including
    locative, instrumental), Toba Batak has only actor and object
    voice. The system is symmetrical — neither voice is morphologically
    basic. -/
def tbVoiceSystem : Interfaces.VoiceSystemProfile :=
  { language := "Toba Batak"
    voices := [ ⟨"Actor Voice", .agent⟩, ⟨"Object Voice", .patient⟩ ]
    symmetry := .symmetrical
    notes := "Two-way symmetrical system (@cite{erlewine-2018})" }

theorem tb_voice_system_symmetrical :
    tbVoiceSystem.symmetry = .symmetrical := rfl

theorem tb_voice_count :
    tbVoiceSystem.voiceCount = 2 := rfl

theorem tb_is_active_passive :
    tbVoiceSystem.isActivePassive := by decide

theorem tb_promotes_agent :
    tbVoiceSystem.promotesRole .agent := by decide

end Fragments.TobaBatak
