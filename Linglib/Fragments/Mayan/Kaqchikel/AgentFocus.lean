import Linglib.Syntax.Extraction
import Linglib.Syntax.Voice.Basic

/-!
# Kaqchikel Agent Focus Fragment [erlewine-2016]

Theory-neutral typological data for Agent Focus (AF) in Kaqchikel
(K'ichean, Mayan): verb-form types, the empirical extraction
profile, and the typological AF/extraction-gap classification.

The theory-laden apparatus that interprets this data lives in study
files per the project Fragment-discipline rule (CLAUDE.md):
- OT competing-derivations + SSAL/XRef constraints + ranking →
  `Studies/Erlewine2016.lean`
- Minimalist Voice/ClauseSpine for Kaqchikel →
  `Studies/CoonMateoPedroPreminger2014.lean`

## The Paradigm

| Extracted arg      | Verb form | Agreement     |
|--------------------|-----------|---------------|
| None (declarative) | Transitive| Set A + Set B |
| Patient/Abs        | Transitive| Set A + Set B |
| Agent/Erg (local)  | AF (*-Vn*)| Set B only    |
| Agent/Erg (long)   | Transitive| Set A + Set B |

AF is obligatory for clause-local agent extraction and ungrammatical
for patient extraction or long-distance agent extraction — it is not a
free alternation but a locality-sensitive, structurally conditioned
repair. The structural analysis (SSAL ≫ XRef OT competition) lives in
the Erlewine2016 study file.

-/

namespace Kaqchikel

-- ============================================================================
-- § 1: Morphological Forms
-- ============================================================================

/-- Verbal morphology in a Kaqchikel clause: either the normal transitive
    form (with Set A ergative agreement) or Agent Focus (with *-Vn* and
    no Set A). -/
inductive VerbForm where
  /-- Normal transitive: Set A (erg) + Set B (abs) agreement. -/
  | transitive
  /-- Agent Focus: suffix *-Vn*, Set B only, no Set A (erg). -/
  | agentFocus
  deriving DecidableEq, Repr

/-- Does this verb form bear ergative (Set A) agreement? -/
def VerbForm.hasSetA : VerbForm → Bool
  | .transitive => true
  | .agentFocus => false

/-- Does this verb form bear the AF suffix *-Vn*? -/
def VerbForm.hasAFSuffix : VerbForm → Bool
  | .transitive => false
  | .agentFocus => true

-- ============================================================================
-- § 2: Extraction Data
-- ============================================================================

/-- An extraction datum: which argument is extracted and which verb form
    surfaces. -/
structure ExtractionDatum where
  extracted : Extraction.ArgumentRole
  verbForm : VerbForm
  judgment : Extraction.ExtractionMarkingStrategy
  deriving Repr

/-- Agent extraction (clause-local) requires AF. -/
def agentExtractionAF : ExtractionDatum :=
  { extracted := .agent
  , verbForm := .agentFocus
  , judgment := .dedicatedMorpheme }

/-- Agent extraction with normal transitive (clause-local) is ungrammatical. -/
def agentExtractionTrans : ExtractionDatum :=
  { extracted := .agent
  , verbForm := .transitive
  , judgment := .dedicatedMorpheme }

/-- Patient extraction uses normal transitive. -/
def patientExtractionTrans : ExtractionDatum :=
  { extracted := .patient
  , verbForm := .transitive
  , judgment := .unmarked }  -- no special morphology needed

/-- Long-distance agent extraction uses normal transitive, NOT AF.
    When the agent extracts from an embedded clause, it passes through
    intermediate Spec,CP positions via successive-cyclic movement. Each
    step crosses enough structure to satisfy SSAL — the too-local
    Spec,TP → Spec,CP step within the embedded clause is avoided.

    This is the key evidence that AF is triggered by *locality of
    movement*, not simply by agent extraction ([erlewine-2016] §2.3,
    examples 21–22). -/
def longDistanceAgentExtraction : ExtractionDatum :=
  { extracted := .agent
  , verbForm := .transitive
  , judgment := .unmarked }

-- ============================================================================
-- § 3: Extraction Profile
-- ============================================================================

/-- Kaqchikel's extraction data: agent focus alternation
    (`extractionStrategy = .dedicatedMorpheme`, marking subject extraction).
    AF (*-Vn*) is obligatory for clause-local agent extraction
    ([erlewine-2016]). -/
def extractionStrategy : Extraction.ExtractionMarkingStrategy := .dedicatedMorpheme
def extractionMarkedPositions : List Extraction.ExtractionTarget := [.subject]
def extractionDistinguishesPosition : Bool := true

-- ============================================================================
-- § 4: Mayan AF Typology ([erlewine-2016] §6.1)
-- ============================================================================

/-- Mayan languages vary in whether AF is available, depending on the
    ranking of SSAL vs XRef. This produces a two-way typological split:

    - **AF languages**: SSAL >> XRef. Anti-locality violation is repaired
      by switching to AF morphology. E.g., Kaqchikel, Q'anjob'al.
    - **Extraction-gap languages**: XRef >> SSAL. No AF repair available;
      clause-local agent extraction is simply ungrammatical. E.g., Chol.

    Both types share the same underlying problem (SSAL blocks clause-local
    agent extraction); they differ only in whether the grammar provides
    a repair strategy. -/
inductive MayanAFType where
  /-- SSAL >> XRef: AF available as repair for anti-locality. -/
  | afLanguage
  /-- XRef >> SSAL: no repair; extraction gap. -/
  | extractionGap
  deriving DecidableEq, Repr

/-- Kaqchikel is an AF language (SSAL >> XRef). -/
def kaqAFType : MayanAFType := .afLanguage

-- ============================================================================
-- § 5: Verb Form Verification
-- ============================================================================

/-- AF does not bear Set A (ergative) agreement. -/
theorem af_no_set_a : VerbForm.agentFocus.hasSetA = false := rfl

/-- Normal transitive does bear Set A agreement. -/
theorem trans_has_set_a : VerbForm.transitive.hasSetA = true := rfl

/-- AF bears the *-Vn* suffix. -/
theorem af_has_suffix : VerbForm.agentFocus.hasAFSuffix = true := rfl

-- ============================================================================
-- § 6: Voice System
-- ============================================================================

namespace VoiceSystem

/-! Kaqchikel voice system: two-way asymmetrical (transitive/AF).

    Not a true pivot system — AF is a locality-sensitive repair for
    clause-local agent extraction, not a symmetric voice alternation.
    Transitive is the basic form; AF is derived (triggered by SSAL).

    Language: "Kaqchikel".
    Notes: AF is locality-sensitive repair, not symmetric pivot (Erlewine 2016). -/

/-- The voices of the Kaqchikel system. -/
def voices : List Voice.VoiceEntry :=
  [ ⟨"Transitive", .agent⟩, ⟨"Agent Focus", .agent⟩ ]

/-- System symmetry: asymmetrical (transitive is the basic form). -/
def symmetry : Voice.VoiceSystemSymmetry := .asymmetrical

end VoiceSystem

theorem kaq_voice_system_asymmetrical :
    VoiceSystem.symmetry = .asymmetrical := rfl

theorem kaq_voice_count :
    Voice.voiceCount VoiceSystem.voices = 2 := rfl

/-- Both Kaqchikel voices promote agent — AF is not a patient-promoting
    voice but an alternative agent-extracting structure. -/
theorem kaq_both_promote_agent :
    VoiceSystem.voices.all (·.promotes == .agent) = true := rfl

/-- Kaqchikel is NOT an active/passive system: it lacks a
    patient-promoting voice. -/
theorem kaq_not_active_passive :
    ¬ Voice.isActivePassive VoiceSystem.voices := by decide

end Kaqchikel
