import Linglib.Theories.Interfaces.Morphosyntax.Extraction
import Linglib.Phenomena.ArgumentStructure.VoiceSystem

/-!
# Kaqchikel Agent Focus Fragment @cite{erlewine-2016}

Theory-neutral typological data for Agent Focus (AF) in Kaqchikel
(K'ichean, Mayan): verb-form types, the empirical extraction
profile, and the typological AF/extraction-gap classification.

The theory-laden apparatus that interprets this data lives in study
files per the project Fragment-discipline rule (CLAUDE.md):
- OT competing-derivations + SSAL/XRef constraints + ranking →
  `Phenomena/FillerGap/Studies/Erlewine2016.lean`
- Minimalist Voice/ClauseSpine for Kaqchikel →
  `Phenomena/Ergativity/Studies/CoonMateoPedroPreminger2014.lean`

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

namespace Fragments.Mayan.Kaqchikel

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
  extracted : Interfaces.ArgumentRole
  verbForm : VerbForm
  judgment : Interfaces.ExtractionMarkingStrategy
  deriving Repr

/-- Agent extraction (clause-local) requires AF. -/
def agentExtractionAF : ExtractionDatum :=
  { extracted := .agent
  , verbForm := .agentFocus
  , judgment := .agentFocusAlternation }

/-- Agent extraction with normal transitive (clause-local) is ungrammatical. -/
def agentExtractionTrans : ExtractionDatum :=
  { extracted := .agent
  , verbForm := .transitive
  , judgment := .agentFocusAlternation }

/-- Patient extraction uses normal transitive. -/
def patientExtractionTrans : ExtractionDatum :=
  { extracted := .patient
  , verbForm := .transitive
  , judgment := .none }  -- no special morphology needed

/-- Long-distance agent extraction uses normal transitive, NOT AF.
    When the agent extracts from an embedded clause, it passes through
    intermediate Spec,CP positions via successive-cyclic movement. Each
    step crosses enough structure to satisfy SSAL — the too-local
    Spec,TP → Spec,CP step within the embedded clause is avoided.

    This is the key evidence that AF is triggered by *locality of
    movement*, not simply by agent extraction (@cite{erlewine-2016} §2.3,
    examples 21–22). -/
def longDistanceAgentExtraction : ExtractionDatum :=
  { extracted := .agent
  , verbForm := .transitive
  , judgment := .none }

-- ============================================================================
-- § 3: Extraction Profile
-- ============================================================================

/-- Kaqchikel's extraction morphology profile: agent focus alternation. -/
def kaqExtractionProfile : Interfaces.ExtractionProfile :=
  { language := "Kaqchikel"
  , strategy := .agentFocusAlternation
  , markedPositions := [.subject]
  , distinguishesPosition := true
  , notes := "AF (*-Vn*) obligatory for clause-local agent extraction; Erlewine 2016" }

-- ============================================================================
-- § 4: Mayan AF Typology (@cite{erlewine-2016} §6.1)
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
-- § 6: Voice System Profile
-- ============================================================================

/-- Kaqchikel voice system: two-way asymmetrical (transitive/AF).

    Not a true pivot system — AF is a locality-sensitive repair for
    clause-local agent extraction, not a symmetric voice alternation.
    Transitive is the basic form; AF is derived (triggered by SSAL). -/
def kaqVoiceSystem : Interfaces.VoiceSystemProfile :=
  { language := "Kaqchikel"
    voices := [ ⟨"Transitive", .agent⟩, ⟨"Agent Focus", .agent⟩ ]
    symmetry := .asymmetrical
    notes := "AF is locality-sensitive repair, not symmetric pivot (Erlewine 2016)" }

theorem kaq_voice_system_asymmetrical :
    kaqVoiceSystem.symmetry = .asymmetrical := rfl

theorem kaq_voice_count :
    kaqVoiceSystem.voiceCount = 2 := rfl

/-- Both Kaqchikel voices promote agent — AF is not a patient-promoting
    voice but an alternative agent-extracting structure. -/
theorem kaq_both_promote_agent :
    kaqVoiceSystem.voices.all (·.promotes == .agent) = true := rfl

/-- Kaqchikel is NOT an active/passive system: it lacks a
    patient-promoting voice. -/
theorem kaq_not_active_passive :
    ¬ kaqVoiceSystem.isActivePassive := by decide

end Fragments.Mayan.Kaqchikel
