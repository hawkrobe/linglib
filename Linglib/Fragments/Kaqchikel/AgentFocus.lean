import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Syntax.Minimalism.Core.ClauseSpine
import Linglib.Core.Logic.ConstraintEvaluation
import Linglib.Core.Interfaces.ExtractionMorphology
import Linglib.Core.Interfaces.VoiceSystem

/-!
# Kaqchikel Agent Focus Fragment @cite{erlewine-2016}

Empirical data and Minimalist infrastructure for Agent Focus (AF) in
Kaqchikel, a K'ichean (Mayan) language. When the transitive agent is
Ā-extracted clause-locally, the verb obligatorily appears in a special
AF form: Set A (ergative) agreement is lost and the suffix *-Vn* appears.

## The Paradigm

| Extracted arg      | Verb form | Agreement     |
|--------------------|-----------|---------------|
| None (declarative) | Transitive| Set A + Set B |
| Patient/Abs        | Transitive| Set A + Set B |
| Agent/Erg (local)  | AF (*-Vn*)| Set B only    |
| Agent/Erg (long)   | Transitive| Set A + Set B |

AF is obligatory for clause-local agent extraction and ungrammatical
for patient extraction or long-distance agent extraction — it is not a
free alternation but a locality-sensitive, structurally conditioned repair.

## Clause Structures

Both derivations share the same clausal spine (CP > TP > vP > VP). The
difference is in the v head and the agent's movement path:

1. **Normal transitive**: Transitive v introduces agent in Spec,vP.
   A-probe on T attracts agent to Spec,TP, establishing Set A (ergative)
   agreement. For Ā-extraction, agent must then move from Spec,TP to
   Spec,CP — but this violates SSAL because CP immediately dominates TP.

2. **AF structure**: Intransitive-like v does NOT introduce agent in
   Spec,vP. Agent extracts directly to Spec,CP without passing through
   Spec,TP. This satisfies SSAL (no too-local step), but skipping
   Spec,TP means no A-agreement — hence no Set A, and AF morphology
   (*-Vn*) surfaces.

The grammar selects AF as optimal via OT competition (§5):
SSAL >> XRef means avoiding the too-local movement outranks maintaining
cross-referencing agreement.

-/

namespace Fragments.Kaqchikel

open Minimalism Core.ConstraintEvaluation

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
  deriving DecidableEq, BEq, Repr

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
    movement*, not simply by agent extraction (@cite{erlewine-2016}, §2.3,
    examples 21–22). -/
def longDistanceAgentExtraction : ExtractionDatum :=
  { extracted := .agent
  , verbForm := .transitive
  , judgment := .none }

-- ============================================================================
-- § 3: Clause Structure — Competing Derivations
-- ============================================================================

/-- A candidate derivation for clause-local transitive agent extraction.

    The OT competition evaluates these: which structure best satisfies
    the ranked constraints? Both candidates share the same clausal spine
    (CP > TP > vP > VP); they differ in the v head and the agent's
    movement path. -/
inductive AFCandidate where
  /-- Normal transitive derivation: transitive v introduces agent in
      Spec,vP. A-probe on T attracts agent to Spec,TP (triggering Set A
      agreement). Subsequent Ā-extraction from Spec,TP to Spec,CP
      violates SSAL because CP immediately dominates TP. -/
  | transitiveExtraction
  /-- Agent Focus derivation: intransitive-like v, agent NOT in Spec,vP.
      Agent extracts directly to Spec,CP without passing through Spec,TP.
      No SSAL violation, but cross-referencing is incomplete: no Set A
      (ergative) agreement because the agent never enters Spec,TP. -/
  | agentFocusExtraction
  deriving DecidableEq, BEq, Repr

/-- The verb form that surfaces for each candidate. -/
def AFCandidate.verbForm : AFCandidate → VerbForm
  | .transitiveExtraction => .transitive
  | .agentFocusExtraction => .agentFocus

/-- Does this candidate violate Spec-to-Spec Anti-Locality (SSAL)?
    The transitive derivation does: the step Spec,TP → Spec,CP crosses
    no intervening maximal projection (CP immediately dominates TP). -/
def AFCandidate.violatesAntiLocality : AFCandidate → Bool
  | .transitiveExtraction => true
  | .agentFocusExtraction => false

/-- Does this candidate violate the XRef (cross-referencing) constraint?
    AF loses Set A agreement because the agent never enters Spec,TP
    where the A-probe resides. The transitive candidate maintains full
    cross-referencing (Set A + Set B). -/
def AFCandidate.violatesXRef : AFCandidate → Bool
  | .transitiveExtraction => false
  | .agentFocusExtraction => true

-- ============================================================================
-- § 4: OT Constraint Ranking
-- ============================================================================

/-- Constraints for Kaqchikel AF, ranked from highest to lowest:

    1. **SSAL** (highest): Spec-to-Spec Anti-Locality. Movement from
       Spec,XP to Spec,YP is banned when YP immediately dominates XP.
    2. **XRef** (lower): Cross-referencing agreement. Every argument
       DP must be cross-referenced by a pronominal morpheme on the verb
       (Set A for ergative, Set B for absolutive).

    SSAL dominates XRef: it is better to lose agreement (AF) than to
    violate anti-locality (crash). -/
inductive AFConstraint where
  | antiLocality  -- Highest: Spec-to-Spec Anti-Locality (SSAL)
  | xref          -- Lower: cross-referencing agreement
  deriving DecidableEq, BEq, Repr

/-- Violation profile for each candidate.

    Position 0 = highest-ranked constraint (SSAL / AntiLocality).
    Position 1 = lower-ranked constraint (XRef).

    - Transitive extraction: [1, 0] — violates SSAL, satisfies XRef
    - AF extraction: [0, 1] — satisfies SSAL, violates XRef -/
def AFCandidate.violations : AFCandidate → List Nat
  | .transitiveExtraction => [1, 0]
  | .agentFocusExtraction => [0, 1]

/-- The OT tableau for Kaqchikel clause-local agent extraction. -/
def agentExtractionTableau : OTTableau AFCandidate :=
  { candidates := [.transitiveExtraction, .agentFocusExtraction]
  , profile := AFCandidate.violations
  , nonempty := by decide }

-- ============================================================================
-- § 5: Clause Spine and Voice
-- ============================================================================

/-- Both the transitive and AF derivations project the same clausal spine
    (CP > TP > vP > VP). The difference is in the v head: transitive v
    introduces the agent in Spec,vP; AF v does not. -/
def kaqClauseSpine : ClauseSpine := ClauseSpine.cP

/-- Kaqchikel agentive Voice/v head (parallel to Mam's Voice). Present
    in the transitive derivation; absent or altered in AF. -/
def kaqVoice : VoiceHead :=
  { flavor := .agentive
  , hasD := true
  , phaseHead := true }

-- ============================================================================
-- § 6: Extraction Profile
-- ============================================================================

/-- Kaqchikel's extraction morphology profile: agent focus alternation. -/
def kaqExtractionProfile : Interfaces.ExtractionProfile :=
  { language := "Kaqchikel"
  , strategy := .agentFocusAlternation
  , markedPositions := [.subject]
  , distinguishesPosition := true
  , notes := "AF (*-Vn*) obligatory for clause-local agent extraction; Erlewine 2016" }

-- ============================================================================
-- § 7: Mayan AF Typology (@cite{erlewine-2016}, §6.1)
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
  deriving DecidableEq, BEq, Repr

/-- Kaqchikel is an AF language (SSAL >> XRef). -/
def kaqAFType : MayanAFType := .afLanguage

-- ============================================================================
-- § 8: Verification Theorems
-- ============================================================================

/-- AF does not bear Set A (ergative) agreement. -/
theorem af_no_set_a : VerbForm.agentFocus.hasSetA = false := rfl

/-- Normal transitive does bear Set A agreement. -/
theorem trans_has_set_a : VerbForm.transitive.hasSetA = true := rfl

/-- AF bears the *-Vn* suffix. -/
theorem af_has_suffix : VerbForm.agentFocus.hasAFSuffix = true := rfl

/-- The two candidates have different violation profiles. -/
theorem candidates_differ :
    AFCandidate.transitiveExtraction.violations ≠
    AFCandidate.agentFocusExtraction.violations := by decide

/-- The transitive derivation violates SSAL. -/
theorem trans_violates_antilocality :
    AFCandidate.transitiveExtraction.violatesAntiLocality = true := rfl

/-- The AF derivation does NOT violate SSAL. -/
theorem af_obeys_antilocality :
    AFCandidate.agentFocusExtraction.violatesAntiLocality = false := rfl

/-- AF is lexicographically optimal: it satisfies the higher-ranked
    constraint (SSAL) at the cost of the lower-ranked one (XRef).
    This is the central result of @cite{erlewine-2016}. -/
theorem af_is_optimal :
    agentExtractionTableau.optimal = [.agentFocusExtraction] := by
  native_decide

/-- Under satisfaction ordering (subset inclusion), the two candidates
    would be incomparable — each satisfies a constraint the other violates.
    OT's strict ranking is what breaks the tie in favor of AF. -/
theorem satisfaction_ordering_incomparable :
    agentExtractionTableau.satOptimal = [] := by
  native_decide

/-- Kaqchikel clause projects Voice. -/
theorem kaq_has_voice :
    kaqClauseSpine.projects .Voice = true := by native_decide

/-- Kaqchikel Voice is agentive and a phase head. -/
theorem kaq_voice_is_agentive : kaqVoice.flavor = .agentive := rfl

/-- AF is locality-sensitive: clause-local agent extraction triggers AF,
    but long-distance agent extraction does NOT.
    The paper's deepest empirical claim: AF is about the *locality of
    movement*, not about agent extraction per se. -/
theorem af_locality_sensitive :
    agentExtractionAF.verbForm = .agentFocus ∧
    longDistanceAgentExtraction.verbForm = .transitive := ⟨rfl, rfl⟩

-- ============================================================================
-- § 9: Voice System Profile
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
    kaqVoiceSystem.isActivePassive = false := rfl

end Fragments.Kaqchikel
