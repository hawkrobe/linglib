import Linglib.Fragments.Mayan.Tseltalan
import Linglib.Theories.Morphology.DM.NominalStructure
import Linglib.Core.SpecificityCondition
import Linglib.Core.Discourse.InformationStructure

/-!
# Aissen & Polian 2025: Possessor Extraction and Categorical Subject in Tseltalan
@cite{aissen-polian-2025}

*Natural Language & Linguistic Theory* 43:63--113.

## Overview

Tseltalan languages (Tsotsil, Tseltal) have two possessor extraction
strategies — pied-piping and stranding — whose availability depends on
nominal size (= specificity). Specific nominals project to DP and are
opaque to Ā-subextraction (selective opacity, @cite{keine-2019}); only
pied-piping of the whole DP is possible. Non-specific nominals project
only to nP/PossP and are transparent; possessor stranding (raising to
an A-position, then Ā-movement) is possible.

Stranding is further constrained by intervention: an A-positioned DP
(agent or S_A) between the possessor and T°'s EPP:D probe blocks
possessor raising. This correctly predicts that stranding is available
in unaccusative clauses but blocked in transitive and unergative clauses.

The paper also identifies three construction types exhibiting ψ-subjects
(categorical judgment subjects in Spec,TP, @cite{kuroda-1972}):
predicative possession, experiential collocations, and lexical
unaccusatives. ψ-subjects are always cross-referenced by Set B
(absolutive), regardless of transitivity.

## Key Claims Formalized

1. Possessor extraction always produces external possessors (§3)
2. Pied-piping ↔ specific nominals; stranding ↔ non-specific (§3.2)
3. Table 4 intervention paradigm derived from clause type × extraction mode
4. ψ-subjects receive Set B agreement (§5)
5. All ψ-subject constructions are structurally unaccusative

## Integration Points

- `NominalPosition` / `PossessionType` from `NominalStructure.lean`
- `SpecificityCondition` from `Core/SpecificityCondition.lean`
- `JudgmentType` from `Core/Discourse/InformationStructure.lean`
- `GramFunction` / `ClauseType` from `Fragments/Mayan/Tseltalan.lean`
-/

namespace Phenomena.Possession.Studies.AissenPolian2025

open Fragments.Mayan (MarkerSet)
open Fragments.Mayan.Tseltalan
open Theories.Morphology.DM

-- ============================================================================
-- § 1: Nominal Size and Specificity
-- ============================================================================

/-- Nominal projections in Tseltalan, determining extractability.
    @cite{aissen-polian-2025} §3.2: specific indefinites and definites
    project to DP; non-specific indefinites project only to nP or PossP.

    Derived from the nominal spine in `NominalStructure.lean`:
    √ROOT < n < (Poss) < D. -/
inductive NominalSize where
  | dp    -- projects to D: specific nominals
  | possP -- projects to PossP: non-specific with alienable possessor
  | nP    -- projects to nP: non-specific with inalienable possessor
  deriving DecidableEq, Repr

/-- Map nominal size to the highest `NominalPosition` in the projection. -/
def NominalSize.highestPosition : NominalSize → NominalPosition
  | .dp    => .d
  | .possP => .specPoss
  | .nP    => .specN

/-- Specific nominals project to DP; non-specific nominals do not.
    @cite{aissen-polian-2025} §3.2. -/
def NominalSize.isSpecific : NominalSize → Bool
  | .dp    => true
  | .possP => false
  | .nP    => false

-- ============================================================================
-- § 2: Nominal Opacity (Selective Opacity, @cite{keine-2019})
-- ============================================================================

/-- DPs are opaque to Ā-subextraction: movement cannot extract from
    within a DP. Only elements at the DP edge or the whole DP can move.
    Non-DP nominals (nP, PossP) are transparent — possessors at their
    edge can raise out.

    This is @cite{keine-2019}'s selective opacity applied to the
    nominal domain. -/
def nominalOpaque (size : NominalSize) : Bool :=
  size == .dp

theorem nP_transparent : nominalOpaque .nP = false := rfl
theorem possP_transparent : nominalOpaque .possP = false := rfl
theorem dp_opaque : nominalOpaque .dp = true := rfl

-- ============================================================================
-- § 3: Extraction Modes
-- ============================================================================

/-- Two possessor extraction strategies in Tseltalan.
    @cite{aissen-polian-2025} §3. -/
inductive ExtractionMode where
  /-- Pied-piping: the entire nominal (including possessor) moves to
      Spec,CP. The possessor stays nominal-internal. -/
  | piedPiping
  /-- Stranding: the possessor raises out of the nominal to an
      A-position (Spec,ApplP or Spec,VoiceP), then undergoes
      Ā-movement from there. The remnant nominal stays in situ. -/
  | stranding
  deriving DecidableEq, Repr

/-- Whether a given extraction mode is available for a nominal of
    given size.

    - Pied-piping moves the whole DP — requires D projection (specific).
    - Stranding raises the possessor out — requires nominal transparency
      (non-specific, i.e., not a full DP).

    @cite{aissen-polian-2025} §3.2. -/
def extractionAvailable (mode : ExtractionMode) (size : NominalSize) : Bool :=
  match mode with
  | .piedPiping => size == .dp
  | .stranding  => !nominalOpaque size

/-- Pied-piping requires specificity (D projection). -/
theorem piedPiping_requires_specific :
    extractionAvailable .piedPiping .dp = true ∧
    extractionAvailable .piedPiping .possP = false ∧
    extractionAvailable .piedPiping .nP = false := ⟨rfl, rfl, rfl⟩

/-- Stranding requires non-specificity (nominal transparency). -/
theorem stranding_requires_nonspecific :
    extractionAvailable .stranding .dp = false ∧
    extractionAvailable .stranding .possP = true ∧
    extractionAvailable .stranding .nP = true := ⟨rfl, rfl, rfl⟩

/-- Every nominal size admits at least one extraction mode.
    Possessor extraction is never fully blocked — the available
    strategy depends on specificity. -/
theorem extraction_always_possible (size : NominalSize) :
    extractionAvailable .piedPiping size = true ∨
    extractionAvailable .stranding size = true := by
  cases size <;> simp [extractionAvailable, nominalOpaque]

-- ============================================================================
-- § 4: External Possession
-- ============================================================================

/-- Possessor extraction in Tseltalan always produces external possessors.
    The possessor ends up outside the nominal projection regardless of
    extraction mode:

    - Pied-piping: the whole DP moves to Spec,CP; the possessor is at
      the clause level.
    - Stranding: the possessor raises to an A-position (Spec,ApplP or
      Spec,VoiceP) before Ā-movement.

    This follows from nominal opacity: Ā-subextraction from within a
    nominal is blocked, so possessors can only be extracted by first
    becoming external. @cite{aissen-polian-2025} §3.1. -/
def extractedIsExternal (_mode : ExtractionMode) : Bool := true

theorem extracted_always_external (mode : ExtractionMode) :
    extractedIsExternal mode = true := by cases mode <;> rfl

-- ============================================================================
-- § 5: Bridge to NominalStructure
-- ============================================================================

/-- Map nominal size to possession type from `NominalStructure.lean`.

    - nP-internal possessors (Spec,nP) → inalienable
    - PossP-level possessors (Spec,PossP) → alienable
    - DP subsumes both; the type depends on internal structure. -/
def NominalSize.possessionType : NominalSize → Option PossessionType
  | .nP    => some .inalienable
  | .possP => some .alienable
  | .dp    => none

theorem inalienable_at_nP :
    NominalSize.nP.possessionType = some .inalienable := rfl

theorem alienable_at_possP :
    NominalSize.possP.possessionType = some .alienable := rfl

/-- The possessor position derived from NominalSize agrees with
    PossessionType.possessorPosition from NominalStructure.lean. -/
theorem possessor_position_agrees_inalienable :
    NominalSize.nP.highestPosition =
    PossessionType.inalienable.possessorPosition := rfl

theorem possessor_position_agrees_alienable :
    NominalSize.possP.highestPosition =
    PossessionType.alienable.possessorPosition := rfl

-- ============================================================================
-- § 6: Bridge to SpecificityCondition
-- ============================================================================

/-- Convergence: both A&P's nominal opacity and @cite{fiengo-higginbotham-1981}'s
    Specificity Condition predict that specific DPs resist possessor
    extraction by subextraction/binding into the DP.

    Divergence: A&P predict pied-piping IS available for specific DPs
    (whole DP moves, no subextraction); the Specificity Condition blocks
    ALL operator binding into specific DPs. The two constraints operate
    at different levels — A&P targets syntactic movement, Fiengo &
    Higginbotham targets operator-variable binding. -/
theorem specificity_convergence_on_stranding :
    extractionAvailable .stranding .dp = false ∧
    Core.SpecificityCondition.blocked .whTrace .definite = true := ⟨rfl, rfl⟩

theorem specificity_divergence_on_piedpiping :
    extractionAvailable .piedPiping .dp = true ∧
    Core.SpecificityCondition.blocked .whTrace .definite = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Categorical Judgment (ψ-Subject)
-- ============================================================================

open Core.InformationStructure

/-- ψ-subjects are always cross-referenced by Set B (absolutive),
    regardless of their thematic role.

    @cite{aissen-polian-2025} §5, Table 2: in categorical judgment
    constructions, the subject in Spec,TP triggers Set B agreement
    on T°, even in contexts where an A argument would normally trigger
    Set A. This is because T°'s EPP:D probe attracts the closest DP
    to Spec,TP, and that DP is cross-referenced by Set B (the marker
    set T° assigns). -/
def ψSubjectMarkerSet : MarkerSet := .setB

/-- ψ-subjects get Set B, not Set A. This contrasts with the normal
    transitive pattern where A gets Set A. -/
theorem ψSubject_is_absolutive :
    ψSubjectMarkerSet = .setB := rfl

/-- A categorical judgment places a ψ-subject in Spec,TP. -/
theorem categorical_has_ψSubject :
    JudgmentType.categorical.hasψSubject = true := rfl

/-- A thetic judgment has no ψ-subject. -/
theorem thetic_no_ψSubject :
    JudgmentType.thetic.hasψSubject = false := rfl

-- ============================================================================
-- § 8: ψ-Subject Constructions
-- ============================================================================

/-- The three construction types that exhibit ψ-subjects in Tseltalan.
    @cite{aissen-polian-2025} §5. -/
inductive ψConstruction where
  /-- Predicative possession: 'X has Y' via existential construction.
      ψ-subject = possessor. -/
  | predicativePossession
  /-- Experiential collocation: 'X is happy/angry/etc.'
      ψ-subject = experiencer. -/
  | experientialCollocation
  /-- Lexical unaccusative: 'X arrived/fell/etc.'
      ψ-subject = theme (internal argument of unaccusative V). -/
  | lexicalUnaccusative
  deriving DecidableEq, Repr

/-- The clause type associated with each ψ-subject construction.
    All three are structurally unaccusative: no vP layer, the sole
    argument is complement of V. -/
def ψConstruction.clauseType : ψConstruction → ClauseType
  | .predicativePossession   => .unaccusative
  | .experientialCollocation  => .unaccusative
  | .lexicalUnaccusative     => .unaccusative

/-- All ψ-subject constructions are structurally unaccusative.
    @cite{aissen-polian-2025} §5: predicative possession, experiential
    collocations, and lexical unaccusatives all lack a vP layer. -/
theorem ψ_constructions_unaccusative (c : ψConstruction) :
    c.clauseType = .unaccusative := by cases c <;> rfl

/-- All ψ-subject constructions lack a vP layer. Derived from
    `ClauseType.hasVP` in Tseltalan.lean. -/
theorem ψ_constructions_no_vP (c : ψConstruction) :
    c.clauseType.hasVP = false := by cases c <;> rfl

-- ============================================================================
-- § 9: Intervention Effects (Table 4)
-- ============================================================================

/-- Does a clause type have an A-positioned DP that could intervene
    between T°'s probe and a lower possessor?

    Derived from `ClauseType.hasVP`: if there is a vP layer, its
    specifier hosts an A-positioned DP (agent in transitive, S_A in
    unergative). This DP intervenes via Attract Closest
    (@cite{aissen-polian-2025} §4.2). -/
def hasIntervener (ct : ClauseType) : Bool := ct.hasVP

/-- Possessor stranding is blocked by intervention: an A-positioned
    DP blocks possessor raising past it.
    Pied-piping is unaffected: the whole DP moves directly to Spec,CP
    via Ā-movement, bypassing A-positions entirely. -/
def interventionBlocks (ct : ClauseType) (mode : ExtractionMode) : Bool :=
  match mode with
  | .stranding  => hasIntervener ct
  | .piedPiping => false

/-- An intervention datum for Table 4. -/
structure InterventionDatum where
  clauseType : ClauseType
  mode : ExtractionMode
  blocked : Bool
  deriving DecidableEq, Repr

/-- Table 4 of @cite{aissen-polian-2025}: intervention effects on
    possessor extraction.

    |              | Transitive | Unergative | Unaccusative |
    |--------------|------------|------------|--------------|
    | Pied-piping  | ok         | ok         | ok           |
    | Stranding    | blocked    | blocked    | ok           | -/
def table4 : List InterventionDatum :=
  [ ⟨.transitive,   .piedPiping, false⟩
  , ⟨.unergative,   .piedPiping, false⟩
  , ⟨.unaccusative, .piedPiping, false⟩
  , ⟨.transitive,   .stranding,  true⟩
  , ⟨.unergative,   .stranding,  true⟩
  , ⟨.unaccusative, .stranding,  false⟩ ]

/-- Table 4 is derivable from `interventionBlocks`: every cell matches.
    The table is not stipulated — it follows from the clause type's
    vP structure and the extraction mode. -/
theorem table4_derived :
    table4.all (λ d => d.blocked == interventionBlocks d.clauseType d.mode) = true := by
  decide

/-- Pied-piping is never blocked by intervention (Ā-movement
    bypasses A-positions). -/
theorem piedPiping_never_blocked (ct : ClauseType) :
    interventionBlocks ct .piedPiping = false := by cases ct <;> rfl

/-- Stranding is blocked iff there is an intervener (= vP layer).
    Derived from `ClauseType.hasVP`. -/
theorem stranding_blocked_iff_vP (ct : ClauseType) :
    interventionBlocks ct .stranding = ct.hasVP := by cases ct <;> rfl

-- ============================================================================
-- § 10: Specifier Directionality
-- ============================================================================

/-- Specifier directionality parameter for functional heads.
    @cite{aissen-polian-2025} §4: T° and Appl° in Tseltalan take
    right-side specifiers, yielding post-verbal external possessors
    and post-verbal ψ-subjects. -/
inductive SpecDirection where
  | left   -- specifier precedes head (e.g., English Spec,TP)
  | right  -- specifier follows head (Tseltalan Spec,TP, Spec,ApplP)
  deriving DecidableEq, Repr

/-- Tseltalan T° takes a right-side specifier. -/
def tseltalanTSpec : SpecDirection := .right

/-- Tseltalan Appl° takes a right-side specifier. -/
def tseltalanApplSpec : SpecDirection := .right

-- ============================================================================
-- § 11: Full Extraction Availability
-- ============================================================================

/-- Combining extraction mode availability (§3) with intervention
    effects (§9): is possessor extraction ultimately possible for
    a given nominal size in a given clause type? -/
def canExtractPossessor (size : NominalSize) (ct : ClauseType)
    (mode : ExtractionMode) : Bool :=
  extractionAvailable mode size && !interventionBlocks ct mode

/-- In unaccusative clauses, both modes are available for their
    respective nominal sizes: no intervener blocks stranding,
    and pied-piping is always available for DPs. -/
theorem unaccusative_both_modes :
    canExtractPossessor .dp .unaccusative .piedPiping = true ∧
    canExtractPossessor .possP .unaccusative .stranding = true ∧
    canExtractPossessor .nP .unaccusative .stranding = true := ⟨rfl, rfl, rfl⟩

/-- In transitive clauses, only pied-piping of specific DPs works.
    Stranding is blocked by the agent in Spec,VoiceP. -/
theorem transitive_only_piedpiping :
    canExtractPossessor .dp .transitive .piedPiping = true ∧
    canExtractPossessor .possP .transitive .stranding = false ∧
    canExtractPossessor .nP .transitive .stranding = false := ⟨rfl, rfl, rfl⟩

/-- In unergative clauses, same as transitive: only pied-piping.
    Stranding is blocked by S_A in Spec,vP. -/
theorem unergative_only_piedpiping :
    canExtractPossessor .dp .unergative .piedPiping = true ∧
    canExtractPossessor .possP .unergative .stranding = false ∧
    canExtractPossessor .nP .unergative .stranding = false := ⟨rfl, rfl, rfl⟩

/-- ψ-subject constructions (all unaccusative) permit both extraction
    modes. This follows from §8 (unaccusative) + §9 (no intervener). -/
theorem ψ_constructions_permit_both_modes (c : ψConstruction) :
    canExtractPossessor .dp c.clauseType .piedPiping = true ∧
    canExtractPossessor .possP c.clauseType .stranding = true ∧
    canExtractPossessor .nP c.clauseType .stranding = true := by
  cases c <;> exact ⟨rfl, rfl, rfl⟩

end Phenomena.Possession.Studies.AissenPolian2025
