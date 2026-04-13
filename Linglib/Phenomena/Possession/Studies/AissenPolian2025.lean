import Linglib.Fragments.Mayan.Tseltalan
import Linglib.Theories.Morphology.DM.NominalStructure
import Linglib.Theories.Syntax.Minimalism.Core.Agree
import Linglib.Core.SpecificityCondition
import Linglib.Core.Discourse.InformationStructure

/-!
# Aissen & Polian 2025: Possessor Extraction and Categorical Subject in Tseltalan
@cite{aissen-polian-2025}

*Natural Language & Linguistic Theory* 43:63--113.

## Overview

Tseltalan languages (Tsotsil, Tseltal) have two possessor extraction
strategies — pied-piping and stranding — whose availability depends on
nominal size (= specificity) and intervention by A-positioned DPs.

The analysis rests on two independent mechanisms:

1. **Selective opacity** (@cite{keine-2019}): N⁰ is a horizon for wh-probes
   on C° — Ā-subextraction from within ANY nominal is impossible,
   regardless of size. This forces all possessor extraction to proceed
   via external possession.

2. **D-layer shielding** (Attract Closest): in specific DPs, D° is closer
   to T°'s [EPP:D] probe than the possessor inside Spec,PossP. Non-specific
   nominals (PossP/nP) lack a D layer, so T°'s probe reaches the possessor.

Together these derive:
- Stranding: possessor A-moves out of non-specific nominal (D-probe sees
  through nominal, no D-layer shields), then Ā-moves from external position
- Pied-piping: whole DP moves to Spec,CP (DP is visible to wh-probe as a
  unit; subextraction from within is blocked by selective opacity)
- Why extracted possessors are ALWAYS external (claim (3)): follows from
  selective opacity — not stipulated

Stranding is further constrained by intervention: an A-positioned DP
(agent or S_A) between the possessor and T°'s [EPP:D] probe blocks
possessor raising via Attract Closest.

The paper also identifies three ψ-subject constructions (categorical
judgment subjects in Spec,TP, @cite{kuroda-1972}): predicative possession,
experiential collocations, and lexical unaccusatives.

## Integration Points

- `NominalPosition` / `PossessionType` from `NominalStructure.lean`
- `SpecificityCondition` from `Core/SpecificityCondition.lean`
- `JudgmentType` from `Core/Discourse/InformationStructure.lean`
- `GramFunction` from `Fragments/Mayan/Tseltalan.lean`
- `ABSPosition` from `Fragments/Mayan/Params.lean`
-/

namespace Phenomena.Possession.Studies.AissenPolian2025

open Fragments.Mayan (MarkerSet ABSPosition)
open Fragments.Mayan.Tseltalan
open Theories.Morphology.DM

-- ============================================================================
-- § 1: Nominal Size and Specificity
-- ============================================================================

/-- Nominal projections in Tseltalan, determining extractability.
    @cite{aissen-polian-2025} §3.2, (11)/(18): specific indefinites and
    definites project to DP; non-specific indefinites project only to
    nP (if non-possessive) or PossP (if possessive).

    Derived from the nominal spine in `NominalStructure.lean`:
    √ROOT < n < (Poss) < D. -/
inductive NominalSize where
  | dp    -- projects to D: specific nominals
  | possP -- projects to PossP: non-specific with alienable possessor
  | nP    -- projects to nP: non-specific with inalienable possessor
  deriving DecidableEq, Repr

/-- The highest position projected in the nominal spine.
    For DPs, the highest position is D (which shields the possessor
    from external D-probes). For non-specific nominals, the highest
    position IS the possessor's specifier position, making the
    possessor directly accessible. -/
def NominalSize.highestProjection : NominalSize → NominalPosition
  | .dp    => .d       -- D head shields possessor
  | .possP => .specPoss -- possessor directly accessible
  | .nP    => .specN    -- possessor directly accessible

/-- Specific nominals project to DP; non-specific nominals do not.
    @cite{aissen-polian-2025} §3.2. -/
def NominalSize.isSpecific : NominalSize → Bool
  | .dp    => true
  | .possP => false
  | .nP    => false

-- ============================================================================
-- § 2: Clause Types (Theoretical Classification)
-- ============================================================================

/-- Clause types in Tseltalan, classified by whether the verb projects
    an external argument (vP layer). This is a theoretical classification
    from Minimalist syntax, used here to derive intervention effects.

    @cite{aissen-polian-2025} (9):
    - Unaccusative: no vP layer (sole argument is complement of V)
    - Transitive: vP layer with agent in Spec,vP
    - Unergative: vP layer with agentive S in Spec,vP -/
inductive ClauseType where
  | unaccusative  -- no vP layer (existentials, unaccusatives)
  | transitive    -- vP layer with agent
  | unergative    -- vP layer with agentive intransitive subject
  deriving DecidableEq, Repr

/-- Whether a clause type projects a vP layer (= has an external argument
    position that could host an intervening DP).
    @cite{aissen-polian-2025} (9): transitives and unergatives have vP;
    unaccusatives do not. -/
def ClauseType.hasVP : ClauseType → Bool
  | .unaccusative => false
  | .transitive   => true
  | .unergative   => true

/-- Unaccusatives lack a vP layer. -/
theorem unaccusative_no_vP : ClauseType.unaccusative.hasVP = false := rfl

/-- Transitives and unergatives both project vP. -/
theorem vp_distribution :
    ClauseType.transitive.hasVP = true ∧
    ClauseType.unergative.hasVP = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 3: Probe Types and Selective Opacity
-- ============================================================================

/-- Probe types that trigger movement in Tseltalan.
    @cite{aissen-polian-2025} §3.1, (10):

    - **[EPP:D]** on T° and Appl°: triggers A-movement of a DP to
      the probe's specifier. T° and Appl° take rightside specifiers.
    - **[EPP:WH]** on D° (secondary wh-movement) and C° (primary
      wh-movement): triggers Ā-movement of a wh-phrase. -/
inductive ProbeType where
  | dProbe   -- [EPP:D] on T° or Appl° (A-movement)
  | whProbe  -- [EPP:WH] on D° or C° (Ā-movement)
  deriving DecidableEq, Repr

/-- **Selective opacity** (@cite{keine-2019}, @cite{aissen-polian-2025} (33)):
    N⁰ is a horizon for wh-probes on C°. Elements inside the extended
    projection of N⁰ are invisible to wh-probes, blocking Ā-subextraction.

    Crucially, this does NOT apply to D-probes: A-movement of a possessor
    DP out of a nominal is permitted. The opacity is *selective* — it
    depends on the probe type, not on nominal size.

    `[wh]_{C°} -|| N` (A&P's (33)) -/
def selectivelyOpaque (probe : ProbeType) : Bool :=
  match probe with
  | .whProbe => true   -- nominals always opaque to wh-probes
  | .dProbe  => false  -- nominals transparent to D-probes

theorem wh_probes_blocked : selectivelyOpaque .whProbe = true := rfl
theorem d_probes_pass : selectivelyOpaque .dProbe = false := rfl

/-- Ā-subextraction from within any nominal is impossible. Derived
    from selective opacity: wh-probes cannot see into nominals. -/
def canĀSubextract (_size : NominalSize) : Bool :=
  !selectivelyOpaque .whProbe

theorem subextraction_impossible (size : NominalSize) :
    canĀSubextract size = false := rfl

-- ============================================================================
-- § 4: D-Layer Shielding (Attract Closest)
-- ============================================================================

/-- **D-layer shielding**: in a specific nominal (DP), D° is closer to
    an external D-probe (T°'s [EPP:D]) than the possessor inside
    Spec,PossP or Spec,nP. Attract Closest causes the probe to find
    D° first, preventing it from reaching the possessor.

    Non-specific nominals (PossP/nP) lack a D layer, so T°'s probe
    reaches the possessor directly.

    This is independent of selective opacity: D-probes CAN see into
    nominals (selectivelyOpaque .dProbe = false), but D° intervenes
    when present.

    Derived from `isSpecific`: D-layer shielding ↔ specificity. -/
def dLayerShields (size : NominalSize) : Bool :=
  size.isSpecific

theorem dp_shields : dLayerShields .dp = true := rfl
theorem possP_no_shield : dLayerShields .possP = false := rfl
theorem nP_no_shield : dLayerShields .nP = false := rfl

-- ============================================================================
-- § 5: Extraction Modes
-- ============================================================================

/-- Two possessor extraction strategies in Tseltalan.
    @cite{aissen-polian-2025} §3. -/
inductive ExtractionMode where
  /-- Pied-piping: the entire nominal (including possessor) moves to
      Spec,CP. Requires D projection: only DPs can be targeted by a
      wh-probe as a unit. -/
  | piedPiping
  /-- Stranding: the possessor first A-moves out of the nominal via
      T°'s or Appl°'s [EPP:D] probe, then Ā-moves from the external
      position. Requires the nominal to be transparent to D-probes
      (always true) AND no D-layer shielding (non-specific). -/
  | stranding
  deriving DecidableEq, Repr

/-- Whether a given extraction mode is available for a nominal of
    given size, ignoring clause-level intervention.

    - **Pied-piping**: the whole DP moves via wh-probe → requires D
      projection (specific). Non-DPs cannot undergo wh-movement.
    - **Stranding**: possessor A-moves out via D-probe → requires no
      D-layer shielding. D-probes see through nominals (selective
      opacity doesn't apply), but D° intervenes in specific DPs.

    @cite{aissen-polian-2025} §3.2. -/
def extractionAvailable (mode : ExtractionMode) (size : NominalSize) : Bool :=
  match mode with
  | .piedPiping => size.isSpecific       -- only DPs can undergo wh-movement
  | .stranding  => !dLayerShields size   -- no D-layer → possessor reachable

/-- Pied-piping requires specificity (D projection). -/
theorem piedPiping_requires_specific :
    extractionAvailable .piedPiping .dp = true ∧
    extractionAvailable .piedPiping .possP = false ∧
    extractionAvailable .piedPiping .nP = false := ⟨rfl, rfl, rfl⟩

/-- Stranding requires non-specificity (no D-layer shielding). -/
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
  cases size <;> simp [extractionAvailable, dLayerShields]

/-- **Complementary distribution**: pied-piping and stranding are
    mutually exclusive — exactly one is available for each nominal size.
    Specific nominals admit only pied-piping; non-specific nominals
    admit only stranding. Both reduce to `isSpecific`. -/
theorem extraction_complementary (size : NominalSize) :
    extractionAvailable .piedPiping size =
    !extractionAvailable .stranding size := by
  cases size <;> simp [extractionAvailable, dLayerShields]

-- ============================================================================
-- § 6: External Possession (Derived from Selective Opacity)
-- ============================================================================

/-- Possessor extraction in Tseltalan never involves Ā-subextraction.
    This follows from selective opacity: wh-probes cannot see into
    nominals, so the possessor cannot be extracted from within.

    Since subextraction is impossible, extraction requires either:
    (a) moving the whole nominal (pied-piping) — possessor at clause level
    (b) first A-moving the possessor out (stranding) — possessor external

    In both cases, the extracted possessor is external at the point
    of Ā-movement. This is A&P's claim (3): "An extracted possessor
    in Tseltalan is always an external possessor." -/
theorem extracted_always_external :
    canĀSubextract .dp = false ∧
    canĀSubextract .possP = false ∧
    canĀSubextract .nP = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 7: Bridge to NominalStructure
-- ============================================================================

/-- Map nominal size to possession type from `NominalStructure.lean`.

    - nP-internal possessors (Spec,nP) → inalienable
    - PossP-level possessors (Spec,PossP) → alienable
    - DP subsumes both; the type depends on internal structure. -/
def NominalSize.toPossessionType : NominalSize → Option PossessionType
  | .nP    => some .inalienable
  | .possP => some .alienable
  | .dp    => none

theorem inalienable_at_nP :
    NominalSize.nP.toPossessionType = some .inalienable := rfl

theorem alienable_at_possP :
    NominalSize.possP.toPossessionType = some .alienable := rfl

/-- For non-specific nominals, the highest projection IS the possessor's
    position, agreeing with PossessionType.possessorPosition from
    NominalStructure.lean. For DPs, the highest projection is D (the
    possessor is shielded below). -/
theorem highest_agrees_inalienable :
    NominalSize.nP.highestProjection =
    PossessionType.inalienable.possessorPosition := rfl

theorem highest_agrees_alienable :
    NominalSize.possP.highestProjection =
    PossessionType.alienable.possessorPosition := rfl

-- ============================================================================
-- § 8: Bridge to SpecificityCondition
-- ============================================================================

/-- Convergence: both A&P's D-layer shielding and @cite{fiengo-higginbotham-1981}'s
    Specificity Condition predict that specific DPs resist possessor
    extraction by stranding/binding into the DP.

    Divergence: A&P predict pied-piping IS available for specific DPs
    (whole DP moves, no subextraction); the Specificity Condition blocks
    ALL operator binding into specific DPs. The two constraints operate
    at different levels — D-layer shielding targets A-movement (D-probes),
    the Specificity Condition targets operator-variable binding. -/
theorem specificity_convergence_on_stranding :
    extractionAvailable .stranding .dp = false ∧
    Core.SpecificityCondition.blocked .whTrace .definite = true := ⟨rfl, rfl⟩

theorem specificity_divergence_on_piedpiping :
    extractionAvailable .piedPiping .dp = true ∧
    Core.SpecificityCondition.blocked .whTrace .definite = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 9: Categorical Judgment (ψ-Subject)
-- ============================================================================

open Core.InformationStructure

/-- The grammatical function of a ψ-subject.
    ψ-subjects are always intransitive subjects — they raise from
    unaccusative clauses where the sole argument is S_O (patientive).

    @cite{aissen-polian-2025} §5, Table 1: all ψ-subject constructions
    are structurally unaccusative, so the ψ-subject is always S_O. -/
def ψSubjectGramFunction : GramFunction := .S_O

/-- ψ-subject agreement is DERIVED from GramFunction.markerSet:
    ψ-subjects are S_O, and S_O maps to Set B (absolutive). -/
def ψSubjectMarkerSet : MarkerSet := ψSubjectGramFunction.markerSet

/-- ψ-subjects receive Set B (absolutive) agreement — derived from
    the fact that they are S_O, and S_O maps to Set B. -/
theorem ψSubject_is_absolutive :
    ψSubjectMarkerSet = .setB := rfl

theorem categorical_has_ψSubject :
    JudgmentType.categorical.hasψSubject = true := rfl

theorem thetic_no_ψSubject :
    JudgmentType.thetic.hasψSubject = false := rfl

/-- A ψ-subject must be specific (= project to DP) to raise to Spec,TP.
    @cite{aissen-polian-2025} §5.1, p. 85: "the subject of a clause
    which expresses a categorical judgment cannot be non-specific."

    This connects the specificity system to the ψ-subject system:
    T°'s [EPP:D] probe searches for a DP. If the highest nominal in
    T°'s domain is non-specific (PossP/nP), it is not a DP, and T°'s
    probe passes over it. Only a specific DP satisfies the [EPP:D]
    requirement and raises to Spec,TP as ψ-subject. -/
def canBeψSubject (size : NominalSize) : Bool :=
  size.isSpecific

theorem specific_can_be_ψSubject : canBeψSubject .dp = true := rfl
theorem nonspecific_cannot_be_ψSubject_possP :
    canBeψSubject .possP = false := rfl
theorem nonspecific_cannot_be_ψSubject_nP :
    canBeψSubject .nP = false := rfl

-- ============================================================================
-- § 10: ψ-Subject Constructions
-- ============================================================================

/-- The three construction types that exhibit ψ-subjects in Tseltalan.
    @cite{aissen-polian-2025} §5. -/
inductive ψConstruction where
  /-- Predicative possession: 'X has Y' via existential construction
      (Tsotsil *oy*, Tseltal *ay*). ψ-subject = possessor. -/
  | predicativePossession
  /-- Experiential collocation: 'X is angry' (lit: 'x's head gets
      mixed up'). ψ-subject = experiencer-possessor. -/
  | experientialCollocation
  /-- Lexical unaccusative: 'X's money was lost.'
      ψ-subject = possessor of theme (S_O). -/
  | lexicalUnaccusative
  deriving DecidableEq, Repr

/-- The clause type associated with each ψ-subject construction.
    All three are structurally unaccusative: no vP layer, the sole
    argument is complement of V. -/
def ψConstruction.clauseType : ψConstruction → ClauseType
  | .predicativePossession   => .unaccusative
  | .experientialCollocation  => .unaccusative
  | .lexicalUnaccusative     => .unaccusative

/-- Whether pied-piping is possible for a given ψ-construction.

    In predicative possession (§5.2, (48a/48b)) and experiential
    collocations (§5.3, (55a/55b)), the possessor and possessum do NOT
    form a constituent that can undergo wh-movement: the predicative
    element (*oy*/*ay*, or the verb) intervenes. Only stranding works.

    In lexical unaccusatives (§5.4, (62a/62b)), the entire possessive
    phrase IS the internal argument and can be pied-piped. -/
def ψConstruction.piedPipingPossible : ψConstruction → Bool
  | .predicativePossession  => false  -- (48b): *[Mach'u x-chitom] oy t?
  | .experientialCollocation => false  -- (55b): *[Much'u s-jol] kap-em t?
  | .lexicalUnaccusative    => true   -- (62a): [Mach'a s-tak'in] ch'ay t?

theorem pred_poss_no_piedpiping :
    ψConstruction.predicativePossession.piedPipingPossible = false := rfl
theorem exp_coll_no_piedpiping :
    ψConstruction.experientialCollocation.piedPipingPossible = false := rfl
theorem lex_unacc_piedpiping_ok :
    ψConstruction.lexicalUnaccusative.piedPipingPossible = true := rfl

/-- All ψ-subject constructions are structurally unaccusative. -/
theorem ψ_constructions_unaccusative (c : ψConstruction) :
    c.clauseType = .unaccusative := by cases c <;> rfl

/-- All ψ-subject constructions lack a vP layer. -/
theorem ψ_constructions_no_vP (c : ψConstruction) :
    c.clauseType.hasVP = false := by cases c <;> rfl

/-- The grammatical function of the ψ-subject in each construction.
    All three involve an unaccusative S_O that raises to Spec,TP.
    @cite{aissen-polian-2025} §5:
    - Predicative possession: possessor of the existential pivot
    - Experiential collocation: experiencer-possessor
    - Lexical unaccusative: possessor of the unaccusative theme -/
def ψConstruction.ψSubjectFunction : ψConstruction → GramFunction
  | .predicativePossession  => .S_O
  | .experientialCollocation => .S_O
  | .lexicalUnaccusative    => .S_O

/-- All ψ-subject constructions assign S_O to the ψ-subject. -/
theorem ψ_constructions_all_S_O (c : ψConstruction) :
    c.ψSubjectFunction = .S_O := by cases c <;> rfl

/-- ψ-subject agreement in each construction is Set B, derived from
    the S_O grammatical function via the shared Tseltalan paradigm. -/
theorem ψ_constructions_setB (c : ψConstruction) :
    c.ψSubjectFunction.markerSet = .setB := by cases c <;> rfl

-- ============================================================================
-- § 11: Intervention Effects (Table 4)
-- ============================================================================

/-- Functional heads that carry [EPP:D] probes triggering A-movement.
    @cite{aissen-polian-2025} §4.2, §6, Table 4. -/
inductive DProbeHead where
  | t     -- T° in all clause types
  | appl  -- Appl° in applicative constructions
  deriving DecidableEq, Repr

/-- Does a clause type have an A-positioned DP that could intervene
    between a given probe and a lower possessor?

    Derived from `ClauseType.hasVP` for T° probes: if there is a vP
    layer, its specifier hosts an A-positioned DP (agent or S_A).
    For Appl° probes, intervention occurs when Spec,ApplP is filled
    by a thematic applied argument (goal, recipient, etc.). -/
def hasIntervener (head : DProbeHead) (ct : ClauseType)
    (thematicAppl : Bool) : Bool :=
  match head with
  | .t    => ct.hasVP
  | .appl => thematicAppl

/-- Possessor stranding is blocked when an A-positioned DP intervenes
    between the [EPP:D] probe and the possessor.
    Pied-piping is unaffected: the whole DP moves to Spec,CP via
    wh-probe, bypassing A-positions entirely. -/
def interventionBlocks (head : DProbeHead) (ct : ClauseType)
    (mode : ExtractionMode) (thematicAppl : Bool := false) : Bool :=
  match mode with
  | .stranding  => hasIntervener head ct thematicAppl
  | .piedPiping => false

/-- An intervention datum for Table 4. -/
structure InterventionDatum where
  probe : DProbeHead
  clauseType : ClauseType
  mode : ExtractionMode
  /-- Is Spec,ApplP filled by a thematic applied argument? -/
  thematicAppl : Bool
  /-- Is extraction blocked? -/
  blocked : Bool
  deriving DecidableEq, Repr

/-- Table 4 of @cite{aissen-polian-2025} (p. 103): intervention effects
    on possessor extraction. Expanded to include Appl° probe cases.

    | Probe  | Clause Type    | Thematic Appl | Pied-piping | Stranding |
    |--------|----------------|---------------|-------------|-----------|
    | T°     | unaccusative   | —             | ok          | ok        |
    | T°     | transitive     | —             | ok          | blocked   |
    | T°     | unergative     | —             | ok          | blocked   |
    | Appl°  | (raising appl) | no            | ok          | ok        |
    | Appl°  | (thematic appl)| yes           | ok          | blocked   | -/
def table4 : List InterventionDatum :=
  -- T° probe, no thematic applicative
  [ ⟨.t, .unaccusative, .piedPiping, false, false⟩
  , ⟨.t, .unaccusative, .stranding,  false, false⟩
  , ⟨.t, .transitive,   .piedPiping, false, false⟩
  , ⟨.t, .transitive,   .stranding,  false, true⟩
  , ⟨.t, .unergative,   .piedPiping, false, false⟩
  , ⟨.t, .unergative,   .stranding,  false, true⟩
  -- Appl° probe: raising applicative (empty Spec,ApplP)
  , ⟨.appl, .transitive, .piedPiping, false, false⟩
  , ⟨.appl, .transitive, .stranding,  false, false⟩
  -- Appl° probe: thematic applicative (Goal in Spec,ApplP)
  , ⟨.appl, .transitive, .piedPiping, true, false⟩
  , ⟨.appl, .transitive, .stranding,  true, true⟩ ]

/-- Table 4 is derivable: every cell matches `interventionBlocks`. -/
theorem table4_derived :
    table4.all (λ d => d.blocked ==
      interventionBlocks d.probe d.clauseType d.mode d.thematicAppl)
    = true := by decide

/-- Pied-piping is never blocked by intervention (Ā-movement
    bypasses A-positions). -/
theorem piedPiping_never_blocked (head : DProbeHead) (ct : ClauseType)
    (ta : Bool) :
    interventionBlocks head ct .piedPiping ta = false := by
  cases head <;> rfl

/-- For T° probes, stranding is blocked iff there is a vP layer. -/
theorem t_stranding_blocked_iff_vP (ct : ClauseType) :
    interventionBlocks .t ct .stranding = ct.hasVP := by
  cases ct <;> rfl

/-- For Appl° probes, stranding is blocked iff Spec,ApplP is filled
    by a thematic applied argument. -/
theorem appl_stranding_blocked_iff_thematic (ct : ClauseType) (ta : Bool) :
    interventionBlocks .appl ct .stranding ta = ta := by
  cases ta <;> rfl

-- ============================================================================
-- § 12: Specifier Directionality
-- ============================================================================

/-- Specifier directionality parameter for functional heads.
    @cite{aissen-polian-2025} §3.1, (10): the default is leftside
    specifiers, but T°, Appl°, and possibly Poss° take rightside
    specifiers in Tseltalan. This yields post-verbal ψ-subjects
    and post-verbal external possessors. -/
inductive SpecDirection where
  | left   -- specifier precedes head (e.g., English Spec,TP)
  | right  -- specifier follows head (Tseltalan Spec,TP, Spec,ApplP)
  deriving DecidableEq, Repr

/-- Tseltalan T° takes a right-side specifier. -/
def tseltalanTSpec : SpecDirection := .right

/-- Tseltalan Appl° takes a right-side specifier. -/
def tseltalanApplSpec : SpecDirection := .right

-- ============================================================================
-- § 13: Full Extraction Availability
-- ============================================================================

/-- Combining extraction mode availability (§4) with intervention
    effects (§10): is possessor extraction ultimately possible for
    a given nominal size, clause type, and probe? -/
def canExtractPossessor (size : NominalSize) (head : DProbeHead)
    (ct : ClauseType) (mode : ExtractionMode)
    (thematicAppl : Bool := false) : Bool :=
  extractionAvailable mode size &&
    !interventionBlocks head ct mode thematicAppl

/-- In unaccusative clauses via T°, both modes are available. -/
theorem unaccusative_both_modes :
    canExtractPossessor .dp .t .unaccusative .piedPiping = true ∧
    canExtractPossessor .possP .t .unaccusative .stranding = true ∧
    canExtractPossessor .nP .t .unaccusative .stranding = true :=
  ⟨rfl, rfl, rfl⟩

/-- In transitive clauses via T°, only pied-piping works. -/
theorem transitive_only_piedpiping :
    canExtractPossessor .dp .t .transitive .piedPiping = true ∧
    canExtractPossessor .possP .t .transitive .stranding = false ∧
    canExtractPossessor .nP .t .transitive .stranding = false :=
  ⟨rfl, rfl, rfl⟩

/-- Via Appl° raising applicative (no thematic arg), stranding works. -/
theorem raising_appl_stranding :
    canExtractPossessor .possP .appl .transitive .stranding false = true ∧
    canExtractPossessor .nP .appl .transitive .stranding false = true :=
  ⟨rfl, rfl⟩

/-- Via Appl° thematic applicative (Goal fills Spec,ApplP), blocked. -/
theorem thematic_appl_blocked :
    canExtractPossessor .possP .appl .transitive .stranding true = false ∧
    canExtractPossessor .nP .appl .transitive .stranding true = false :=
  ⟨rfl, rfl⟩

/-- ψ-subject constructions (all unaccusative) permit both extraction
    modes via T°. -/
theorem ψ_constructions_permit_both_modes (c : ψConstruction) :
    canExtractPossessor .dp .t c.clauseType .piedPiping = true ∧
    canExtractPossessor .possP .t c.clauseType .stranding = true ∧
    canExtractPossessor .nP .t c.clauseType .stranding = true := by
  cases c <;> exact ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 14: Table 2 — Psr-S_O vs Psr-O Extraction Asymmetry
-- ============================================================================

/-- Table 2 of @cite{aissen-polian-2025} (p. 77): possessor extraction
    and grammatical function in Ch'ol and Tseltalan.

    | Mode        | Psr-S_O | Psr-O |
    |-------------|---------|-------|
    | Stranding   |    ✓    |   *   |
    | Pied-piping |    ✓    |   ✓   |

    Derived: Psr-S_O is the possessor of the internal argument of an
    unaccusative clause (no vP → no intervener → stranding OK).
    Psr-O is the possessor of the internal argument of a transitive
    clause (vP layer → agent intervenes → stranding blocked). -/
theorem table2_psr_S_O :
    canExtractPossessor .possP .t .unaccusative .stranding = true ∧
    canExtractPossessor .dp .t .unaccusative .piedPiping = true :=
  ⟨rfl, rfl⟩

theorem table2_psr_O :
    canExtractPossessor .possP .t .transitive .stranding = false ∧
    canExtractPossessor .dp .t .transitive .piedPiping = true :=
  ⟨rfl, rfl⟩

/-- The stranding asymmetry between Psr-S_O and Psr-O reduces to
    whether the clause type has a vP layer. -/
theorem stranding_asymmetry_is_vP :
    canExtractPossessor .possP .t .unaccusative .stranding = true ∧
    canExtractPossessor .possP .t .transitive .stranding = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 15: Bridge to Ergativity
-- ============================================================================

/-- Tseltalan is LOW-ABS: absolutive agreement follows the verb stem.
    @cite{aissen-polian-2025} p. 97: in Tseltalan, "A's extract freely"
    — there are no syntactic ergativity effects. This is consistent with
    Tada's generalization: LOW-ABS languages lack extraction asymmetries.

    The intervention effects in Table 4 are NOT about Ā-movement being
    blocked by A-positioned DPs (as in HIGH-ABS/syntactically ergative
    languages). Rather, they are about A-movement (possessor raising)
    being blocked by a closer A-positioned DP, preventing the possessor
    from reaching an external position from which it could Ā-extract. -/
def tseltalanABSPosition : ABSPosition := .low

theorem tseltalan_is_low_abs :
    tseltalanABSPosition = .low := rfl

/-- LOW-ABS languages have ABS=DEF (v° assigns case to transitive
    object), not ABS=NOM (Infl° assigns case). -/
theorem tseltalan_case_locus :
    Fragments.Mayan.toCaseLocus tseltalanABSPosition =
    Fragments.Mayan.CaseLocus.absDef := rfl

-- ============================================================================
-- § 16: Tree-Geometric Derivation (Attract Closest)
-- ============================================================================

section AttractClosest

open Minimalism

/-! ### Attract Closest on Concrete Trees

The boolean functions `dLayerShields`, `hasIntervener`, and
`canExtractPossessor` above capture the paper's predictions but
**stipulate** them directly. Here we **derive** them from Attract
Closest applied to concrete `SyntacticObject` trees
(@cite{aissen-polian-2025} (9a-c)), using `closestGoalB` from
`Theories.Syntax.Minimalism.Core.Agree`.

**Key derivation**: T°'s [EPP:D] probe searches its c-command domain
for the closest D-bearing element. The result depends only on tree
geometry and which nodes carry D features:

| Tree configuration         | Closest D-bearer | Possessor reachable? |
|----------------------------|------------------|----------------------|
| Unaccusative + PossP       | Psr              | ✓ (stranding)        |
| Unaccusative + DP          | D°               | ✗ (D-layer shields)  |
| Transitive + PossP         | Agent            | ✗ (agent intervenes) |
| Transitive + DP            | Agent            | ✗ (double blocking)  |
-/

/-- Whether a `SyntacticObject` leaf carries D-category features.
    Matching criterion for T°'s [EPP:D] probe: D-bearing elements
    (possessor DPs, D° heads, agent DPs) are potential goals. -/
private def hasDFeatures : SyntacticObject → Bool
  | .leaf tok => tok.item.outerCat == .D
  | .node _ _ => false

/-! ### Leaf Nodes -/

private def T₀  := mkLeaf .T [] 1   -- T° head (carries [EPP:D] probe)
private def V₀  := mkLeaf .V [] 2   -- V° (lexical verb)
private def v₀  := mkLeaf .v [] 3   -- v° (light verb, introduces agent)
private def Psr := mkLeaf .D [] 4   -- Possessor DP (D-bearing)
private def Psm := mkLeaf .N [] 5   -- Possessum (noun, not D-bearing)
private def D₀  := mkLeaf .D [] 6   -- D° head of specific nominal
private def Agt := mkLeaf .D [] 7   -- Agent DP (D-bearing)

/-! ### Clause Trees (@cite{aissen-polian-2025} (9a-c))

(9a) Unaccusative: `[TP T° [VP V° OBJECT]]`
     No vP layer — sole argument is complement of V.

(9b) Transitive: `[TP T° [vP Agent [v' v° [VP V° OBJECT]]]]`
     Agent in Spec,vP — creates potential intervener.

Object is PossP (non-specific) or DP (specific). -/

-- Non-specific possessive object: [PossP Psr Psm]
private def possP' := SyntacticObject.node Psr Psm

-- Specific possessive object: [DP D° [PossP Psr Psm]]
private def dpObj := SyntacticObject.node D₀ possP'

-- (9a) Unaccusative + non-specific: [TP T° [VP V° [PossP Psr Psm]]]
private def treeUnaccPossP :=
  SyntacticObject.node T₀ (SyntacticObject.node V₀ possP')

-- (9a') Unaccusative + specific: [TP T° [VP V° [DP D° [PossP Psr Psm]]]]
private def treeUnaccDP :=
  SyntacticObject.node T₀ (SyntacticObject.node V₀ dpObj)

-- (9b) Transitive + non-specific:
-- [TP T° [vP Agt [v' v° [VP V° [PossP Psr Psm]]]]]
private def treeTransPossP :=
  SyntacticObject.node T₀
    (SyntacticObject.node Agt
      (SyntacticObject.node v₀
        (SyntacticObject.node V₀ possP')))

-- (9b') Transitive + specific:
-- [TP T° [vP Agt [v' v° [VP V° [DP D° [PossP Psr Psm]]]]]]
private def treeTransDP :=
  SyntacticObject.node T₀
    (SyntacticObject.node Agt
      (SyntacticObject.node v₀
        (SyntacticObject.node V₀ dpObj)))

/-! ### Core Predictions

Each theorem shows that `closestGoalB` computes the correct
result for T°'s [EPP:D] probe searching for the possessor. -/

/-- **Unaccusative + PossP**: possessor IS the closest D-bearer to T°.
    No D-layer, no agent → T°'s probe reaches possessor directly.
    This is why stranding is available. -/
theorem unacc_possP_psr_closest :
    closestGoalB treeUnaccPossP T₀ Psr hasDFeatures = true := by decide

/-- **Unaccusative + DP**: possessor is NOT the closest D-bearer.
    D° is closer to T° than the possessor inside Spec,PossP.
    This is D-layer shielding — stranding is blocked. -/
theorem unacc_dp_psr_blocked :
    closestGoalB treeUnaccDP T₀ Psr hasDFeatures = false := by decide

/-- **Unaccusative + DP**: D° IS the closest D-bearer to T°.
    The whole DP is what T°'s probe attracts — basis for pied-piping. -/
theorem unacc_dp_dHead_closest :
    closestGoalB treeUnaccDP T₀ D₀ hasDFeatures = true := by decide

/-- **Transitive + PossP**: possessor is NOT the closest D-bearer.
    Agent in Spec,vP is closer — the agent intervenes.
    This is why stranding is blocked in transitives. -/
theorem trans_possP_psr_blocked :
    closestGoalB treeTransPossP T₀ Psr hasDFeatures = false := by decide

/-- **Transitive + PossP**: agent IS the closest D-bearer to T°.
    T°'s probe attracts the agent, not the possessor. -/
theorem trans_possP_agt_closest :
    closestGoalB treeTransPossP T₀ Agt hasDFeatures = true := by decide

/-- **Transitive + DP**: double blocking — both agent AND D° shield
    the possessor from T°'s probe. -/
theorem trans_dp_psr_blocked :
    closestGoalB treeTransDP T₀ Psr hasDFeatures = false := by decide

/-! ### Bridge Theorems

The tree-geometric derivation agrees with the boolean stipulations
from §§3-4. Each conjunction pairs a tree prediction with the
corresponding boolean function, showing they make identical claims. -/

/-- D-layer shielding: tree geometry matches `dLayerShields .dp`. -/
theorem bridge_dLayer_dp :
    closestGoalB treeUnaccDP T₀ Psr hasDFeatures = false ∧
    dLayerShields .dp = true := ⟨by decide, rfl⟩

/-- No D-layer for PossP: tree geometry matches `dLayerShields .possP`. -/
theorem bridge_no_dLayer_possP :
    closestGoalB treeUnaccPossP T₀ Psr hasDFeatures = true ∧
    dLayerShields .possP = false := ⟨by decide, rfl⟩

/-- Agent intervention: tree geometry matches `hasIntervener .t .transitive`. -/
theorem bridge_intervention_trans :
    closestGoalB treeTransPossP T₀ Psr hasDFeatures = false ∧
    hasIntervener .t .transitive false = true := ⟨by decide, rfl⟩

/-- No intervention in unaccusative: tree geometry matches
    `hasIntervener .t .unaccusative`. -/
theorem bridge_no_intervention_unacc :
    closestGoalB treeUnaccPossP T₀ Psr hasDFeatures = true ∧
    hasIntervener .t .unaccusative false = false := ⟨by decide, rfl⟩

-- ============================================================================
-- § 17: Selective Opacity from Tree Geometry (N-Horizons)
-- ============================================================================

/-! ### Selective Opacity as a Tree Constraint

Selective opacity (@cite{keine-2019}, @cite{aissen-polian-2025} (33))
states that N° is a horizon for wh-probes: C°'s [EPP:WH] probe
cannot see elements c-commanded by N° (= inside the nominal's
lexical projection). Here we derive this from `behindHorizonB`
applied to concrete trees.

The key geometric fact: in `[PossP Psr N°]`, N° and Psr are sisters,
so N° c-commands Psr. This makes Psr invisible to any probe for
which N° is a horizon. But D° (sister of PossP, NOT c-commanded by
N°) remains visible — which is why pied-piping works.

Together with § 16 (Attract Closest), both pillars of A&P's analysis
are now derived from tree geometry:
- **D-layer shielding / intervention** → `closestGoalB` (§ 16)
- **Selective opacity** → `behindHorizonB` (§ 17)
-/

private def C₀ := mkLeaf .C [] 8

-- CP wrapping unaccusative + DP:
-- [CP C° [TP T° [VP V° [DP D° [PossP Psr Psm]]]]]
private def treeCPUnaccDP := SyntacticObject.node C₀ treeUnaccDP

-- CP wrapping unaccusative + PossP:
-- [CP C° [TP T° [VP V° [PossP Psr Psm]]]]
private def treeCPUnaccPossP := SyntacticObject.node C₀ treeUnaccPossP

/-! ### Core Predictions -/

/-- Psr is behind the N-horizon in the DP tree: C°'s wh-probe cannot
    subextract the possessor from inside the DP. N° (Psm) c-commands
    Psr (they are sisters in PossP), so Psr is in N°'s opaque domain. -/
theorem psr_behind_horizon_dp :
    behindHorizonB treeCPUnaccDP C₀ Psr .N = true := by decide

/-- Psr is behind the N-horizon in the PossP tree: selective opacity
    applies regardless of nominal size. Even without a D layer, N°
    c-commands Psr. -/
theorem psr_behind_horizon_possP :
    behindHorizonB treeCPUnaccPossP C₀ Psr .N = true := by decide

/-- D° is NOT behind the N-horizon: N° (Psm) does not c-command D°.
    D° is a sister of PossP, not inside N°'s c-command domain. This
    is why pied-piping (whole DP movement to Spec,CP) is available:
    the wh-probe can see D° even though it cannot see inside PossP. -/
theorem dHead_not_behind_horizon :
    behindHorizonB treeCPUnaccDP C₀ D₀ .N = false := by decide

/-- The N-horizon is geometrically present even for D-probes — N°
    c-commands Psr regardless of probe type. The difference is that
    D-probes IGNORE the horizon (`selectivelyOpaque .dProbe = false`).
    This is the "selective" in selective opacity: the same tree
    geometry produces different results for different probe types. -/
theorem horizon_present_but_dprobe_ignores :
    behindHorizonB treeUnaccPossP T₀ Psr .N = true ∧
    selectivelyOpaque .dProbe = false := ⟨by decide, rfl⟩

/-! ### Bridge Theorems -/

/-- Selective opacity from tree geometry: the N-horizon blocks
    wh-subextraction of Psr from both DP and PossP nominals,
    agreeing with `canĀSubextract`. -/
theorem bridge_selective_opacity :
    behindHorizonB treeCPUnaccDP C₀ Psr .N = true ∧
    behindHorizonB treeCPUnaccPossP C₀ Psr .N = true ∧
    canĀSubextract .dp = false ∧
    canĀSubextract .possP = false := ⟨by decide, by decide, rfl, rfl⟩

/-- D° visible despite N-horizon: pied-piping is available because
    D° is outside N°'s c-command domain. Agrees with
    `extractionAvailable .piedPiping .dp`. -/
theorem bridge_piedpiping_ok :
    behindHorizonB treeCPUnaccDP C₀ D₀ .N = false ∧
    extractionAvailable .piedPiping .dp = true := ⟨by decide, rfl⟩

/-! ### Unified Derivation -/

/-- **Both pillars from tree geometry**: D-layer shielding, agent
    intervention, selective opacity, and pied-piping availability
    all follow from Attract Closest + N-horizons on concrete trees.

    (a) D-layer shielding: D° closer to T° than Psr (`closestGoalB`)
    (b) Agent intervention: Agt closer to T° than Psr (`closestGoalB`)
    (c) Selective opacity: N° c-commands Psr (`behindHorizonB`)
    (d) Pied-piping: D° NOT c-commanded by N° (`behindHorizonB`) -/
theorem unified_tree_derivation :
    closestGoalB treeUnaccDP T₀ Psr hasDFeatures = false ∧
    closestGoalB treeTransPossP T₀ Psr hasDFeatures = false ∧
    behindHorizonB treeCPUnaccDP C₀ Psr .N = true ∧
    behindHorizonB treeCPUnaccPossP C₀ Psr .N = true ∧
    behindHorizonB treeCPUnaccDP C₀ D₀ .N = false :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

end AttractClosest

end Phenomena.Possession.Studies.AissenPolian2025
