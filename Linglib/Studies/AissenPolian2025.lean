import Linglib.Fragments.Mayan.Tseltalan
import Linglib.Morphology.DM.NominalStructure
import Linglib.Syntax.Minimalist.Agree.Basic
import Linglib.Syntax.Minimalist.Probe.Profile
import Linglib.Syntax.Binding.SpecificityCondition
import Linglib.Features.InformationStructure
import Linglib.Features.WordOrder

/-!
# Aissen & Polian 2025: Possessor Extraction and Categorical Subject in Tseltalan
[aissen-polian-2025]

*Natural Language & Linguistic Theory* 43:63--113.

## Overview

Tseltalan languages (Tsotsil, Tseltal) have two possessor extraction
strategies — pied-piping and stranding — whose availability depends on
nominal size (= specificity) and intervention by A-positioned DPs.

The analysis rests on two independent mechanisms:

1. **Selective opacity** ([keine-2019]): N⁰ is a horizon for wh-probes
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
- Why extracted possessors are ALWAYS external (claim (3) on p. 65):
  follows from selective opacity — not stipulated

Stranding is further constrained by intervention: an A-positioned DP
(agent or S_A) between the possessor and T°'s [EPP:D] probe blocks
possessor raising via Attract Closest.

## ψ-Subject Constructions

A&P identify a family of constructions in which a possessor is interpreted
as ψ-subject (categorical-judgment subject in Spec,TP, [kuroda-1972]).
§5 focuses on three **intransitive unaccusative** cases:
predicative possession (§5.2), experiential collocations (§5.3), and
ordinary lexical unaccusatives (§5.4). §6.2 extends the analysis to
configurations where the ψ-subject possessor originates inside a PP:
path verbs (§6.2.1), locative existentials (§6.2.2), and two-argument
experiential collocations (§6.2.3). §7.1 further notes that even Psr-A
can serve as ψ-subject in broad-predicate expressions like *x's fleas
landed on me*. The `ψConstruction` enumeration below covers the §5
intransitive subset; §6.2 / §7.1 cases are noted but not enumerated.

## Predecessor Accounts and Comparative Engagement

A&P §4 contests **[little-2020a] / [little-2020b]**, the
proximate Ch'ol analysis that derives possessor-extraction asymmetries
from a Diesing-style specificity restriction combined with the Freezing
Principle (Object Shift of specific objects → frozen for Ā-subextraction).
A&P argue Little's account fails to extend to non-specific cases:
Ā-subextraction is blocked from non-specifics as well, so a blanket
nominal-opacity ban (selective opacity) is needed instead.

The escape-hatch view of [gavruseva-2000] (Spec,DP as left-edge
position parallel to Spec,CP) is the older predecessor view A&P reject:
their analysis derives extraction without any DP-internal subextraction
step. [aissen-1996] is the earlier Tsotsil pied-piping analysis;
[aissen-1999a] establishes that Tseltalan A's extract freely
(used in §6.2 to motivate why intervention is by A-position not
Ā-extraction). [coon-baier-levin-2021] on Mayan agent focus is
contested in §6.1 (the file currently does not formalize this).

[coon-henderson-2011] and [aissen-1987] are the two competing
analyses of the Tseltalan possessive applicative (control vs raising);
A&P adopt the raising analysis, which the file's `DProbeHead.appl` slot
implicitly assumes.

[heycock-doron-2003] on Hebrew broad subjects is A&P's primary
cross-linguistic typological precedent for ψ-subjects (cited p. 86 fn 22
alongside Tz'utujil, Chickasaw, Sinitic double-unaccusative).

## Integration Points

- `NominalPosition` / `PossessionType` from `NominalStructure.lean`
- `SpecificityCondition` from `Core/SpecificityCondition.lean`
- `JudgmentType` from `Discourse/InformationStructure.lean`
- `GramFunction`, `absPosition` from `Fragments/Mayan/Tseltalan.lean`
- `ABSPosition` from `Fragments/Mayan/Params.lean`
- `Probe.Profile`, `closestGoalB`, `behindHorizonB` from
  `Syntax/Minimalist/Agree.lean`; `SO` construction DSL (`SO.ofPlanar`,
  `SO.leafP`, `SO.nodeP`, `SO.lexLeaf`) from
  `Syntax/Minimalist/SyntacticObject/Build.lean`
-/

namespace AissenPolian2025

open Mayan (MarkerSet ABSPosition)
open Mayan.Tseltalan
open Morphology.DM

-- ============================================================================
-- § 1: Nominal Size and Specificity
-- ============================================================================

/-- Nominal projections in Tseltalan, determining extractability.
    [aissen-polian-2025] §3.2, (11)/(18): specific indefinites and
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
    [aissen-polian-2025] §3.2. -/
def NominalSize.IsSpecific : NominalSize → Prop
  | .dp    => True
  | .possP => False
  | .nP    => False

instance : DecidablePred NominalSize.IsSpecific := fun n => by
  cases n <;> unfold NominalSize.IsSpecific <;> infer_instance

-- ============================================================================
-- § 2: Argument Structure Classes (Theoretical Classification)
-- ============================================================================

/-- Clause types in Tseltalan, classified by whether the verb projects
    an external argument (vP layer). This is a theoretical classification
    from Minimalist syntax, used here to derive intervention effects.

    [aissen-polian-2025] (9):
    - Unaccusative: no vP layer (sole argument is complement of V)
    - Transitive: vP layer with agent in Spec,vP
    - Unergative: vP layer with agentive S in Spec,vP -/
inductive ArgumentStructureClass where
  | unaccusative  -- no vP layer (existentials, unaccusatives)
  | transitive    -- vP layer with agent
  | unergative    -- vP layer with agentive intransitive subject
  deriving DecidableEq, Repr

/-- Whether a clause type projects a vP layer (= has an external argument
    position that could host an intervening DP).
    [aissen-polian-2025] (9): transitives and unergatives have vP;
    unaccusatives do not. -/
def ArgumentStructureClass.HasVP : ArgumentStructureClass → Prop
  | .unaccusative => False
  | .transitive   => True
  | .unergative   => True

instance : DecidablePred ArgumentStructureClass.HasVP := fun c => by
  cases c <;> unfold ArgumentStructureClass.HasVP <;> infer_instance

/-- Unaccusatives lack a vP layer; transitives and unergatives have one.
    The positive directions are immediate from the def; this lemma names
    the negative direction for stranding-intervention proofs to consume. -/
theorem unaccusative_no_vP : ¬ ArgumentStructureClass.unaccusative.HasVP := id

-- ============================================================================
-- § 3: Probe Types and Selective Opacity
-- ============================================================================

/-- Probe types that trigger movement in Tseltalan.
    [aissen-polian-2025] §3.1, (10):

    - **[EPP:D]** on T° and Appl°: triggers A-movement of a DP to
      the probe's specifier. T° and Appl° take rightside specifiers.
    - **[EPP:WH]** on D° (secondary wh-movement) and C° (primary
      wh-movement): triggers Ā-movement of a wh-phrase. -/
inductive ProbeType where
  | dProbe   -- [EPP:D] on T° or Appl° (A-movement)
  | whProbe  -- [EPP:WH] on D° or C° (Ā-movement)
  deriving DecidableEq, Repr

/-- **Selective opacity** ([keine-2019], [aissen-polian-2025] (33)):
    N⁰ is a horizon for wh-probes on C°. Elements inside the extended
    projection of N⁰ are invisible to wh-probes, blocking Ā-subextraction.

    Crucially, this does NOT apply to D-probes: A-movement of a possessor
    DP out of a nominal is permitted. The opacity is *selective* — it
    depends on the probe type, not on nominal size.

    `[wh]_{C°} -|| N` (A&P's (33)) -/
def SelectivelyOpaque : ProbeType → Prop
  | .whProbe => True   -- nominals always opaque to wh-probes
  | .dProbe  => False  -- nominals transparent to D-probes

instance : DecidablePred SelectivelyOpaque := fun p => by
  cases p <;> unfold SelectivelyOpaque <;> infer_instance

theorem wh_probes_blocked : SelectivelyOpaque .whProbe := trivial
theorem d_probes_pass : ¬ SelectivelyOpaque .dProbe := id

/-- Ā-subextraction from within a nominal is impossible. Derived from
    selective opacity: wh-probes cannot see into nominals, regardless of
    nominal size. The proposition does not depend on `NominalSize` —
    [aissen-polian-2025] (33) is the universal nominal-opacity ban
    A&P argue against the size-relative Diesing/Freezing predecessor of
    [little-2020a] / [little-2020b]. -/
def CanĀSubextract : Prop :=
  ¬ SelectivelyOpaque .whProbe

instance : Decidable CanĀSubextract := by unfold CanĀSubextract; infer_instance

theorem subextraction_impossible : ¬ CanĀSubextract := fun h => h trivial

-- ────────────────────────────────────────────────────────────────
-- ProbeType ↔ Probe.Profile bridge
-- ────────────────────────────────────────────────────────────────

/-- Convert a `ProbeType` to a `Probe.Profile` from [keine-2019].

    - `dProbe` (A-movement, on T°/Appl°) maps to an A-probe on T°
      with horizon C — the same profile as `keineAProbe`.
    - `whProbe` (Ā-movement, on D°/C°) maps to an Ā-probe on C°
      with no horizon — the same profile as `keineĀProbe`. -/
def ProbeType.toProfile : ProbeType → Minimalist.Probe.Profile
  | .dProbe  => Minimalist.keineAProbe
  | .whProbe => Minimalist.keineĀProbe

/-- D-probes are A-probes in Keine's classification. -/
theorem dProbe_is_A : ProbeType.dProbe.toProfile.isAProbe = true := by decide

/-- Wh-probes are Ā-probes in Keine's classification. -/
theorem whProbe_is_Ā : ProbeType.whProbe.toProfile.isĀProbe = true := by decide

/-- Selective opacity is consistent with Keine's transparency:
    wh-probes (Ā, no horizon) are transparent to all clause types
    including CP, while d-probes (A, horizon C) cannot search into
    CP or TP.

    The `selectivelyOpaque` predicate captures a different facet —
    opacity of *nominals* (N° as horizon), not opacity of *clauses*.
    But both derive from the same underlying mechanism: probes
    differ in their horizons. -/
theorem probe_type_keine_consistency :
    -- D-probes: opaque to CP (can't A-move out of finite clause)
    ProbeType.dProbe.toProfile.transparentTo .C = false ∧
    -- Wh-probes: transparent to CP (can Ā-move out of finite clause)
    ProbeType.whProbe.toProfile.transparentTo .C = true := by decide

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

    Derived from `IsSpecific`: D-layer shielding ↔ specificity. -/
def DLayerShields (size : NominalSize) : Prop :=
  size.IsSpecific

instance : DecidablePred DLayerShields := fun s => by
  unfold DLayerShields; infer_instance

theorem dp_shields : DLayerShields .dp := trivial
theorem possP_no_shield : ¬ DLayerShields .possP := id
theorem nP_no_shield : ¬ DLayerShields .nP := id

-- ============================================================================
-- § 5: Extraction Modes
-- ============================================================================

/-- Two possessor extraction strategies in Tseltalan.
    [aissen-polian-2025] §3. -/
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

    [aissen-polian-2025] §3.2. -/
def ExtractionAvailable (mode : ExtractionMode) (size : NominalSize) : Prop :=
  match mode with
  | .piedPiping => size.IsSpecific      -- only DPs can undergo wh-movement
  | .stranding  => ¬ DLayerShields size  -- no D-layer → possessor reachable

instance : ∀ m s, Decidable (ExtractionAvailable m s) := fun m s => by
  cases m <;> unfold ExtractionAvailable <;> infer_instance

/-- Pied-piping requires specificity (D projection). -/
theorem piedPiping_requires_specific :
    ExtractionAvailable .piedPiping .dp ∧
    ¬ ExtractionAvailable .piedPiping .possP ∧
    ¬ ExtractionAvailable .piedPiping .nP := ⟨trivial, id, id⟩

/-- Stranding requires non-specificity (no D-layer shielding). -/
theorem stranding_requires_nonspecific :
    ¬ ExtractionAvailable .stranding .dp ∧
    ExtractionAvailable .stranding .possP ∧
    ExtractionAvailable .stranding .nP :=
  ⟨fun h => h trivial, id, id⟩

/-- Every nominal size admits at least one extraction mode.
    Possessor extraction is never fully blocked — the available
    strategy depends on specificity. -/
theorem extraction_always_possible (size : NominalSize) :
    ExtractionAvailable .piedPiping size ∨
    ExtractionAvailable .stranding size := by
  cases size
  · exact Or.inl trivial
  · exact Or.inr id
  · exact Or.inr id

/-- **Complementary distribution**: pied-piping and stranding are
    mutually exclusive — exactly one is available for each nominal size.
    Specific nominals admit only pied-piping; non-specific nominals
    admit only stranding. Both reduce to `IsSpecific`. -/
theorem extraction_complementary (size : NominalSize) :
    ExtractionAvailable .piedPiping size ↔
    ¬ ExtractionAvailable .stranding size := by
  cases size <;>
    simp only [ExtractionAvailable, DLayerShields, NominalSize.IsSpecific,
      not_not, not_true_eq_false, not_false_eq_true]

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
theorem extracted_always_external : ¬ CanĀSubextract :=
  subextraction_impossible

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

/-- Convergence: both A&P's D-layer shielding and the Specificity Condition
    (see `Syntax.Binding.SpecificityCondition`) predict that specific DPs resist
    possessor extraction by stranding/binding into the DP.

    Divergence: A&P predict pied-piping IS available for specific DPs
    (whole DP moves, no subextraction); the Specificity Condition blocks
    ALL operator binding into specific DPs. The two constraints operate
    at different levels — D-layer shielding targets A-movement (D-probes),
    the Specificity Condition targets operator-variable binding. -/
theorem specificity_convergence_on_stranding :
    ¬ ExtractionAvailable .stranding .dp ∧
    Syntax.Binding.SpecificityCondition.blocked .whTrace .definite :=
  ⟨fun h => h trivial, rfl⟩

theorem specificity_divergence_on_piedpiping :
    ExtractionAvailable .piedPiping .dp ∧
    Syntax.Binding.SpecificityCondition.blocked .whTrace .definite :=
  ⟨trivial, rfl⟩

-- ============================================================================
-- § 9: Categorical Judgment (ψ-Subject)
-- ============================================================================

open Features.InformationStructure

/-- The grammatical function of a ψ-subject.
    ψ-subjects are always intransitive subjects — they raise from
    unaccusative clauses where the sole argument is S_O (patientive).

    [aissen-polian-2025] §5, Table 1: all ψ-subject constructions
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
    JudgmentType.categorical.HasψSubject := rfl

theorem thetic_no_ψSubject :
    ¬ JudgmentType.thetic.HasψSubject := by decide

/-- A ψ-subject must be specific (= project to DP) to raise to Spec,TP.
    [aissen-polian-2025] §5.1, p. 85: "the subject of a clause
    which expresses a categorical judgment cannot be non-specific."

    This connects the specificity system to the ψ-subject system:
    T°'s [EPP:D] probe searches for a DP. If the highest nominal in
    T°'s domain is non-specific (PossP/nP), it is not a DP, and T°'s
    probe passes over it. Only a specific DP satisfies the [EPP:D]
    requirement and raises to Spec,TP as ψ-subject. -/
def CanBeψSubject (size : NominalSize) : Prop :=
  size.IsSpecific

instance : DecidablePred CanBeψSubject := fun s => by
  unfold CanBeψSubject; infer_instance

theorem specific_can_be_ψSubject : CanBeψSubject .dp := trivial
theorem nonspecific_cannot_be_ψSubject_possP :
    ¬ CanBeψSubject .possP := id
theorem nonspecific_cannot_be_ψSubject_nP :
    ¬ CanBeψSubject .nP := id

-- ============================================================================
-- § 10: ψ-Subject Constructions
-- ============================================================================

/-- The three intransitive-unaccusative ψ-subject constructions of
    [aissen-polian-2025] §5. **Not exhaustive**: §6.2 adds path
    verbs, locative existentials, and two-argument experiential
    collocations (where the ψ-subject possessor originates inside a
    PP — see `ψPPConstruction` below); §7.1 admits Psr-A as ψ-subject
    in broad-predicate expressions like *x's fleas landed on me* (not
    enumerated here, as those are transitive). p. 91 fn 29 / p. 102
    fn 34 also note transitive/causative versions of experiential
    collocations where the possessor externalizes to Spec,ApplP rather
    than Spec,TP — by definition not ψ-subject constructions. -/
inductive ψConstruction where
  /-- Predicative possession: 'X has Y' via existential construction
      (Tsotsil *oy*, Tseltal *ay*). ψ-subject = possessor of pivot.
      Structure (44): [TP T° [VP V° PossP]] — V° is the existential. -/
  | predicativePossession
  /-- Experiential collocation (intransitive, §5.3): 'X is angry'
      (lit: 'x's head gets mixed up'). ψ-subject = experiencer-possessor.
      Structure (52): [TP T° [VP V° PossP]]. -/
  | experientialCollocation
  /-- Lexical unaccusative (§5.4): 'X's money was lost.'
      ψ-subject = possessor of theme (S_O), present only on the
      non-specific reading where PossP remains. -/
  | lexicalUnaccusative
  deriving DecidableEq, Repr

/-- Additional ψ-subject configurations from [aissen-polian-2025]
    §6.2 in which the ψ-subject possessor originates as the object of
    an internal PP (Psr-OP) rather than as a possessor of the verb's
    direct internal argument. The clauses are still unaccusative (no vP),
    but the ψ-subject reaches Spec,TP via raising from inside a PP rather
    than a PossP. These are ψ-subjects in the same sense as `ψConstruction`
    above; they are kept in a separate enumeration only because the
    geometry of extraction (PP-internal origin, locative co-argument)
    differs from the simple V° + PossP cases of §5. -/
inductive ψPPConstruction where
  /-- Path verb (§6.2.1): intransitive motion verb (V° + Theme + PP_loc),
      e.g. (75a) *Mach'a och wakax [ta s-na]?* 'Who had a cow enter
      his house?' — ψ-subject = possessor of locative PP, raised over
      non-specific Theme. -/
  | pathVerb
  /-- Locative existential (§6.2.2): same predicative *oy*/*ay* as
      predicative possession but with PP rather than PossP, e.g. (77b)
      *Much'u oy ixim [ta s-na]?* 'Who has corn in his/her house?' —
      ψ-subject = possessor of locative PP, Theme is non-specific. -/
  | locativeExistential
  /-- Two-argument experiential collocation (§6.2.3): experiencer
      introduced in PP whose object is the experiential PossP, e.g.
      (81) *Mach'u k'ux-at [ta y-o'tan]?* 'Who loves you?' (lit. 'who
      are you painful in their heart?') — ψ-subject = possessor of
      PP-experiencer, can extract regardless of Theme specificity. -/
  | twoArgExperiential
  deriving DecidableEq, Repr

/-- The clause type for every §5 ψ-construction is unaccusative
    ([aissen-polian-2025] p. 83 verbatim: "three unaccusative
    constructions"). The function is constant over its domain — the
    constraint is intrinsic to membership in `ψConstruction`. -/
def ψConstruction.clauseType (_ : ψConstruction) : ArgumentStructureClass :=
  .unaccusative

/-- Whether pied-piping is possible for a given ψ-construction.

    In predicative possession (§5.2, (48a/48b)) and experiential
    collocations (§5.3, (55a/55b)), the possessor and possessum do NOT
    form a constituent that can undergo wh-movement: the predicative
    element (*oy*/*ay*, or the verb) intervenes. Only stranding works.

    In lexical unaccusatives (§5.4, (62a/62b)), the entire possessive
    phrase IS the internal argument and can be pied-piped. -/
def ψConstruction.PiedPipingPossible : ψConstruction → Prop
  | .predicativePossession  => False  -- (48b): *[Mach'u x-chitom] oy t?
  | .experientialCollocation => False  -- (55b): *[Much'u s-jol] kap-em t?
  | .lexicalUnaccusative    => True   -- (62a): [Mach'a s-tak'in] ch'ay t?

instance : DecidablePred ψConstruction.PiedPipingPossible := fun c => by
  cases c <;> unfold ψConstruction.PiedPipingPossible <;> infer_instance

theorem pred_poss_no_piedpiping :
    ¬ ψConstruction.predicativePossession.PiedPipingPossible := id
theorem exp_coll_no_piedpiping :
    ¬ ψConstruction.experientialCollocation.PiedPipingPossible := id
theorem lex_unacc_piedpiping_ok :
    ψConstruction.lexicalUnaccusative.PiedPipingPossible := trivial

/-- Every §5 ψ-construction is structurally unaccusative (true by
    the type signature of `clauseType`). -/
theorem ψ_constructions_unaccusative (c : ψConstruction) :
    c.clauseType = .unaccusative := rfl

/-- Every §5 ψ-construction lacks a vP layer. Derived from
    `ψ_constructions_unaccusative` and `unaccusative_no_vP`. -/
theorem ψ_constructions_no_vP (c : ψConstruction) :
    ¬ c.clauseType.HasVP := id

/-- The ψ-subject grammatical function in every §5 construction is S_O
    ([aissen-polian-2025] §5: in all three, the ψ-subject raises
    from an unaccusative-internal-argument position). -/
def ψConstruction.ψSubjectFunction (_ : ψConstruction) : GramFunction :=
  .S_O

/-- Every §5 ψ-construction assigns S_O to its ψ-subject. -/
theorem ψ_constructions_all_S_O (c : ψConstruction) :
    c.ψSubjectFunction = .S_O := rfl

/-- ψ-subject agreement in every §5 construction is Set B, derived from
    the S_O grammatical function via the shared Tseltalan paradigm. -/
theorem ψ_constructions_setB (c : ψConstruction) :
    c.ψSubjectFunction.markerSet = .setB := rfl

/-! ### §6.2 PP-internal ψ-subjects -/

/-- §6.2 PP-internal ψ-constructions are all unaccusative as well: path
    verbs, locative existentials, and two-arg experiential collocations
    project no vP layer (the Theme/co-argument may sit in VP but the
    ψ-subject possessor raises from inside a PP). -/
def ψPPConstruction.clauseType (_ : ψPPConstruction) : ArgumentStructureClass :=
  .unaccusative

/-- For PP-internal ψ-subjects the extracted possessor is Psr-OP
    (possessor of object of preposition). The §6.2 cases differ from §5
    in that the ψ-subject originates inside a PP rather than a PossP,
    but the grammatical function on the verb tracks the Theme not the
    extracted possessor. We do not assign a `GramFunction` here for the
    extracted Psr-OP because Psr-OP has no per-verb agreement slot in
    the Tseltalan paradigm. -/
theorem ψ_pp_constructions_unaccusative (c : ψPPConstruction) :
    c.clauseType = .unaccusative := rfl

theorem ψ_pp_constructions_no_vP (c : ψPPConstruction) :
    ¬ c.clauseType.HasVP := id

-- ============================================================================
-- § 11: Intervention Effects (Table 4)
-- ============================================================================

/-- Functional heads that carry [EPP:D] probes triggering A-movement.
    [aissen-polian-2025] §4.2, §6, Table 4. -/
inductive DProbeHead where
  | t     -- T° in all clause types
  | appl  -- Appl° in applicative constructions
  deriving DecidableEq, Repr

/-- Does a clause type have an A-positioned DP that could intervene
    between a given probe and a lower possessor?

    Derived from `ArgumentStructureClass.HasVP` for T° probes: if there is a vP
    layer, its specifier hosts an A-positioned DP (agent or S_A).
    For Appl° probes, intervention occurs when Spec,ApplP is filled
    by a thematic applied argument (goal, recipient, etc.). -/
def HasIntervener (head : DProbeHead) (ct : ArgumentStructureClass)
    (thematicAppl : Bool) : Prop :=
  match head with
  | .t    => ct.HasVP
  | .appl => thematicAppl = true

instance : ∀ h c ta, Decidable (HasIntervener h c ta) := fun h c ta => by
  cases h <;> unfold HasIntervener <;> infer_instance

/-- Possessor stranding is blocked when an A-positioned DP intervenes
    between the [EPP:D] probe and the possessor.
    Pied-piping is unaffected: the whole DP moves to Spec,CP via
    wh-probe, bypassing A-positions entirely. -/
def InterventionBlocks (head : DProbeHead) (ct : ArgumentStructureClass)
    (mode : ExtractionMode) (thematicAppl : Bool := false) : Prop :=
  match mode with
  | .stranding  => HasIntervener head ct thematicAppl
  | .piedPiping => False

instance : ∀ h c m ta, Decidable (InterventionBlocks h c m ta) := fun h c m ta => by
  cases m <;> unfold InterventionBlocks <;> infer_instance

/-- An intervention datum for Table 4. -/
structure InterventionDatum where
  probe : DProbeHead
  clauseType : ArgumentStructureClass
  mode : ExtractionMode
  /-- Is Spec,ApplP filled by a thematic applied argument? -/
  thematicAppl : Bool
  /-- Is extraction blocked? -/
  blocked : Bool
  deriving DecidableEq, Repr

/-- A re-tabulation of [aissen-polian-2025] Table 4 (p. 103) along a
    different axis. A&P's Table 4 has 10 rows indexed by `(Probe, A-Intervener,
    Clause Type, Intended Goal)` with a yes/no/yes-no `Ā-movement?` column;
    it covers Psr-S_O, Psr-O, and Psr-OP goals. Our table re-indexes by
    `(Probe, Clause Type, Mode, ThematicAppl)` and tracks `blocked` per
    extraction mode. Only the `Probe × Clause Type × ThematicAppl` rows
    that fall out of `InterventionBlocks` are captured here; the Psr-OP /
    locative-PP rows from A&P's Table 4 (rows for path verbs (75), locative
    existentials (77b/78), PP-island (67-69)) are not yet modelled because
    the file currently formalizes only PossP-internal possessors as goals.
    The `ψPPConstruction` enumeration above marks the §6.2 cases as a
    deferred extension target.

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

/-- Table 4 is derivable: every cell matches `InterventionBlocks`. -/
theorem table4_derived :
    table4.all (λ d => d.blocked ==
      decide (InterventionBlocks d.probe d.clauseType d.mode d.thematicAppl))
    = true := by decide

/-- Pied-piping is never blocked by intervention (Ā-movement
    bypasses A-positions). -/
theorem piedPiping_never_blocked (head : DProbeHead) (ct : ArgumentStructureClass)
    (ta : Bool) :
    ¬ InterventionBlocks head ct .piedPiping ta := id

/-- For T° probes, stranding is blocked iff there is a vP layer. -/
theorem t_stranding_blocked_iff_vP (ct : ArgumentStructureClass) :
    InterventionBlocks .t ct .stranding ↔ ct.HasVP := by
  cases ct <;>
    simp only [InterventionBlocks, HasIntervener, ArgumentStructureClass.HasVP]

/-- For Appl° probes, stranding is blocked iff Spec,ApplP is filled
    by a thematic applied argument. -/
theorem appl_stranding_blocked_iff_thematic (ct : ArgumentStructureClass) (ta : Bool) :
    InterventionBlocks .appl ct .stranding ta ↔ ta = true := by
  cases ta <;> simp only [InterventionBlocks, HasIntervener]

-- ============================================================================
-- § 12: Full Extraction Availability
-- ============================================================================

/-! ### Specifier directionality (deferred)

[aissen-polian-2025] §3.1, (10) parameterizes specifier direction
per functional head: the Tseltalan default is leftside, but T°, Appl°,
and possibly Poss° take rightside specifiers (yielding post-verbal
ψ-subjects and external possessors). The previous version of this file
defined `inductive SpecDirection` + `tseltalanTSpec` / `tseltalanApplSpec`
inline, but these were unused and constituted Fragment-style typological
data outside `Fragments/`. When a downstream consumer needs them, they
should land in `Fragments/Mayan/Tseltalan.lean` (subgroup-shared) or
in `Core/Word.lean` next to `HeadDirection` (the analogous head-vs-
complement axis), not here. -/


/-- Combining extraction mode availability (§4) with intervention
    effects (§10): is possessor extraction ultimately possible for
    a given nominal size, clause type, and probe? -/
def CanExtractPossessor (size : NominalSize) (head : DProbeHead)
    (ct : ArgumentStructureClass) (mode : ExtractionMode)
    (thematicAppl : Bool := false) : Prop :=
  ExtractionAvailable mode size ∧
    ¬ InterventionBlocks head ct mode thematicAppl

instance : ∀ s h c m ta, Decidable (CanExtractPossessor s h c m ta) :=
  fun _ _ _ _ _ => by unfold CanExtractPossessor; infer_instance

/-- In unaccusative clauses via T°, both modes are available. -/
theorem unaccusative_both_modes :
    CanExtractPossessor .dp .t .unaccusative .piedPiping ∧
    CanExtractPossessor .possP .t .unaccusative .stranding ∧
    CanExtractPossessor .nP .t .unaccusative .stranding := by decide

/-- In transitive clauses via T°, only pied-piping works. -/
theorem transitive_only_piedpiping :
    CanExtractPossessor .dp .t .transitive .piedPiping ∧
    ¬ CanExtractPossessor .possP .t .transitive .stranding ∧
    ¬ CanExtractPossessor .nP .t .transitive .stranding := by decide

/-- Via Appl° raising applicative (no thematic arg), stranding works. -/
theorem raising_appl_stranding :
    CanExtractPossessor .possP .appl .transitive .stranding false ∧
    CanExtractPossessor .nP .appl .transitive .stranding false := by decide

/-- Via Appl° thematic applicative (Goal fills Spec,ApplP), blocked. -/
theorem thematic_appl_blocked :
    ¬ CanExtractPossessor .possP .appl .transitive .stranding true ∧
    ¬ CanExtractPossessor .nP .appl .transitive .stranding true := by decide

/-- ψ-subject constructions (all unaccusative) permit both extraction
    modes via T°. -/
theorem ψ_constructions_permit_both_modes (c : ψConstruction) :
    CanExtractPossessor .dp .t c.clauseType .piedPiping ∧
    CanExtractPossessor .possP .t c.clauseType .stranding ∧
    CanExtractPossessor .nP .t c.clauseType .stranding := by
  cases c <;> decide

-- ============================================================================
-- § 13: Table 2 — Psr-S_O vs Psr-O Extraction Asymmetry
-- ============================================================================

/-- Table 2 of [aissen-polian-2025] (p. 77): possessor extraction
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
    CanExtractPossessor .possP .t .unaccusative .stranding ∧
    CanExtractPossessor .dp .t .unaccusative .piedPiping := by decide

theorem table2_psr_O :
    ¬ CanExtractPossessor .possP .t .transitive .stranding ∧
    CanExtractPossessor .dp .t .transitive .piedPiping := by decide

/-- The stranding asymmetry between Psr-S_O and Psr-O reduces to
    whether the clause type has a vP layer. -/
theorem stranding_asymmetry_is_vP :
    CanExtractPossessor .possP .t .unaccusative .stranding ∧
    ¬ CanExtractPossessor .possP .t .transitive .stranding := by decide

-- ============================================================================
-- § 14: Bridge to Ergativity
-- ============================================================================

/-- Tseltalan is LOW-ABS: absolutive agreement follows the verb stem.
    [aissen-polian-2025] p. 97 quotes [aissen-1999a] and
    [polian-2013] p. 272: "A's extract freely" — there are no
    syntactic ergativity effects in Tseltalan. The LOW-ABS / HIGH-ABS
    parameterization (whether Infl° or v° licenses absolutive case) is
    associated with a robust extraction-asymmetry generalization in the
    Mayan literature: HIGH-ABS languages exhibit syntactic ergativity
    (cf. [coon-mateo-pedro-preminger-2014]); LOW-ABS languages do
    not. The shared `Mayan.Tseltalan.absPosition` constant is
    the per-subgroup source of truth, definitionally equal to the
    Tsotsil and Tseltal per-language values.

    The intervention effects in Table 4 are NOT about Ā-movement being
    blocked by A-positioned DPs (as in HIGH-ABS/syntactically ergative
    languages). Rather, they are about A-movement (possessor raising)
    being blocked by a closer A-positioned DP, preventing the possessor
    from reaching an external position from which it could Ā-extract. -/
abbrev tseltalanABSPosition : ABSPosition := Mayan.Tseltalan.absPosition

theorem tseltalan_is_low_abs :
    tseltalanABSPosition = .low := rfl

/-- LOW-ABS languages have ABS=DEF (v° assigns case to transitive
    object), not ABS=NOM (Infl° assigns case). -/
theorem tseltalan_case_locus :
    Mayan.toCaseLocus tseltalanABSPosition =
    Mayan.CaseLocus.absDef := rfl

-- ============================================================================
-- § 15: Tree-Geometric Derivation (Attract Closest)
-- ============================================================================

section AttractClosest

open Minimalist
open RootedTree

/-! ### Attract Closest on Concrete Trees

The boolean functions `dLayerShields`, `hasIntervener`, and
`canExtractPossessor` above capture the paper's predictions but
**stipulate** them directly. Here we **derive** them from Attract
Closest applied to concrete `SyntacticObject` trees
([aissen-polian-2025] (9a-c)), using `closestGoalB` from
`Minimalist.Agree`.

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
    (possessor DPs, D° heads, agent DPs) are potential goals.

    Reads the root token via `SO.getLIToken`. Only leaf SOs carry a
    token; internal (`SO.node`) nodes and traces return `none` and are
    not D-bearing (no structural-position-dependent feature lookup is
    needed). -/
private def hasDFeatures (s : SyntacticObject) : Bool :=
  match s.getLIToken with
  | some tok => tok.item.outerCat == .D
  | none => false

/-! ### Leaf Tokens and Nodes

Concrete trees are built **planar-first** (`SO.ofPlanar`/`SO.nodeP`/`SO.leafP`)
because Merge (`SO.node`) is noncomputable; `closestGoalB`/`behindHorizonB` then
reduce under `decide`. Each leaf `SO` is `SO.lexLeaf` of its token, and the trees
reference the same tokens via `SO.leafP` so the two match definitionally. -/

private def tT₀  : LIToken := ⟨.simple .T [], 1⟩   -- T° head ([EPP:D] probe)
private def tV₀  : LIToken := ⟨.simple .V [], 2⟩   -- V° (lexical verb)
private def tv₀  : LIToken := ⟨.simple .v [], 3⟩   -- v° (introduces agent)
private def tPsr : LIToken := ⟨.simple .D [], 4⟩   -- Possessor DP (D-bearing)
private def tPsm : LIToken := ⟨.simple .N [], 5⟩   -- Possessum (not D-bearing)
private def tD₀  : LIToken := ⟨.simple .D [], 6⟩   -- D° head of specific nominal
private def tAgt : LIToken := ⟨.simple .D [], 7⟩   -- Agent DP (D-bearing)

private def T₀  : SyntacticObject := SO.lexLeaf tT₀
private def V₀  : SyntacticObject := SO.lexLeaf tV₀
private def v₀  : SyntacticObject := SO.lexLeaf tv₀
private def Psr : SyntacticObject := SO.lexLeaf tPsr
private def Psm : SyntacticObject := SO.lexLeaf tPsm
private def D₀  : SyntacticObject := SO.lexLeaf tD₀
private def Agt : SyntacticObject := SO.lexLeaf tAgt

/-! ### Clause Trees ([aissen-polian-2025] (9a-c))

(9a) Unaccusative: `[TP T° [VP V° OBJECT]]`
     No vP layer — sole argument is complement of V.

(9b) Transitive: `[TP T° [vP Agent [v' v° [VP V° OBJECT]]]]`
     Agent in Spec,vP — creates potential intervener.

Object is PossP (non-specific) or DP (specific). -/

-- Non-specific possessive object: [PossP Psr Psm]
private def possPp : RoseTree SOLabel := SO.nodeP (SO.leafP tPsr) (SO.leafP tPsm)

-- Specific possessive object: [DP D° [PossP Psr Psm]]
private def dpObjp : RoseTree SOLabel := SO.nodeP (SO.leafP tD₀) possPp

-- (9a) Unaccusative + non-specific: [TP T° [VP V° [PossP Psr Psm]]]
private def treeUnaccPossP : SyntacticObject :=
  SO.ofPlanar (SO.nodeP (SO.leafP tT₀) (SO.nodeP (SO.leafP tV₀) possPp))

-- (9a') Unaccusative + specific: [TP T° [VP V° [DP D° [PossP Psr Psm]]]]
private def treeUnaccDP : SyntacticObject :=
  SO.ofPlanar (SO.nodeP (SO.leafP tT₀) (SO.nodeP (SO.leafP tV₀) dpObjp))

-- (9b) Transitive + non-specific:
-- [TP T° [vP Agt [v' v° [VP V° [PossP Psr Psm]]]]]
private def treeTransPossP : SyntacticObject :=
  SO.ofPlanar (SO.nodeP (SO.leafP tT₀)
    (SO.nodeP (SO.leafP tAgt)
      (SO.nodeP (SO.leafP tv₀)
        (SO.nodeP (SO.leafP tV₀) possPp))))

-- (9b') Transitive + specific:
-- [TP T° [vP Agt [v' v° [VP V° [DP D° [PossP Psr Psm]]]]]]
private def treeTransDP : SyntacticObject :=
  SO.ofPlanar (SO.nodeP (SO.leafP tT₀)
    (SO.nodeP (SO.leafP tAgt)
      (SO.nodeP (SO.leafP tv₀)
        (SO.nodeP (SO.leafP tV₀) dpObjp))))

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

/-- D-layer shielding: tree geometry matches `DLayerShields .dp`. -/
theorem bridge_dLayer_dp :
    closestGoalB treeUnaccDP T₀ Psr hasDFeatures = false ∧
    DLayerShields .dp := ⟨by decide, trivial⟩

/-- No D-layer for PossP: tree geometry matches `DLayerShields .possP`. -/
theorem bridge_no_dLayer_possP :
    closestGoalB treeUnaccPossP T₀ Psr hasDFeatures = true ∧
    ¬ DLayerShields .possP := ⟨by decide, id⟩

/-- Agent intervention: tree geometry matches `HasIntervener .t .transitive`. -/
theorem bridge_intervention_trans :
    closestGoalB treeTransPossP T₀ Psr hasDFeatures = false ∧
    HasIntervener .t .transitive false := ⟨by decide, trivial⟩

/-- No intervention in unaccusative: tree geometry matches
    `HasIntervener .t .unaccusative`. -/
theorem bridge_no_intervention_unacc :
    closestGoalB treeUnaccPossP T₀ Psr hasDFeatures = true ∧
    ¬ HasIntervener .t .unaccusative false := ⟨by decide, id⟩

-- ============================================================================
-- § 16: Selective Opacity from Tree Geometry (N-Horizons)
-- ============================================================================

/-! ### Selective Opacity as a Tree Constraint

Selective opacity ([keine-2019], [aissen-polian-2025] (33))
states that N° is a horizon for wh-probes: C°'s [EPP:WH] probe
cannot see elements c-commanded by N° (= inside the nominal's
lexical projection). Here we derive this from `behindHorizonB`
applied to concrete trees.

The key geometric fact: in `[PossP Psr N°]`, N° and Psr are sisters,
so N° c-commands Psr. This makes Psr invisible to any probe for
which N° is a horizon. But D° (sister of PossP, NOT c-commanded by
N°) remains visible — which is why pied-piping works.

Together with § 15 (Attract Closest), both pillars of A&P's analysis
are now derived from tree geometry:
- **D-layer shielding / intervention** → `closestGoalB` (§ 15)
- **Selective opacity** → `behindHorizonB` (§ 16)
-/

private def tC₀ : LIToken := ⟨.simple .C [], 8⟩
private def C₀ : SyntacticObject := SO.lexLeaf tC₀

-- Planar bodies of the unaccusative trees, reused under the CP node.
private def treeUnaccDPp : RoseTree SOLabel :=
  SO.nodeP (SO.leafP tT₀) (SO.nodeP (SO.leafP tV₀) dpObjp)
private def treeUnaccPossPp : RoseTree SOLabel :=
  SO.nodeP (SO.leafP tT₀) (SO.nodeP (SO.leafP tV₀) possPp)

-- CP wrapping unaccusative + DP:
-- [CP C° [TP T° [VP V° [DP D° [PossP Psr Psm]]]]]
private def treeCPUnaccDP : SyntacticObject :=
  SO.ofPlanar (SO.nodeP (SO.leafP tC₀) treeUnaccDPp)

-- CP wrapping unaccusative + PossP:
-- [CP C° [TP T° [VP V° [PossP Psr Psm]]]]
private def treeCPUnaccPossP : SyntacticObject :=
  SO.ofPlanar (SO.nodeP (SO.leafP tC₀) treeUnaccPossPp)

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
    D-probes IGNORE the horizon (`¬ SelectivelyOpaque .dProbe`).
    This is the "selective" in selective opacity: the same tree
    geometry produces different results for different probe types. -/
theorem horizon_present_but_dprobe_ignores :
    behindHorizonB treeUnaccPossP T₀ Psr .N = true ∧
    ¬ SelectivelyOpaque .dProbe := ⟨by decide, id⟩

/-! ### Bridge Theorems -/

/-- Selective opacity from tree geometry: the N-horizon blocks
    wh-subextraction of Psr from both DP and PossP nominals,
    agreeing with `CanĀSubextract` (which is size-independent). -/
theorem bridge_selective_opacity :
    behindHorizonB treeCPUnaccDP C₀ Psr .N = true ∧
    behindHorizonB treeCPUnaccPossP C₀ Psr .N = true ∧
    ¬ CanĀSubextract :=
  ⟨by decide, by decide, subextraction_impossible⟩

/-- D° visible despite N-horizon: pied-piping is available because
    D° is outside N°'s c-command domain. Agrees with
    `ExtractionAvailable .piedPiping .dp`. -/
theorem bridge_piedpiping_ok :
    behindHorizonB treeCPUnaccDP C₀ D₀ .N = false ∧
    ExtractionAvailable .piedPiping .dp := ⟨by decide, trivial⟩

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

end AissenPolian2025
