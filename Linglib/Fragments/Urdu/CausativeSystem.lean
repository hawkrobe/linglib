import Linglib.Theories.Semantics.Causation.Morphological

/-!
# Urdu Causative Construction System

@cite{hafeez-2025}

Urdu distinguishes at least 7 causative constructions tested in
@cite{hafeez-2025}'s acceptability rating study. Each construction is
sensitive to three semantic variables: **causer type** (IHCr/AHCr/NFCr),
**causee/affectee type** (ContrHCEAF/PhysImpHCEAF/PsychImpHCEAF/InanCEAF),
and **mediation** (direct/indirect).

## The 7 Constructions (Acceptability Study, Ch. 5)

| # | Construction | Abbrev | Complexity | Description |
|---|---|---|---|---|
| 1 | Lexical Ergative | LEX-ERG | lexical | Ergative case on causer NP (perfective) |
| 2 | Lexical Instrumental | LEX-INST | lexical | Instrumental case on causer NP |
| 3 | Lexical Dative | LEX-DAT | lexical | Dative case on highest-ranked NP |
| 4 | Morphological Causative Verb | MCV | morphological | -aa suffix, always mediated |
| 5 | Adverbial Causative | ADV | periphrastic | *keyoonkeh* 'because', *itni...keh* |
| 6 | Non-sentential Cause Adjunct | NCA | periphrastic | *wajah=se* 'because of' |
| 7 | Non-sentential Causer Adjunct | NCrA | periphrastic | Causer NP as adjunct |

## Semantic Prototypes (Table 25)

@cite{hafeez-2025} identifies hypothesized semantic prototypes for 5 of
the 7 constructions via acceptability rating peaks (>50% ceiling).
Prototypes use both positive ([+F]) and negative ([-F]) features:

- **LEX-ERG**: [+IHCr, +InanCEAF] — prototypical direct causation
- **LEX-INST**: [-IHCr, +InanCEAF] — accidental causer acting on object
- **MCV**: [+Mediation, +IHCr, +ContrHCEAF] — causation by command
- **NCrA**: [-InanCEAF, +NFCr] — natural force causer with human affectee
- **NCA**: [-InanCEAF, -NFCr] — human causer, human affectee
- **ADV**: [+InanCEAF] — broad acceptability, weaker prototype
- **LEX-DAT**: No prototype (default case, high acceptability across the board)

## Discourse Production (Ch. 6)

The discourse production study confirms key patterns:
- LEX-ERG preferred for [+InanCEAF, +IHCr] (53.7% production rate)
- NCrA used *exclusively* with natural force causers (categorical)
- IMP-CAUS-REL preferred for [+ContrHCEAF, +IHCr] (communication scenes)

## Bridges

- Each construction is typed as `CausativeConstruction` from
  `Theories/Semantics/Causation/MorphologicalCausation.lean`
- `prototype` field encodes Table 25 semantic prototypes using
  `presentCausers`/`absentCausers`/`presentCausees`/`absentCausees`
- Per-datum verification theorems check complexity, mediation,
  and restriction properties
- Key empirical generalizations are encoded as theorems
-/

namespace Fragments.Urdu.CausativeSystem

open Semantics.Causation.Morphological

-- ════════════════════════════════════════════════════
-- § 1. Construction Definitions
-- ════════════════════════════════════════════════════

/-- A construction entry bundles a `CausativeConstruction` with its
    empirically derived semantic prototype. -/
structure ConstructionEntry where
  construction : CausativeConstruction
  prototype : SemanticPrototype
  deriving DecidableEq, Repr

/-- Lexical Ergative (LEX-ERG): transitive/causative verb with ergative
    case on the causer NP in perfective aspect.
    Prototype: [+IHCr, +InanCEAF] — prototypical direct causation.
    This is Hopper & Thompson's (1980) prototypical transitive clause. -/
def lexErg : ConstructionEntry :=
  { construction :=
      { complexity := .lexical
        mediation := .direct
        causerRestriction := none
        causeeRestriction := none }
    prototype :=
      { presentCausers := [.intentionalHuman]
        absentCausers := []
        presentCausees := [.inanimate]
        absentCausees := []
        requiresMediation := some false } }

/-- Lexical Instrumental (LEX-INST): intransitive verb with instrumental
    case on the causer NP. The causer appears as an adjunct rather than
    a core argument.
    Prototype: [-IHCr, +InanCEAF] — non-intentional causer acting on
    inanimate affectee. -/
def lexInst : ConstructionEntry :=
  { construction :=
      { complexity := .lexical
        mediation := .direct
        causerRestriction := none
        causeeRestriction := none }
    prototype :=
      { presentCausers := []
        absentCausers := [.intentionalHuman]
        presentCausees := [.inanimate]
        absentCausees := []
        requiresMediation := some false } }

/-- Lexical Dative (LEX-DAT): causative verb with dative case on the
    highest-ranked NP.
    No semantic prototype identified — high acceptability across all
    scene types. @cite{hafeez-2025} suggests this may be a default
    case in Urdu, consistent with Van Valin (2018). -/
def lexDat : ConstructionEntry :=
  { construction :=
      { complexity := .lexical
        mediation := .direct
        causerRestriction := none
        causeeRestriction := none }
    prototype :=
      { presentCausers := []
        absentCausers := []
        presentCausees := []
        absentCausees := []
        requiresMediation := none } }

/-- Morphological Causative Verb (MCV): productive -aa suffix.
    Always involves mediation — the causer instructs a causee who
    performs the action.
    Prototype: [+Mediation, +IHCr, +ContrHCEAF] — causation by
    command/communication. -/
def mcv : ConstructionEntry :=
  { construction :=
      { complexity := .morphological
        mediation := .indirect
        causerRestriction := none
        causeeRestriction := none }
    prototype :=
      { presentCausers := [.intentionalHuman]
        absentCausers := []
        presentCausees := [.controllingHuman]
        absentCausees := []
        requiresMediation := some true } }

/-- Adverbial Causative (ADV): two clauses connected by *keyoonkeh*
    'because' or *itni...keh* 'so...that'.
    Prototype: [+InanCEAF] — weak prototype, broad acceptability. -/
def adv : ConstructionEntry :=
  { construction :=
      { complexity := .periphrastic
        mediation := .direct
        causerRestriction := none
        causeeRestriction := none }
    prototype :=
      { presentCausers := []
        absentCausers := []
        presentCausees := [.inanimate]
        absentCausees := []
        requiresMediation := none } }

/-- Non-sentential Cause Adjunct (NCA): phrasal cause adjunct marked
    with *wajah=se* 'because of', *par/pe* 'on', or *=se* INST.
    Matrix clause expresses the result; adjunct expresses the cause.
    Prototype: [-InanCEAF, -NFCr] — human causer with human affectee. -/
def nca : ConstructionEntry :=
  { construction :=
      { complexity := .periphrastic
        mediation := .direct
        causerRestriction := none
        causeeRestriction := none }
    prototype :=
      { presentCausers := []
        absentCausers := [.naturalForce]
        presentCausees := []
        absentCausees := [.inanimate]
        requiresMediation := none } }

/-- Non-sentential Causer Adjunct (NCrA): causer NP as adjunct phrase
    in a matrix clause predicting the result.
    Categorically restricted to natural force causers in
    @cite{hafeez-2025}'s data — human causers never trigger NCrA.
    Prototype: [-InanCEAF, +NFCr] — natural force causer with human
    affectee. -/
def ncrA : ConstructionEntry :=
  { construction :=
      { complexity := .periphrastic
        mediation := .direct
        causerRestriction := some .naturalForce
        causeeRestriction := none }
    prototype :=
      { presentCausers := [.naturalForce]
        absentCausers := []
        presentCausees := []
        absentCausees := [.inanimate]
        requiresMediation := none } }

/-- The acceptability study system as a list, from most compact to most
    analytic. -/
def system : List ConstructionEntry :=
  [lexErg, lexInst, lexDat, mcv, adv, nca, ncrA]

-- ════════════════════════════════════════════════════
-- § 2. Per-Datum Verification: Complexity
-- ════════════════════════════════════════════════════

theorem lexErg_lexical : lexErg.construction.complexity = .lexical := rfl
theorem lexInst_lexical : lexInst.construction.complexity = .lexical := rfl
theorem lexDat_lexical : lexDat.construction.complexity = .lexical := rfl
theorem mcv_morphological : mcv.construction.complexity = .morphological := rfl
theorem adv_periphrastic : adv.construction.complexity = .periphrastic := rfl
theorem nca_periphrastic : nca.construction.complexity = .periphrastic := rfl
theorem ncrA_periphrastic : ncrA.construction.complexity = .periphrastic := rfl

-- ════════════════════════════════════════════════════
-- § 3. Per-Datum Verification: Mediation
-- ════════════════════════════════════════════════════

/-- MCV always involves mediation (causer → causee → result). -/
theorem mcv_indirect : mcv.construction.mediation = .indirect := rfl

/-- Lexical constructions encode direct causation. -/
theorem lexErg_direct : lexErg.construction.mediation = .direct := rfl
theorem lexInst_direct : lexInst.construction.mediation = .direct := rfl
theorem lexDat_direct : lexDat.construction.mediation = .direct := rfl

-- ════════════════════════════════════════════════════
-- § 4. Semantic Prototype Verification
-- ════════════════════════════════════════════════════

/-- LEX-ERG prototype: [+IHCr]. -/
theorem lexErg_prototype_ihcr :
    lexErg.prototype.presentCausers = [.intentionalHuman] := rfl

/-- LEX-ERG prototype: [+InanCEAF]. -/
theorem lexErg_prototype_inan :
    lexErg.prototype.presentCausees = [.inanimate] := rfl

/-- LEX-INST prototype: [-IHCr] — excludes intentional causers. -/
theorem lexInst_prototype_no_ihcr :
    lexInst.prototype.absentCausers = [.intentionalHuman] := rfl

/-- LEX-INST prototype: [+InanCEAF]. -/
theorem lexInst_prototype_inan :
    lexInst.prototype.presentCausees = [.inanimate] := rfl

/-- MCV prototype requires mediation. -/
theorem mcv_prototype_mediation :
    mcv.prototype.requiresMediation = some true := rfl

/-- MCV prototype: [+IHCr, +ContrHCEAF]. -/
theorem mcv_prototype_command :
    mcv.prototype.presentCausers = [.intentionalHuman] ∧
    mcv.prototype.presentCausees = [.controllingHuman] := ⟨rfl, rfl⟩

/-- NCrA prototype: [+NFCr]. -/
theorem ncrA_prototype_nfcr :
    ncrA.prototype.presentCausers = [.naturalForce] := rfl

/-- NCrA prototype: [-InanCEAF] — requires human affectee. -/
theorem ncrA_prototype_no_inan :
    ncrA.prototype.absentCausees = [.inanimate] := rfl

/-- NCA prototype: [-NFCr, -InanCEAF] — human causer, human affectee. -/
theorem nca_prototype_human :
    nca.prototype.absentCausers = [.naturalForce] ∧
    nca.prototype.absentCausees = [.inanimate] := ⟨rfl, rfl⟩

/-- ADV prototype: [+InanCEAF] (weak). -/
theorem adv_prototype_inan :
    adv.prototype.presentCausees = [.inanimate] := rfl

/-- LEX-DAT has no prototype features (default case). -/
theorem lexDat_no_prototype :
    lexDat.prototype.presentCausers = [] ∧
    lexDat.prototype.absentCausers = [] ∧
    lexDat.prototype.presentCausees = [] ∧
    lexDat.prototype.absentCausees = [] ∧
    lexDat.prototype.requiresMediation = none := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Key Empirical Generalizations
-- ════════════════════════════════════════════════════

/-- **NCrA categorical restriction**: NCrA is restricted to natural
    force causers. No human causer (intentional or accidental) triggers
    NCrA in @cite{hafeez-2025}'s data. -/
theorem ncrA_requires_natural_force :
    ncrA.construction.causerRestriction = some .naturalForce := rfl

/-- **MCV encodes indirect causation**: The morphological causative
    verb (-aa suffix) always involves an intermediary causee. -/
theorem mcv_always_mediated :
    mcv.construction.mediation = .indirect := rfl

/-- **Lexical constructions are compact**: All three lexical
    constructions (ERG, INST, DAT) are at the lexical complexity level. -/
theorem all_lexical_compact :
    lexErg.construction.complexity = .lexical ∧
    lexInst.construction.complexity = .lexical ∧
    lexDat.construction.complexity = .lexical := ⟨rfl, rfl, rfl⟩

/-- **MCV sits between lexical and periphrastic**: Morphological
    complexity is strictly between the two. -/
theorem mcv_between :
    mcv.construction.complexity = .morphological ∧
    (lexErg.construction.complexity < mcv.construction.complexity) ∧
    (mcv.construction.complexity < adv.construction.complexity) := by
  exact ⟨rfl, trivial, trivial⟩

-- ════════════════════════════════════════════════════
-- § 6. Comrie's Generalization (Partial)
-- ════════════════════════════════════════════════════

/-- Lexical (compact, direct) vs. MCV (morphological, indirect):
    Comrie's monotonicity holds (direct.rank 0 ≤ indirect.rank 1). -/
theorem comrie_lexErg_mcv : comrie_monotone lexErg.construction mcv.construction := by
  intro _; decide

/-- Lexical (compact, direct) vs. periphrastic ADV (direct):
    Comrie's monotonicity holds (direct.rank 0 ≤ direct.rank 0). -/
theorem comrie_lexErg_adv : comrie_monotone lexErg.construction adv.construction := by
  intro _; decide

-- ════════════════════════════════════════════════════
-- § 7. System Properties
-- ════════════════════════════════════════════════════

/-- The system has exactly 7 constructions. -/
theorem system_size : system.length = 7 := rfl

/-- The system spans all three complexity levels. -/
theorem system_has_all_complexities :
    (system.map (·.construction.complexity)).elem .lexical = true ∧
    (system.map (·.construction.complexity)).elem .morphological = true ∧
    (system.map (·.construction.complexity)).elem .periphrastic = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- The system has both direct and indirect constructions. -/
theorem system_has_both_mediations :
    (system.map (·.construction.mediation)).elem .direct = true ∧
    (system.map (·.construction.mediation)).elem .indirect = true := by
  exact ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 8. Agentivity–Construction Correspondence
-- ════════════════════════════════════════════════════

/-- Full agentivity (IHCr) drives LEX-ERG selection:
    the prototype requires an intentional causer. -/
theorem full_agentivity_drives_lexErg :
    CauserType.agentivityDegree .intentionalHuman = .full ∧
    lexErg.prototype.presentCausers = [.intentionalHuman] := ⟨rfl, rfl⟩

/-- Non-agentive causer (NFCr) drives NCrA selection:
    NCrA is categorically restricted to natural force. -/
theorem nonagentive_drives_ncrA :
    CauserType.agentivityDegree .naturalForce = .marginal ∧
    ncrA.construction.causerRestriction = some .naturalForce := ⟨rfl, rfl⟩

/-- Induced agentivity (ContrHCEAF) drives MCV:
    the controlling causee has partial agentivity. -/
theorem induced_agentivity_drives_mcv :
    CauseeAffecteeType.hasInducedAgentivity .controllingHuman = true ∧
    mcv.prototype.presentCausees = [.controllingHuman] := ⟨rfl, rfl⟩

end Fragments.Urdu.CausativeSystem
