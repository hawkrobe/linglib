/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.MinimalPronoun
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Fragments.Mixtec.SMPM.Basic
import Linglib.Syntax.Control.Tier
import Linglib.Syntax.Control.CopyControl
import Linglib.Syntax.Control.Basic
import Linglib.Syntax.Control.Diagnostics
import Linglib.Studies.Landau2013
import Linglib.Studies.Allotey2021
import Linglib.Features.Complementation

/-!
# Ostrove (2026): Obligatorily Overt PRO in San Martín Peras Mixtec
[ostrove-2026]

Linguistic Inquiry 57(1): 1–48.

San Martín Peras Mixtec (SMPM), an Oto-Manguean language (ISO: jmx), has
obligatory control constructions where the controlled subject must be an
**overt clitic pronoun** — null PRO is strongly ungrammatical. This is analyzed
via the minimal pronoun framework ([kratzer-2009], [safir-2014],
[landau-2015]): SMPM simply lacks a null vocabulary item for controlled
subject position. The elsewhere item (→ pronoun) applies.

## Core Contributions

1. **Three-way clause typology**: finite embedded, tensed subjunctive,
   untensed subjunctive — distinguished by TAM, noncoreferential subjects,
   and restructuring (26)
2. **OC with overt pronouns**: untensed subjunctives show the full OC
   signature despite having an overt clitic pronoun, not null PRO
3. **Against movement, for base-generation**: exempt anaphor distribution
   shows the controlled pronoun is base-generated (§6)
4. **Morphological analysis**: overt PRO derived by lacking a null
   vocabulary item; cross-linguistic syncretism typology (92)
5. **Copy control typology**: four types of copy control distinguished
   cross-linguistically (§5)
6. **Implicational universal**: overt PRO → non-*pro*-drop (54)

## Landau (2004) Bridge

SMPM's subjunctive types map onto [landau-2004]'s finiteness scale,
connecting clause-level tense properties to control. The paper explicitly
discusses this connection (p.8), following Landau's distinction between
"C-subjunctives" (untensed, OC) and "F-subjunctives" (tensed, non-OC).

## Wurmbrand (2014) Partial Bridge

[wurmbrand-2014]'s three-way classification of infinitival tense
(futureIrrealis, restructuring, propositional) maps partially to SMPM's
subjunctive types. The mapping applies only to subjunctives — SMPM's
finite embedded clauses are genuinely finite and fall outside Wurmbrand's
infinitival classification.

| Wurmbrand class   | SMPM clause type       | OC? |
|-------------------|------------------------|-----|
| futureIrrealis    | tensed subjunctive     | No  |
| restructuring     | untensed subjunctive   | Yes |
| *(not applicable)*| finite embedded        | No  |
-/

namespace Ostrove2026

open Minimalist.MinimalPronoun
open Control
open Minimalist (InfinitivalTenseClass)
open Mixtec.SMPM (EmbeddedClauseType clauseProperties)

-- ════════════════════════════════════════════════════════════════
-- § 1: Clause Type Verification (26)
-- ════════════════════════════════════════════════════════════════

-- Per-feature verification theorems derived from Fragment data
theorem finite_unrestricted_tam :
    (clauseProperties .finiteEmbedded).unrestrictedTAM = true := rfl
theorem tensed_restricted_tam :
    (clauseProperties .tensedSubjunctive).unrestrictedTAM = false := rfl
theorem untensed_restricted_tam :
    (clauseProperties .untensedSubjunctive).unrestrictedTAM = false := rfl

theorem finite_allows_noncoreferential :
    (clauseProperties .finiteEmbedded).noncoreferentialSubject = true := rfl
theorem tensed_allows_noncoreferential :
    (clauseProperties .tensedSubjunctive).noncoreferentialSubject = true := rfl
theorem untensed_no_noncoreferential :
    (clauseProperties .untensedSubjunctive).noncoreferentialSubject = false := rfl

theorem untensed_restructuring :
    (clauseProperties .untensedSubjunctive).restructuring = true := rfl
theorem tensed_no_restructuring :
    (clauseProperties .tensedSubjunctive).restructuring = false := rfl
theorem finite_no_restructuring :
    (clauseProperties .finiteEmbedded).restructuring = false := rfl

-- ════════════════════════════════════════════════════════════════
-- § 2: OC Diagnostics (§4)
-- ════════════════════════════════════════════════════════════════

/-- The control signature of each SMPM clause type, from
    `clauseProperties.noncoreferentialSubject` via
    `Landau2013.ofNoncoreferential` — the same derivation
    `Allotey2021.gaProfile` uses for Gã.

    Untensed subjunctives show the full OC signature (§4):
    - Sloppy-only under VPE (33)
    - Exhaustive binding — no partial control (37)
    - Local c-commanding antecedent required (40, 44)

    Tensed subjunctives and finite embedded clauses show none of
    these properties: they allow strict readings under VPE (30, 32),
    nonexhaustive binding (tensed subj., fn. 16), and non-local
    antecedents (43, 45). -/
def smpmProfile (c : EmbeddedClauseType) : Profile Landau2013.Clause74 :=
  Landau2013.ofNoncoreferential (clauseProperties c).noncoreferentialSubject

theorem untensed_is_OC :
    (smpmProfile .untensedSubjunctive).IsObligatory := by decide

theorem tensed_not_OC :
    ¬(smpmProfile .tensedSubjunctive).IsObligatory := by decide

theorem finite_not_OC :
    ¬(smpmProfile .finiteEmbedded).IsObligatory := by decide

-- ════════════════════════════════════════════════════════════════
-- § 3: Wurmbrand Bridge (partial — subjunctives only)
-- ════════════════════════════════════════════════════════════════

/-- SMPM's two subjunctive types correspond to [wurmbrand-2014]'s
    infinitival tense classes. The mapping applies only to subjunctives —
    SMPM's finite embedded clauses are genuinely finite and fall outside
    Wurmbrand's infinitival classification.

    - futureIrrealis ↔ tensed subjunctive: future-oriented, non-OC
    - restructuring ↔ untensed subjunctive: dependent tense, OC

    Note: Wurmbrand's `propositional` class (ECM/attitude infinitives
    like "believe Julia to be smart") has no SMPM correspondent. SMPM's
    finite embedded clauses have full TAM morphology and freely
    noncoreferential subjects — they are not infinitival. -/
def wurmbrandToSubjunctive : InfinitivalTenseClass → Option EmbeddedClauseType
  | .futureIrrealis => some .tensedSubjunctive
  | .restructuring  => some .untensedSubjunctive
  | .propositional  => none  -- no SMPM correspondent

/-- Whether a Wurmbrand class involves obligatory control. -/
def wurmbrandHasOC : InfinitivalTenseClass → Bool
  | .restructuring  => true
  | .futureIrrealis => false
  | .propositional  => false

/-- For the Wurmbrand classes with SMPM correspondents, the mapping
    correctly predicts control properties. -/
theorem wurmbrand_predicts_control (w : InfinitivalTenseClass) :
    ∀ c ∈ wurmbrandToSubjunctive w,
      ((smpmProfile c).IsObligatory ↔ wurmbrandHasOC w = true) := by
  cases w <;> decide

/-- Propositional infinitives have no SMPM correspondent —
    SMPM finite embedded clauses are genuinely finite, not infinitival. -/
theorem wurmbrand_propositional_no_correspondent :
    wurmbrandToSubjunctive .propositional = none := rfl

-- ════════════════════════════════════════════════════════════════
-- § 4: Landau (2004) Bridge
-- ════════════════════════════════════════════════════════════════

/-- SMPM clause types map onto [landau-2004]'s finiteness scale.
    This is the framework the paper explicitly uses (p.8).

    | Landau class    | SMPM clause type       | OC? |
    |-----------------|------------------------|-----|
    | C-subjunctive   | untensed subjunctive   | Yes |
    | F-subjunctive   | tensed subjunctive     | No  |
    | finite          | finite embedded        | No  | -/
def landauToSMPM : Control.ClauseClass → EmbeddedClauseType
  | .cSubjunctive => .untensedSubjunctive
  | .fSubjunctive => .tensedSubjunctive
  | .finite       => .finiteEmbedded

/-- The forward direction, derived from the fragment's TAM observables
    via `ClauseClass.ofFiniteness` (the same derivation as
    `Allotey2021.gaToLandau`). -/
def smpmToLandau (c : EmbeddedClauseType) : Control.ClauseClass :=
  .ofFiniteness (clauseProperties c).unrestrictedTAM
    (clauseProperties c).independentTense

/-- The stipulated table `landauToSMPM` is a section of the derived
    classification: SMPM realizes every position of [landau-2004]'s
    scale (contrast `Allotey2021.ga_no_fSubjunctive`). -/
theorem smpmToLandau_landauToSMPM (c : Control.ClauseClass) :
    smpmToLandau (landauToSMPM c) = c := by
  cases c <;> rfl

/-- SMPM Agr status for each Landau clause class.

    - C-subjunctive (untensed): [−Agr] — no independent subject agreement
    - F-subjunctive (tensed): [+Agr] — allows noncoreferential subjects,
      which indicates independent agreement capability
    - Finite: [+Agr] — full agreement

    Under the TTC's OC-NC generalization ((70) in [landau-2015]),
    [+Agr] blocks logophoric control. This is why SMPM tensed subjunctives
    (F-subjunctives with [+Agr]) show no OC despite structurally permitting
    logophoric control. -/
def smpmLandauAgr : Control.ClauseClass → Bool
  | .cSubjunctive => false
  | .fSubjunctive => true
  | .finite       => true

/-- The Landau classification predicts control properties for all
    three SMPM clause types, taking Agr status into account.

    - C-subjunctive [−Agr]: predicative OC (Agr-independent) → OC ✓
    - F-subjunctive [+Agr]: logophoric OC blocked by Agr → no OC ✓
    - Finite [+Agr]: no control tier → no OC ✓ -/
theorem landau_predicts_control (c : Control.ClauseClass) :
    (smpmProfile (landauToSMPM c)).IsObligatory ↔
      c.HasOC (smpmLandauAgr c) := by
  cases c <;> decide

-- ════════════════════════════════════════════════════════════════
-- § 5: Minimal Pronoun Inventories (§7)
-- ════════════════════════════════════════════════════════════════

/-- English vocabulary items (94a–c).

    Three items: null for controlled, reflexive for locally bound,
    pronoun elsewhere. English distinguishes all three non-free BVA
    contexts morphologically. -/
def englishInventory : MinPronInventory PronForm where
  items := [ ⟨.controlledSubject, .null⟩,      -- (94a) D[πφ] → ∅ / controlled
             ⟨.locallyBound, .reflexive⟩ ]      -- (94b) D[πφ] → -self / locally bound
  elsewhere := .pronoun                          -- (94c) D[πφ] → pronoun

/-- Haitian vocabulary items (96a–b).

    Two items: null for controlled, pronoun elsewhere. Crucially
    LACKS a reflexive allomorph — reflexives and bound variables
    are both realized as pronouns ([dechaine-manfredi-1994]). -/
def haitianInventory : MinPronInventory PronForm where
  items := [ ⟨.controlledSubject, .null⟩ ]      -- (96a) D[πφ] → ∅ / controlled
  elsewhere := .pronoun                          -- (96b) D[πφ] → pronoun

/-- SMPM vocabulary items (98a–b).

    Two items: reflexive for locally bound, pronoun elsewhere. Crucially
    LACKS a null allomorph — controlled subjects and bound variables
    are both realized as overt clitic pronouns (=rà, =ñá, etc.). -/
def smpmInventory : MinPronInventory PronForm where
  items := [ ⟨.locallyBound, .reflexive⟩ ]      -- (98a) D[πφ] → mí + pronoun / locally bound
  elsewhere := .pronoun                          -- (98b) D[πφ] → pronoun

/-- Quiegolani Zapotec: no context-specific items at all
    ([black-1994]).

    Everything — reflexives, controlled subjects, bound variables —
    surfaces as a single pronoun form (*men*). Total syncretism. -/
def quiegolaniInventory : MinPronInventory PronForm where
  items := []
  elsewhere := .pronoun

/-- Büli vocabulary items (inferred from [sulemana-2021]).

    Like SMPM and Gã: lacks a null allomorph for controlled subjects.
    Overt PRO in nonfinite complementation. -/
def buliInventory : MinPronInventory PronForm where
  items := []  -- Büli has total BVA syncretism (like Quiegolani)
  elsewhere := .pronoun

-- ════════════════════════════════════════════════════════════════
-- § 6: Deriving Overt PRO
-- ════════════════════════════════════════════════════════════════

/-- English: controlled subjects are null (= silent PRO). -/
theorem english_null_pro :
    englishInventory.controlForm = .null := rfl

/-- SMPM: controlled subjects are overt pronouns (= overt PRO).
    This is the paper's central empirical observation. -/
theorem smpm_overt_pro :
    smpmInventory.controlForm = .pronoun := rfl

/-- Haitian: controlled subjects are null. -/
theorem haitian_null_pro :
    haitianInventory.controlForm = .null := rfl

/-- Quiegolani Zapotec: controlled subjects are overt pronouns. -/
theorem quiegolani_overt_pro :
    quiegolaniInventory.controlForm = .pronoun := rfl

/-- Büli: controlled subjects are overt pronouns. -/
theorem buli_overt_pro :
    buliInventory.controlForm = .pronoun := rfl

/-- English has reflexives distinct from pronouns. -/
theorem english_has_reflexive :
    englishInventory.realize .locallyBound = .reflexive := rfl

/-- SMPM has reflexives distinct from pronouns (mí + clitic). -/
theorem smpm_has_reflexive :
    smpmInventory.realize .locallyBound = .reflexive := rfl

/-- Haitian lacks distinct reflexives — reflexives surface as pronouns. -/
theorem haitian_no_reflexive :
    haitianInventory.realize .locallyBound = .pronoun := rfl

-- ════════════════════════════════════════════════════════════════
-- § 7: Syncretism Typology (92)
-- ════════════════════════════════════════════════════════════════

def englishSyncretism : BVASyncretism :=
  syncretismFromInventory englishInventory "English"

def quiegolaniSyncretism : BVASyncretism :=
  syncretismFromInventory quiegolaniInventory "Quiegolani Zapotec"

def haitianSyncretism : BVASyncretism :=
  syncretismFromInventory haitianInventory "Haitian"

def smpmSyncretism : BVASyncretism :=
  syncretismFromInventory smpmInventory "SMPM"

-- English: reflexive ×, controlled ×, bound var =
theorem english_reflexive_distinct :
    englishSyncretism.reflexiveEqReferential = false := rfl
theorem english_controlled_distinct :
    englishSyncretism.controlledEqReferential = false := rfl
theorem english_boundvar_syncretic :
    englishSyncretism.boundVarEqReferential = true := rfl

-- Quiegolani Zapotec: total syncretism (all =)
theorem quiegolani_reflexive_syncretic :
    quiegolaniSyncretism.reflexiveEqReferential = true := rfl
theorem quiegolani_controlled_syncretic :
    quiegolaniSyncretism.controlledEqReferential = true := rfl
theorem quiegolani_boundvar_syncretic :
    quiegolaniSyncretism.boundVarEqReferential = true := rfl

-- Haitian: reflexive =, controlled ×, bound var =
theorem haitian_reflexive_syncretic :
    haitianSyncretism.reflexiveEqReferential = true := rfl
theorem haitian_controlled_distinct :
    haitianSyncretism.controlledEqReferential = false := rfl
theorem haitian_boundvar_syncretic :
    haitianSyncretism.boundVarEqReferential = true := rfl

-- SMPM: reflexive ×, controlled =, bound var =
theorem smpm_reflexive_distinct :
    smpmSyncretism.reflexiveEqReferential = false := rfl
theorem smpm_controlled_syncretic :
    smpmSyncretism.controlledEqReferential = true := rfl
theorem smpm_boundvar_syncretic :
    smpmSyncretism.boundVarEqReferential = true := rfl

-- ════════════════════════════════════════════════════════════════
-- § 8: Copy Control Typology (§5)
-- ════════════════════════════════════════════════════════════════

/-- SMPM instantiates obligatory pronominal copy control:
    the controlled subject is always an overt clitic pronoun showing
    the full OC signature. This distinguishes SMPM from:
    - Full copy control (San Lucas Quievaní Zapotec): full DP copy
    - Logophoric pronominal (Gengbe, Mandarin): attitude reports only
    - Scope-sensitive pronominal (Italian, Hungarian): focus-triggered -/
def smpmCopyControlType : CopyControlType := .obligatoryPronominal

theorem smpm_shows_oc : smpmCopyControlType.showsOC = true := rfl

theorem smpm_not_attitude_only :
    smpmCopyControlType.attitudeOnly = false := rfl

theorem smpm_no_scope_operator :
    smpmCopyControlType.requiresScopeOperator = false := rfl

/-- Controlled subjects in SMPM cannot bear focus — they must be
    clitic pronouns, and clitics cannot bear focus (65, 67). This
    distinguishes SMPM from scope-sensitive pronominal copy control. -/
theorem smpm_copy_cannot_bear_focus :
    smpmCopyControlType.copyCanBearFocus = false := rfl

/-- The clitic requirement, derived from the fragment and routed through the
    Cardinaletti–Starke deficiency order: the required controlled-subject
    class is strictly more deficient than every entry of the non-clitic
    series ((67)). -/
theorem smpm_controlled_must_be_clitic :
    ∀ p ∈ Mixtec.SMPM.strongSeries, ∀ s ∈ p.strength,
      Mixtec.SMPM.controlledSubjectStrength < s :=
  Mixtec.SMPM.controlledSubject_is_most_deficient

-- ════════════════════════════════════════════════════════════════
-- § 9: Exempt Anaphor Argument (§6)
-- ════════════════════════════════════════════════════════════════

/-- Exempt anaphors (reflexive forms used as possessors, outside the
    Condition A domain) are available in SMPM (74). -/
theorem smpm_has_exempt_anaphors :
    Mixtec.SMPM.exemptAnaphorsAsPossessors = true := rfl

/-- SMPM exempt anaphors cannot have quantified antecedents (75, 78). -/
theorem smpm_no_quantified_exempt :
    Mixtec.SMPM.exemptAnaphorAllowsQuantifiedAntecedent = false := rfl

/-- The occupants of the (86)–(87) configurations. -/
inductive Ex86Item where
  /-- the quantified controller ('each dog', 'no boy') -/
  | quantifierDP
  /-- the overt controlled clitic anteceding the exempt anaphor -/
  | pronoun
  deriving DecidableEq, Repr

/-- The (86)–(87) control dependency: quantified controller position
    `0` to embedded clitic position `1`. -/
def ex86Dependency : SetRel (Fin 2) (Fin 2) := {(0, 1)}

/-- The attested occupants: exempt anaphors reject quantified
    antecedents ((78)), yet they are available in untensed
    subjunctives with quantified controllers ((86)–(87)) — so the
    embedded position holds a genuine referential pronoun, not a
    quantifier copy. -/
def ex86Occupant : Fin 2 → Ex86Item :=
  fun p => if p = 0 then .quantifierDP else .pronoun

/-- Movement is token identity, and the (86)–(87) occupants differ
    across the dependency — movement is refuted (§6, pp. 26–31): SMPM
    control is base-generated. -/
theorem smpm_refutes_movement : ¬ IsExhaustive ex86Occupant ex86Dependency :=
  not_isExhaustive_of_mismatch (P := (· = .quantifierDP)) rfl rfl (by decide)

-- ════════════════════════════════════════════════════════════════
-- § 10: Implicational Universal (54)
-- ════════════════════════════════════════════════════════════════

/-- SMPM instantiates the universal: overt PRO and no *pro*-drop
    (the fragment's flag). -/
theorem smpm_satisfies_universal :
    smpmInventory.OvertPROUniversal Mixtec.SMPM.allowsProDrop :=
  fun _ => rfl

/-- English satisfies the universal vacuously, whatever its pro-drop
    status: its PRO is null. -/
theorem english_satisfies_universal (proDrop : Bool) :
    englishInventory.OvertPROUniversal proDrop :=
  MinPronInventory.overtPROUniversal_of_controlForm_eq_null rfl proDrop

/-- Büli instantiates the universal: overt PRO and no *pro*-drop. -/
theorem buli_satisfies_universal :
    buliInventory.OvertPROUniversal false :=
  fun _ => rfl

-- ════════════════════════════════════════════════════════════════
-- § 11: Complementation Typology Bridge
-- ════════════════════════════════════════════════════════════════

/-- SMPM clause types map to [noonan-2007]'s complement typology.

    - Finite embedded → indicative complement (unrestricted TAM)
    - Tensed subjunctive → subjunctive complement (irrealis only)
    - Untensed subjunctive → subjunctive complement (irrealis, with
      equi-deletion / obligatory coreference)

    All three are "balanced" in Noonan's terms — SMPM lacks
    morphologically nonfinite predicates entirely. -/
def smpmToNoonan : EmbeddedClauseType → NoonanCompType
  | .finiteEmbedded      => .indicative
  | .tensedSubjunctive   => .subjunctive
  | .untensedSubjunctive => .subjunctive

/-- SMPM's CTP classes map to Noonan's CTP classes.

    The paper's predicate lists (27a–c) align with Noonan's semantic
    classification:

    Finite embedded (27a):
    - utterance: say (kà'àn), said (káchi), chat (ntatǔ'un)
    - propAttitude: think (ka'án), believe (nakanini)
    - commentative: be happy (kusijǐ ini), be sad (ntsi'i ini), regret (ntsiko ini)
    - knowledge: know (kòni), wonder (kuntàà ini)

    Tensed subjunctive (27b):
    - desiderative: want (kòni), hope (ntatu), pray (nakwatu), agree (xiinka),
      refuse (xǐunka). 'Hate' (sǐso ini), 'be afraid' (iyì'bí), 'be scared'
      (kuntasí) are emotive predicates but select irrealis complements in SMPM,
      functioning like desideratives. 'Get the idea' (chikàà ini) is cognitive.

    Untensed subjunctive (27c):
    - phasal: start (kìxà), finish (ntsi'i), stop (xikwīn), continue (kò xikwīn)
    - achievement: try (ntùkú), remember (nàkú'ún), forget (nantōso)
    - modal: need (xiniñu'u)
    - desiderative: like to (kutō)
    - knowledge: know how to (kòni xá kasa), learn how to (sakwā'a)
    - negative: not bother (kò ntaa) -/
def smpmCTPClass : EmbeddedClauseType → List CTPClass
  | .finiteEmbedded      => [.utterance, .propAttitude, .commentative, .knowledge]
  | .tensedSubjunctive   => [.desiderative]
  | .untensedSubjunctive => [.phasal, .achievement, .modal, .desiderative,
                              .knowledge, .negative]

/-- Noonan's reality status predicts SMPM clause type selection.

    Irrealis CTPs select subjunctive complements (tensed or untensed);
    realis CTPs select indicative (finite embedded) complements.

    This holds for the core cases: desiderative (want, hope) is irrealis
    and selects tensed subjunctive; phasal (start, stop) is realis but
    selects untensed subjunctive — an apparent exception that reflects
    the restructuring/monoclausal nature of phasal predicates. -/
theorem desiderative_is_irrealis :
    ctpRealityStatus .desiderative = .irrealis := rfl

theorem achievement_is_irrealis :
    ctpRealityStatus .achievement = .irrealis := rfl

theorem utterance_is_realis :
    ctpRealityStatus .utterance = .realis := rfl

theorem propAttitude_is_realis :
    ctpRealityStatus .propAttitude = .realis := rfl

-- ════════════════════════════════════════════════════════════════
-- § 12: Gã Joins the Typology ([allotey-2021])
-- ════════════════════════════════════════════════════════════════

/-! [ostrove-2026] groups SMPM with Gã ([allotey-2021]) and Büli
    ([sulemana-2021]) as obligatory-pronominal copy control languages.
    The Gã fragment and study predate this paper, so the cross-language
    bridges live here (chronology: the later paper draws the
    comparison), consuming `Studies/Allotey2021.lean`. -/

/-- Gã instantiates obligatory pronominal copy control: the controlled
    subject of an irrealis `ni`-clause is always an overt subject
    proclitic showing the full OC signature ([allotey-2021]). -/
def gaCopyControlType : CopyControlType := .obligatoryPronominal

theorem ga_shows_oc : gaCopyControlType.showsOC = true := rfl

/-- Gã and SMPM occupy the same copy-control cell. -/
theorem ga_same_copy_type_as_smpm :
    gaCopyControlType = smpmCopyControlType := rfl

/-- Gã syncretism row, derived from the Allotey2021 inventory:
    reflexive ×, controlled =, bound variable = . -/
def gaSyncretism : BVASyncretism :=
  syncretismFromInventory Allotey2021.gaInventory "Gã"

/-- Gã patterns with SMPM in the syncretism typology: distinct
    reflexive, but controlled subjects and bound variables syncretic
    with the referential pronoun. -/
theorem ga_syncretism_matches_smpm :
    (gaSyncretism.reflexiveEqReferential,
     gaSyncretism.controlledEqReferential,
     gaSyncretism.boundVarEqReferential)
    = (smpmSyncretism.reflexiveEqReferential,
       smpmSyncretism.controlledEqReferential,
       smpmSyncretism.boundVarEqReferential) := rfl

/-- Gã sits in the same cell of the overt-PRO / pro-drop typology as
    SMPM: identical controlled-subject realization, identical pro-drop
    status. -/
theorem ga_patterns_with_smpm :
    Allotey2021.gaInventory.controlForm = smpmInventory.controlForm ∧
      Ga.allowsProDrop = Mixtec.SMPM.allowsProDrop :=
  ⟨rfl, rfl⟩

/-- Where the two overt-PRO languages part ways in [noonan-2007]'s
    typology: SMPM's complements are all balanced (finite or
    subjunctive), while Gã's control complement is a deranked
    bare-root infinitive. -/
theorem ga_deranked_where_smpm_balanced :
    (Allotey2021.gaToNoonan .irrealisNi).isReduced = true ∧
      ∀ c, ((smpmToNoonan c).isReduced = false) :=
  ⟨rfl, fun c => by cases c <;> rfl⟩

end Ostrove2026
