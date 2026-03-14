import Linglib.Theories.Syntax.Minimalism.MinimalPronoun
import Linglib.Theories.Syntax.Minimalism.Tense.InfinitivalTense
import Linglib.Fragments.Mixtec.SMPM.Basic
import Linglib.Phenomena.Complementation.Typology

/-!
# Ostrove (2026): Obligatorily Overt PRO in San Martín Peras Mixtec
@cite{ostrove-2026}

Linguistic Inquiry 57(1): 1–48.

San Martín Peras Mixtec (SMPM), an Oto-Manguean language (ISO: jmx), has
obligatory control constructions where the controlled subject must be an
**overt clitic pronoun** — null PRO is strongly ungrammatical. This is analyzed
via the minimal pronoun framework (@cite{kratzer-2009}, @cite{safir-2014},
@cite{landau-2015}): SMPM simply lacks a null vocabulary item for controlled
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

SMPM's subjunctive types map onto @cite{landau-2004}'s finiteness scale,
connecting clause-level tense properties to control. The paper explicitly
discusses this connection (p.8), following Landau's distinction between
"C-subjunctives" (untensed, OC) and "F-subjunctives" (tensed, non-OC).

## Wurmbrand (2014) Partial Bridge

@cite{wurmbrand-2014}'s three-way classification of infinitival tense
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

namespace Phenomena.Control.Studies.Ostrove2026

open Syntax.Minimalism.MinimalPronoun
open Minimalism.Tense.InfinitivalTense (InfinitivalTenseClass)
open Fragments.Mixtec.SMPM (ClauseType clauseProperties)

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

/-- OC signature for each SMPM clause type.

    Untensed subjunctives show the full OC signature (§4):
    - Sloppy-only under VPE (33)
    - Exhaustive binding — no partial control (37)
    - Local c-commanding antecedent required (40, 44)

    Tensed subjunctives and finite embedded clauses show none of
    these properties: they allow strict readings under VPE (30, 32),
    nonexhaustive binding (tensed subj., fn. 16), and non-local
    antecedents (43, 45). -/
def smpmOCSignature : ClauseType → OCSignature
  | .untensedSubjunctive => ocFull
  | .tensedSubjunctive   => ocNone
  | .finiteEmbedded      => ocNone

theorem untensed_is_OC :
    (smpmOCSignature .untensedSubjunctive).isOC = true := rfl

theorem tensed_not_OC :
    (smpmOCSignature .tensedSubjunctive).isOC = false := rfl

theorem finite_not_OC :
    (smpmOCSignature .finiteEmbedded).isOC = false := rfl

-- ════════════════════════════════════════════════════════════════
-- § 3: Wurmbrand Bridge (partial — subjunctives only)
-- ════════════════════════════════════════════════════════════════

/-- SMPM's two subjunctive types correspond to @cite{wurmbrand-2014}'s
    infinitival tense classes. The mapping applies only to subjunctives —
    SMPM's finite embedded clauses are genuinely finite and fall outside
    Wurmbrand's infinitival classification.

    - futureIrrealis ↔ tensed subjunctive: future-oriented, non-OC
    - restructuring ↔ untensed subjunctive: dependent tense, OC

    Note: Wurmbrand's `propositional` class (ECM/attitude infinitives
    like "believe Julia to be smart") has no SMPM correspondent. SMPM's
    finite embedded clauses have full TAM morphology and freely
    noncoreferential subjects — they are not infinitival. -/
def wurmbrandToSubjunctive : InfinitivalTenseClass → Option ClauseType
  | .futureIrrealis => some .tensedSubjunctive
  | .restructuring  => some .untensedSubjunctive
  | .propositional  => none  -- no SMPM correspondent

/-- Whether a Wurmbrand class involves obligatory control. -/
def wurmbrandHasOC : InfinitivalTenseClass → Bool
  | .restructuring  => true
  | .futureIrrealis => false
  | .propositional  => false

/-- For the two Wurmbrand classes that have SMPM correspondents,
    the mapping correctly predicts control properties. -/
theorem wurmbrand_predicts_control_futureIrrealis :
    (wurmbrandToSubjunctive .futureIrrealis).map (smpmOCSignature · |>.isOC)
    = some (wurmbrandHasOC .futureIrrealis) := rfl

theorem wurmbrand_predicts_control_restructuring :
    (wurmbrandToSubjunctive .restructuring).map (smpmOCSignature · |>.isOC)
    = some (wurmbrandHasOC .restructuring) := rfl

/-- Propositional infinitives have no SMPM correspondent —
    SMPM finite embedded clauses are genuinely finite, not infinitival. -/
theorem wurmbrand_propositional_no_correspondent :
    wurmbrandToSubjunctive .propositional = none := rfl

-- ════════════════════════════════════════════════════════════════
-- § 4: Landau (2004) Bridge
-- ════════════════════════════════════════════════════════════════

/-- @cite{landau-2004}'s finiteness scale distinguishes C-subjunctives
    (untensed, obligatory control) from F-subjunctives (tensed, non-OC).
    This is the framework the paper explicitly uses (p.8).

    | Landau class    | SMPM clause type       | OC? |
    |-----------------|------------------------|-----|
    | C-subjunctive   | untensed subjunctive   | Yes |
    | F-subjunctive   | tensed subjunctive     | No  |
    | finite          | finite embedded        | No  | -/
inductive LandauClauseClass where
  | cSubjunctive   -- Untensed nonfinite, OC
  | fSubjunctive   -- Tensed nonfinite, non-OC
  | finite         -- Fully finite
  deriving DecidableEq, BEq, Repr

def landauToSMPM : LandauClauseClass → ClauseType
  | .cSubjunctive => .untensedSubjunctive
  | .fSubjunctive => .tensedSubjunctive
  | .finite       => .finiteEmbedded

def landauHasOC : LandauClauseClass → Bool
  | .cSubjunctive => true
  | .fSubjunctive => false
  | .finite       => false

/-- The Landau classification predicts control properties for all
    three SMPM clause types. -/
theorem landau_predicts_control (c : LandauClauseClass) :
    (smpmOCSignature (landauToSMPM c)).isOC = landauHasOC c := by
  cases c <;> rfl

-- ════════════════════════════════════════════════════════════════
-- § 5: Minimal Pronoun Inventories (§7)
-- ════════════════════════════════════════════════════════════════

open PronForm

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
    are both realized as pronouns (@cite{dechaine-manfredi-1994}). -/
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
    (@cite{black-1994}).

    Everything — reflexives, controlled subjects, bound variables —
    surfaces as a single pronoun form (*men*). Total syncretism. -/
def quiegolaniInventory : MinPronInventory PronForm where
  items := []
  elsewhere := .pronoun

/-- Gã vocabulary items (inferred from @cite{allotey-2021}).

    Like SMPM: lacks a null allomorph for controlled subjects.
    Overt PRO in complement clause obligatory control. One of three
    languages argued to have obligatory pronominal copy control. -/
def gaInventory : MinPronInventory PronForm where
  items := [ ⟨.locallyBound, .reflexive⟩ ]
  elsewhere := .pronoun

/-- Büli vocabulary items (inferred from @cite{sulemana-2021}).

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

/-- Gã: controlled subjects are overt pronouns. -/
theorem ga_overt_pro :
    gaInventory.controlForm = .pronoun := rfl

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
theorem quiegolani_all_syncretic :
    quiegolaniSyncretism.reflexiveEqReferential = true
    ∧ quiegolaniSyncretism.controlledEqReferential = true
    ∧ quiegolaniSyncretism.boundVarEqReferential = true := ⟨rfl, rfl, rfl⟩

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

theorem smpm_shows_oc :
    (copyControlProfile smpmCopyControlType).showsOC = true := rfl

theorem smpm_not_attitude_only :
    (copyControlProfile smpmCopyControlType).attitudeOnly = false := rfl

theorem smpm_no_scope_operator :
    (copyControlProfile smpmCopyControlType).requiresScopeOperator = false := rfl

/-- Controlled subjects in SMPM cannot bear focus — they must be
    clitic pronouns, and clitics cannot bear focus (65, 67). This
    distinguishes SMPM from scope-sensitive pronominal copy control. -/
theorem smpm_copy_cannot_bear_focus :
    (copyControlProfile smpmCopyControlType).copyCanBearFocus = false := rfl

/-- The clitic requirement is derived from the fragment. -/
theorem smpm_controlled_must_be_clitic :
    Fragments.Mixtec.SMPM.controlledSubjectMustBeClitic = true := rfl

-- ════════════════════════════════════════════════════════════════
-- § 9: Exempt Anaphor Argument (§6)
-- ════════════════════════════════════════════════════════════════

/-- SMPM exempt anaphor profile, derived from fragment data.

    Exempt anaphors (reflexive forms used as possessors, outside
    Condition A domain) ARE available in SMPM (74) but CANNOT have
    quantified antecedents (75, 78). -/
def smpmExemptProfile : ExemptAnaphorProfile where
  hasExemptAnaphors := Fragments.Mixtec.SMPM.exemptAnaphorsAsPossessors
  allowsQuantifiedAntecedent := Fragments.Mixtec.SMPM.exemptAnaphorAllowsQuantifiedAntecedent

theorem smpm_has_exempt_anaphors :
    smpmExemptProfile.hasExemptAnaphors = true := rfl

theorem smpm_no_quantified_exempt :
    smpmExemptProfile.allowsQuantifiedAntecedent = false := rfl

/-- **The argument against movement** (§6, pp.26–31):

    Given: exempt anaphors cannot have quantified antecedents (78).

    Movement analysis predicts: if the controller is quantified (e.g.,
    "every dog"), the copy in embedded subject position IS the quantifier.
    An exempt anaphor in the embedded clause would need to be bound by
    this quantified copy → predicted UNAVAILABLE.

    Base-generation analysis predicts: the pronoun in embedded subject
    position is a genuine pronoun (base-generated), not a copy of the
    quantifier. An exempt anaphor can take this pronoun as antecedent →
    predicted AVAILABLE.

    SMPM data (86–87): exempt anaphors ARE available in untensed
    subjunctives with quantified controllers.
    - *Tá'iin'iin tsǐnà kìxà [tsìi =rí ndò'ò mí =rí].*
      'Each dog started to bite its own tail.'
    - *Kò xíniñu'u ni'iin =rà bálí [kòni =rà táta mí =rà].*
      'No boy needs to see his own father.'

    This matches the base-generation prediction. -/
def smpmExemptAvailableWithQuantifiedController : Bool := true

theorem movement_incorrectly_predicts :
    predictsExemptWithQuantifiedController .movement = false := rfl

theorem basegeneration_correctly_predicts :
    predictsExemptWithQuantifiedController .baseGeneration = true := rfl

theorem smpm_supports_basegeneration :
    smpmExemptAvailableWithQuantifiedController
    = predictsExemptWithQuantifiedController .baseGeneration := rfl

-- ════════════════════════════════════════════════════════════════
-- § 10: Implicational Universal (54)
-- ════════════════════════════════════════════════════════════════

/-- A language's pro-drop and overt-PRO profile.

    @cite{ostrove-2026} (54): If a language requires the subject of
    obligatory control clauses (i.e., PRO) to be overt, then that
    language will not allow *pro*-drop.

    This is a one-way implicational universal — non-*pro*-drop does
    not entail overt PRO (English is non-*pro*-drop but has null PRO). -/
structure ProDropProfile where
  language : String
  allowsProDrop : Bool
  hasOvertPRO : Bool
  deriving DecidableEq, BEq, Repr

/-- The implicational universal: overt PRO → non-*pro*-drop. -/
def satisfiesImplicational (p : ProDropProfile) : Bool :=
  !p.hasOvertPRO || !p.allowsProDrop

/-- Whether the inventory produces overt PRO (i.e., controlled form = pronoun). -/
def hasOvertPRO (inv : MinPronInventory PronForm) : Bool :=
  inv.controlForm == .pronoun

/-- SMPM profile derived from fragment data and inventory. -/
def smpmProfile : ProDropProfile :=
  { language := "SMPM"
  , allowsProDrop := Fragments.Mixtec.SMPM.allowsProDrop
  , hasOvertPRO := hasOvertPRO smpmInventory }

def englishProfile : ProDropProfile :=
  { language := "English", allowsProDrop := false, hasOvertPRO := hasOvertPRO englishInventory }

theorem smpm_satisfies_universal :
    satisfiesImplicational smpmProfile = true := rfl

theorem english_satisfies_universal :
    satisfiesImplicational englishProfile = true := rfl

-- All overt-PRO languages satisfy the universal
theorem ga_satisfies_universal :
    satisfiesImplicational { language := "Gã", allowsProDrop := false
                           , hasOvertPRO := hasOvertPRO gaInventory } = true := rfl

theorem buli_satisfies_universal :
    satisfiesImplicational { language := "Büli", allowsProDrop := false
                           , hasOvertPRO := hasOvertPRO buliInventory } = true := rfl

-- ════════════════════════════════════════════════════════════════
-- § 11: Complementation Typology Bridge
-- ════════════════════════════════════════════════════════════════

open Phenomena.Complementation.Typology

/-- SMPM clause types map to @cite{noonan-2007}'s complement typology.

    - Finite embedded → indicative complement (unrestricted TAM)
    - Tensed subjunctive → subjunctive complement (irrealis only)
    - Untensed subjunctive → subjunctive complement (irrealis, with
      equi-deletion / obligatory coreference)

    All three are "balanced" in Noonan's terms — SMPM lacks
    morphologically nonfinite predicates entirely. -/
def smpmToNoonan : ClauseType → NoonanCompType
  | .finiteEmbedded      => .indicative
  | .tensedSubjunctive   => .subjunctive
  | .untensedSubjunctive => .subjunctive

/-- SMPM's CTP classes map to Noonan's CTP classes.

    The paper's predicate lists (27a–c) align with Noonan's semantic
    classification:
    - Finite embedded predicates: utterance (say), propAttitude (think,
      believe), commentative (be happy, be sad, regret), knowledge (know)
    - Tensed subjunctive predicates: desiderative (want, hope)
    - Untensed subjunctive predicates: phasal (start, finish, stop,
      continue), achievement (try), knowledge (know how to, learn) -/
def smpmCTPClass : ClauseType → List CTPClass
  | .finiteEmbedded      => [.utterance, .propAttitude, .commentative, .knowledge]
  | .tensedSubjunctive   => [.desiderative]
  | .untensedSubjunctive => [.phasal, .achievement]

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
-- § 12: End-to-End Chain
-- ════════════════════════════════════════════════════════════════

/-- End-to-end: SMPM's vocabulary inventory lacks a null allomorph,
    so the elsewhere form (pronoun) surfaces in controlled position,
    which produces overt PRO, which (given non-*pro*-drop from the
    fragment) satisfies the implicational universal.

    This chains §5–§10: inventory → controlForm → overt PRO → universal. -/
theorem smpm_inventory_to_universal :
    satisfiesImplicational
      { language := "SMPM"
      , allowsProDrop := Fragments.Mixtec.SMPM.allowsProDrop
      , hasOvertPRO := hasOvertPRO smpmInventory } = true := rfl

/-- Conversely, English's inventory HAS a null allomorph for controlled
    subjects, so PRO is null — it trivially satisfies the universal
    (the antecedent of the implication is false). -/
theorem english_inventory_to_universal :
    satisfiesImplicational
      { language := "English"
      , allowsProDrop := false
      , hasOvertPRO := hasOvertPRO englishInventory } = true := rfl

/-- Full derivation chain for SMPM: from exempt anaphors through
    base-generation to inventory to overt PRO to the universal.

    1. Exempt anaphors available with quantified controllers (§6) →
    2. Base-generation, not movement (§6) →
    3. Minimal pronoun lacks null allomorph (§7) →
    4. Controlled subjects surface as overt pronouns (§7) →
    5. SMPM is non-pro-drop (§2) →
    6. Implicational universal satisfied (§8) -/
theorem full_chain :
    -- §6: base-generation correctly predicts exempt anaphor data
    smpmExemptAvailableWithQuantifiedController
      = predictsExemptWithQuantifiedController .baseGeneration
    -- §7: inventory produces overt PRO
    ∧ smpmInventory.controlForm = .pronoun
    -- §7: this constitutes obligatory pronominal copy control
    ∧ (copyControlProfile smpmCopyControlType).showsOC = true
    -- §10: implicational universal satisfied
    ∧ satisfiesImplicational smpmProfile = true := ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.Control.Studies.Ostrove2026
