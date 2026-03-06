import Linglib.Theories.Semantics.Reference.MinimalPronoun
import Linglib.Theories.Syntax.Minimalism.Tense.Wurmbrand
import Linglib.Fragments.Mixtec.SMPM.Basic

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
   and restructuring (table 26)
2. **OC with overt pronouns**: untensed subjunctives show the full OC
   signature despite having an overt clitic pronoun, not null PRO
3. **Against movement, for base-generation**: exempt anaphor distribution
   shows the controlled pronoun is base-generated (§6)
4. **Morphological analysis**: overt PRO derived by lacking a null
   vocabulary item; cross-linguistic syncretism typology (table 92)
5. **Implicational universal**: overt PRO → non-*pro*-drop

## Wurmbrand Bridge

SMPM's three clause types map onto @cite{wurmbrand-2014}'s infinitival
tense classification, connecting clause-level tense properties to control:

| Wurmbrand class   | SMPM clause type       | OC? |
|-------------------|------------------------|-----|
| futureIrrealis    | tensed subjunctive     | No  |
| restructuring     | untensed subjunctive   | Yes |
| propositional     | finite embedded        | No  |
-/

namespace Phenomena.Control.Studies.Ostrove2026

open Semantics.Reference.MinimalPronoun
open Minimalism.Tense.Wurmbrand (InfinitivalTenseClass)
open Fragments.Mixtec.SMPM (ClauseType clauseProperties)

-- ════════════════════════════════════════════════════════════════
-- § 1: Clause Type Verification (table 26)
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
    partial control (tensed subj. only, fn. 16), and non-local
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
-- § 3: Wurmbrand Bridge
-- ════════════════════════════════════════════════════════════════

/-- SMPM clause types correspond to @cite{wurmbrand-2014}'s infinitival
    tense classes. The mapping is not identity — SMPM has subjunctives
    rather than infinitives — but the tense-structural properties align:

    - futureIrrealis ↔ tensed subjunctive: future-oriented, non-OC
    - restructuring ↔ untensed subjunctive: dependent tense, OC
    - propositional ↔ finite embedded: independent tense, non-OC -/
def wurmbrandToSMPM : InfinitivalTenseClass → ClauseType
  | .futureIrrealis => .tensedSubjunctive
  | .restructuring  => .untensedSubjunctive
  | .propositional  => .finiteEmbedded

/-- Whether a Wurmbrand class involves obligatory control.

    Restructuring infinitives (try, begin, manage) are the canonical
    OC environment crosslinguistically. Future-irrealis (want, decide)
    and propositional (believe, claim) are non-OC. -/
def wurmbrandHasOC : InfinitivalTenseClass → Bool
  | .restructuring  => true
  | .futureIrrealis => false
  | .propositional  => false

/-- The Wurmbrand classification predicts control properties:
    mapping a Wurmbrand class to its SMPM correspondent and checking
    for OC gives the same result as directly asking whether the
    Wurmbrand class involves OC. -/
theorem wurmbrand_predicts_control (c : InfinitivalTenseClass) :
    (smpmOCSignature (wurmbrandToSMPM c)).isOC = wurmbrandHasOC c := by
  cases c <;> rfl

-- ════════════════════════════════════════════════════════════════
-- § 4: Minimal Pronoun Inventories
-- ════════════════════════════════════════════════════════════════

/-- Surface forms for bound variable anaphora. -/
inductive PronForm where
  /-- Silent (null PRO) -/
  | null
  /-- Overt pronoun (φ-matching clitic or full form) -/
  | pronoun
  /-- Reflexive anaphor (English *-self*, SMPM *mí* + pronoun) -/
  | reflexive
  deriving DecidableEq, BEq, Repr

/-- English vocabulary items (94a–c).

    Three items: null for controlled, reflexive for locally bound,
    pronoun elsewhere. This is the "full" inventory — English
    distinguishes all three non-free BVA contexts morphologically. -/
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

-- ════════════════════════════════════════════════════════════════
-- § 5: Deriving Overt PRO
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
-- § 6: Syncretism Typology (table 92)
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
-- § 7: Implicational Universal (54)
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

-- ════════════════════════════════════════════════════════════════
-- § 8: End-to-End Chain
-- ════════════════════════════════════════════════════════════════

/-- End-to-end: SMPM's vocabulary inventory lacks a null allomorph,
    so the elsewhere form (pronoun) surfaces in controlled position,
    which produces overt PRO, which (given non-*pro*-drop from the
    fragment) satisfies the implicational universal.

    This chains §4–§7: inventory → controlForm → overt PRO → universal. -/
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

end Phenomena.Control.Studies.Ostrove2026
