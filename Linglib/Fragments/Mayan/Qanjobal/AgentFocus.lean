import Linglib.Theories.Syntax.Minimalism.Voice
import Linglib.Core.ExtractionMorphology

/-!
# Q'anjob'al Agent Focus and Extraction Fragment
@cite{coon-mateo-pedro-preminger-2014}

Morphological data on Q'anjob'al (Q'anjob'alan, Mayan) related to
extraction asymmetries, Agent Focus, and the Crazy Antipassive.

## Person Morphology (table (13))

Q'anjob'al has two agreement paradigms head-marked on the predicate:
- **Set A (ERG)**: prefixes with pre-consonantal and pre-vocalic allomorphs
- **Set B (ABS)**: suffixes; 3rd person is null (∅)

## Status Suffixes (table (14))

The verb stem's final suffix encodes transitivity:
- Intransitive: *-i* (ITV)
- Transitive: *-V'* (TV)

These surface only phrase-finally; non-final forms omit them.

## Morpheme Order (HIGH-ABS)

Template: ASP - ABS - ERG - ROOT - (DERIV) - SUFFIX

Absolutive immediately follows the aspect marker (pre-stem position),
confirming Q'anjob'al as a HIGH-ABS language.

## Extraction Asymmetries

- S (intransitive subject): extracts freely
- P (transitive object): extracts freely
- A (transitive subject): **banned** without Agent Focus

## Agent Focus

AF suffix *-on* attaches to the verb stem. The verb carries the
intransitive status suffix *-i* (not transitive *-V'*). Absolutive
agreement co-indexes the notional object (not the subject). Used
for *wh*-questions, focus, and relativization targeting the agent.

## Crazy Antipassive

The same *-on* morpheme appears in non-finite embedded transitives:
`Chi uj [hin y-il-on-i] ix Malin` 'Maria can see me.'
Analyzed as the same case-assigning mechanism in environments where
Infl⁰ is absent.
-/

namespace Fragments.Mayan.Qanjobal

open Minimalism

-- ============================================================================
-- § 1: Person Morphology
-- ============================================================================

/-- Person-number values relevant for Q'anjob'al agreement. -/
inductive PN where
  | p1sg | p2sg | p3sg | p1pl | p2pl | p3pl
  deriving DecidableEq, Repr

/-- Set A (ergative/possessive) markers: pre-consonantal allomorphs. -/
def setAPreC : PN → String
  | .p1sg => "hin-"
  | .p2sg => "ha-"
  | .p3sg => "s-"
  | .p1pl => "ko-"
  | .p2pl => "he-"
  | .p3pl => "s-…heb'"

/-- Set A (ergative/possessive) markers: pre-vocalic allomorphs. -/
def setAPreV : PN → String
  | .p1sg => "w-"
  | .p2sg => "h-"
  | .p3sg => "y-"
  | .p1pl => "j-"
  | .p2pl => "hey-"
  | .p3pl => "y-…heb'"

/-- Set B (absolutive) markers: suffixes. -/
def setBMarker : PN → String
  | .p1sg => "-in"
  | .p2sg => "-ach"
  | .p3sg => "-∅"
  | .p1pl => "-on"
  | .p2pl => "-ex"
  | .p3pl => "heb'"

/-- 3rd person absolutive is null (∅). -/
theorem p3sg_abs_null : setBMarker .p3sg = "-∅" := rfl

/-- 3rd person ergative (pre-vocalic) is *y-*, pre-consonantal is *s-*. -/
theorem p3sg_erg_allomorphy :
    setAPreC .p3sg = "s-" ∧ setAPreV .p3sg = "y-" := ⟨rfl, rfl⟩

-- ============================================================================
-- § 2: Status Suffixes
-- ============================================================================

/-- Verb status suffixes encode transitivity. Surface only phrase-finally. -/
inductive StatusSuffix where
  | itv   -- intransitive: *-i*
  | tv    -- transitive: *-V'*
  deriving DecidableEq, Repr

def StatusSuffix.form : StatusSuffix → String
  | .itv => "-i"
  | .tv  => "-V'"

-- ============================================================================
-- § 3: Extraction Data
-- ============================================================================

/-- Extraction possibilities in Q'anjob'al transitive clauses. -/
inductive ExtractionTarget where
  | intranS   -- S: intransitive subject
  | patient   -- P: transitive object
  | agent     -- A: transitive subject
  deriving DecidableEq, Repr

/-- Can this argument be A-bar extracted from a regular transitive clause? -/
def ExtractionTarget.extractable : ExtractionTarget → Bool
  | .intranS => true   -- S extracts freely
  | .patient => true   -- P extracts freely
  | .agent   => false  -- A banned without AF

/-- A (transitive subject) cannot be extracted. -/
theorem agent_extraction_banned :
    ExtractionTarget.agent.extractable = false := rfl

/-- S and P extract freely. -/
theorem absolutive_extraction_free :
    ExtractionTarget.intranS.extractable = true ∧
    ExtractionTarget.patient.extractable = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 4: Agent Focus Construction
-- ============================================================================

/-- Morphological properties of a Q'anjob'al verb form. -/
structure VerbMorphology where
  /-- Does the verb bear the AF suffix *-on*? -/
  hasAFSuffix : Bool
  /-- Which status suffix: ITV or TV? -/
  statusSuffix : StatusSuffix
  /-- Does the verb bear Set A (ergative) agreement? -/
  hasSetA : Bool
  deriving DecidableEq, Repr

/-- Regular transitive verb form. -/
def regularTransitive : VerbMorphology :=
  { hasAFSuffix := false
  , statusSuffix := .tv
  , hasSetA := true }

/-- Agent Focus verb form. -/
def agentFocusForm : VerbMorphology :=
  { hasAFSuffix := true
  , statusSuffix := .itv    -- intransitive status suffix!
  , hasSetA := false }       -- no Set A agreement

/-- AF carries the intransitive status suffix *-i*, not *-V'*. This is
    the morphological reflex of AF Voice being non-phasal (intransitive v⁰).
    Despite the clause having two non-oblique core arguments, the verb's
    status suffix signals intransitivity. -/
theorem af_has_itv_suffix :
    agentFocusForm.statusSuffix = .itv := rfl

/-- AF lacks Set A (ergative) agreement. -/
theorem af_no_set_a : agentFocusForm.hasSetA = false := rfl

/-- Regular transitives have Set A agreement. -/
theorem trans_has_set_a : regularTransitive.hasSetA = true := rfl

/-- Can the agent be extracted with this verb form? -/
def VerbMorphology.permitsAgentExtraction (v : VerbMorphology) : Bool :=
  v.hasAFSuffix

/-- AF permits agent extraction; regular transitive does not. -/
theorem af_permits_extraction :
    agentFocusForm.permitsAgentExtraction = true ∧
    regularTransitive.permitsAgentExtraction = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 5: Crazy Antipassive
-- ============================================================================

/-- The Crazy Antipassive uses the same *-on* morpheme as AF, but in
    non-finite embedded transitives rather than extraction contexts. Both
    carry the intransitive status suffix *-i*.

    `Chi uj [hin y-il-on-i] ix Malin` 'Maria can see me.'
    `Lanan [hach hin-laq'-on-i]` 'I am hugging you.' -/
def crazyAntipassiveForm : VerbMorphology :=
  { hasAFSuffix := true
  , statusSuffix := .itv
  , hasSetA := false }

/-- The Crazy Antipassive is morphologically identical to AF. -/
theorem crazy_ap_is_af_form :
    crazyAntipassiveForm = agentFocusForm := rfl

-- ============================================================================
-- § 6: Person Restriction on AF
-- ============================================================================

/-- In Q'anjob'al, AF is restricted to clauses with **3rd person** agents.
    1st and 2nd person agents use the regular transitive form even when
    focused or extracted. Compare (72a-b) of @cite{coon-mateo-pedro-preminger-2014}:

    - 3rd person: `A Juan max maq'-on[-i] no tx'i'.` (AF required)
    - 1st person: `Ay-in max hin-maq'[-a'] no tx'i'.` (regular transitive)

    The tentative account: 1st/2nd person agents may be base-generated in
    a high clausal position (Spec,CP), so no extraction through the vP phase
    edge is needed — the trapping problem never arises. -/
inductive PersonRestriction where
  | first | second | third
  deriving DecidableEq, Repr

/-- Does AF apply for this person of agent? Only 3rd person. -/
def PersonRestriction.requiresAF : PersonRestriction → Bool
  | .first  => false
  | .second => false
  | .third  => true

theorem af_only_third_person :
    PersonRestriction.third.requiresAF = true ∧
    PersonRestriction.first.requiresAF = false ∧
    PersonRestriction.second.requiresAF = false := ⟨rfl, rfl, rfl⟩

/-- The Crazy Antipassive does NOT have this person restriction:
    it appears with all persons in non-finite embedded transitives.
    This is expected because the Crazy Antipassive is triggered by
    the absence of Infl⁰ (a property of the embedded clause), not by
    extraction through a phase edge. -/
def PersonRestriction.requiresCrazyAP (_p : PersonRestriction) : Bool := true

theorem crazy_ap_all_persons :
    PersonRestriction.first.requiresCrazyAP = true ∧
    PersonRestriction.second.requiresCrazyAP = true ∧
    PersonRestriction.third.requiresCrazyAP = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 7: Extraction Profile
-- ============================================================================

/-- Q'anjob'al's extraction morphology profile. -/
def extractionProfile : Interfaces.ExtractionProfile :=
  { language := "Q'anjob'al"
  , strategy := .agentFocusAlternation
  , markedPositions := [.subject]
  , distinguishesPosition := true
  , notes := "AF (*-on*) for 3rd person agent extraction; Coon, Mateo Pedro & Preminger 2014" }

end Fragments.Mayan.Qanjobal
