import Linglib.Fragments.Mayan.Qanjobal.Agreement
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Extraction
import Linglib.Fragments.Mayan.Params

/-!
# Q'anjob'al Agent Focus and Extraction Fragment

Morphological data on Q'anjob'al (Q'anjob'alan, Mayan) extraction
asymmetries, Agent Focus, and the Crazy Antipassive, following
[coon-mateo-pedro-preminger-2014]. Q'anjob'al shows an extraction
asymmetry: the intransitive subject (S) and transitive object (P)
extract freely, but the transitive subject (A) cannot be extracted
without Agent Focus. Agent Focus replaces the regular transitive form
with a verb bearing the AF suffix *-on*, the intransitive status suffix
*-i* (not transitive *-V'*), and no Set A agreement — used for
*wh*-questions, focus, and relativization targeting the agent.

## Main declarations

* `Qanjobal.StatusSuffix` with `.form`: the ITV and TV status suffixes.
* `Qanjobal.VerbMorphology` with `regularTransitive`, `agentFocusForm`:
  the AF-suffix, status-suffix, and Set A properties of a verb form.
* `Qanjobal.VerbMorphology.toMayanVerbForm`: projection to the pan-Mayan
  `Mayan.VerbForm` for cross-Mayan typology.
* `Qanjobal.crazyAntipassiveForm`: the Crazy Antipassive, morphologically
  identical to Agent Focus.
* `Qanjobal.PersonRestriction` with `.requiresAF`, `.requiresCrazyAP`:
  the 3rd-person restriction on Agent Focus.
* `Qanjobal.extractionStrategy`: the AF-based extraction profile.

## Implementation notes

Q'anjob'al head-marks two agreement paradigms on the predicate: Set A
(ERG) prefixes with pre-consonantal and pre-vocalic allomorphs, and Set
B (ABS) suffixes with null 3rd person (∅); the tables live in
`Qanjobal/Agreement.lean`. The verb stem's final suffix encodes
transitivity (intransitive ITV *-i*, transitive TV *-V'*) and surfaces
only phrase-finally. Morpheme order is ASP-ABS-ERG-ROOT-(DERIV)-SUFFIX,
with the absolutive immediately after the aspect marker (pre-stem),
confirming Q'anjob'al as HIGH-ABS. In Agent Focus, absolutive agreement
co-indexes the notional object rather than the subject. The Crazy
Antipassive reuses the same *-on* morpheme in non-finite embedded
transitives (where Infl⁰ is absent), analyzed as the same case-assigning
mechanism. Tables and examples cite [coon-mateo-pedro-preminger-2014]
tables (13) and (14).
-/

namespace Qanjobal

open Minimalist

/-! ### Status suffixes -/

/-- Verb status suffixes encode transitivity. Surface only phrase-finally. -/
inductive StatusSuffix where
  | itv   -- intransitive: *-i*
  | tv    -- transitive: *-V'*
  deriving DecidableEq, Repr

def StatusSuffix.form : StatusSuffix → String
  | .itv => "-i"
  | .tv  => "-V'"

-- The local `inductive ExtractionTarget` (intranS/patient/agent) was
-- redundant with `extractionMarkedPositions`: the substantive
-- claim "A-extraction is banned without AF" is now expressed as
-- `Extraction.Marks extractionMarkedPositions .subject` (subject = .agent's
-- default position per `Extraction.ArgumentRole.defaultPosition`).

/-! ### Agent Focus construction -/

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

/-- Project `VerbMorphology` down to the pan-Mayan `Mayan.VerbForm` for
    cross-Mayan typology; the `hasAFSuffix` flag discriminates AF form
    from transitive. -/
def VerbMorphology.toMayanVerbForm (v : VerbMorphology) : Mayan.VerbForm :=
  if v.hasAFSuffix then .agentFocus else .transitive

/-- AF morphology projects to `.agentFocus`; regular transitive to
    `.transitive`. -/
theorem toMayanVerbForm_canonical :
    agentFocusForm.toMayanVerbForm = .agentFocus ∧
    regularTransitive.toMayanVerbForm = .transitive := ⟨rfl, rfl⟩

/-- Cross-Mayan consistency: Q'anjob'al's AF form lacks Set A under both
    the language-internal `hasSetA` field and the projected
    `Mayan.VerbForm.hasSetA` predicate. -/
theorem hasSetA_consistent_with_projection :
    agentFocusForm.toMayanVerbForm.hasSetA = agentFocusForm.hasSetA ∧
    regularTransitive.toMayanVerbForm.hasSetA = regularTransitive.hasSetA :=
  ⟨rfl, rfl⟩

/-! ### Crazy Antipassive -/

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

/-! ### Person restriction on Agent Focus -/

/-- In Q'anjob'al, AF is restricted to clauses with **3rd person** agents.
    1st and 2nd person agents use the regular transitive form even when
    focused or extracted. Compare (72a-b) of [coon-mateo-pedro-preminger-2014]:

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

/-! ### Extraction profile -/

/-- Q'anjob'al's extraction data: dedicated AF morphology (*-on*) marks
    3rd person agent (subject) extraction ([coon-mateo-pedro-preminger-2014]). -/
def extractionStrategy : Extraction.ExtractionMarkingStrategy := .dedicatedMorpheme
def extractionMarkedPositions : List Extraction.ExtractionTarget := [.subject]
def extractionDistinguishesPosition : Bool := true

end Qanjobal
