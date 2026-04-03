import Linglib.Theories.Syntax.Minimalism.Core.Agree
import Linglib.Theories.Interfaces.SyntaxPhonology.Minimalism.Spellout
import Linglib.Theories.Syntax.Minimalism.Core.PersonGeometry
import Linglib.Fragments.Mayan.Kaqchikel.AgentFocus
import Linglib.Core.Case

/-!
# Kaqchikel Agreement Fragment @cite{preminger-2014}

Agreement morphology for Kaqchikel (K'ichean, Mayan), formalizing
@cite{preminger-2014} *Agreement and Its Failures*, Chapters 3-4 and @cite{chomsky-2001} @cite{scott-2023} @cite{blake-1994}
Appendix 9.A.

## The System

Kaqchikel has two agreement paradigms on the verb:
- **Set A** (ERG): prefixes on Voice/v cross-referencing the transitive agent
- **Set B** (ABS): preverbal markers on Infl/T cross-referencing the
  absolutive argument (transitive patient or intransitive S)

Morpheme order on the verb (276): `aspect - ABS - ERG - stem`.
Set B (ABS) precedes Set A (ERG).

| Position | Case | Agreement |
|----------|------|-----------|
| A (transitive agent)   | ERG | Set A |
| P (transitive patient) | ABS | Set B |
| S (intransitive subj)  | ABS | Set B |

Unlike Mam, where Infl's φ-probe is blocked in transitives and the
patient goes unagreed, Kaqchikel cross-references *both* transitive
arguments (@cite{preminger-2014}, Ch. 3 vs. @cite{scott-2023} for Mam).

## Agent Focus Agreement (@cite{preminger-2014}, §3.3, table 22)

In AF constructions (clause-local agent extraction), the normal two-slot
agreement collapses to a **single marker** drawn from the absolutive
(Set B) paradigm. The target is chosen by an *omnivorous* hierarchy:

    [+participant] > [+plural] > default (3SG = ∅)

The probe does not distinguish subject from object — AF agreement is
**commutative**: ⟨1SG subj, 3SG obj⟩ = ⟨3SG subj, 1SG obj⟩ → *in-*.
This follows from Preminger's analysis: the probe (π⁰) seeks the
closest [+participant]-bearing DP regardless of its thematic role.

### Person Restriction (@cite{preminger-2014}, (25))

At most one core argument can bear [+participant]. Combinations like
⟨1SG, 2SG⟩ are ungrammatical regardless of subject/object assignment.

## Feature Geometry (@cite{preminger-2014}, §4.3, (55))

Person features decompose as:
- [φ] → [PERSON] → [participant] → [author]
- [φ] → [NUMBER] → [plural]

Two probes in the AF clause:
- **π⁰**: seeks [participant], triggers clitic doubling of full φ-set
- **#⁰**: seeks [plural], triggers number agreement

## Obligatory Operations

Preminger's central theoretical claim: φ-agreement is **obligatory** —
the grammar must attempt it — but can **fail without crashing**. When
the probe finds no suitable goal, no agreement obtains and a default
(3SG = ∅) surfaces. This contrasts with the standard Minimalist view where unvalued features cause the derivation to crash.

-/

namespace Fragments.Mayan.Kaqchikel

open Minimalism

-- ============================================================================
-- § 1: Person-Number Inventory
-- ============================================================================

/-- Person-number combinations for Kaqchikel agreement paradigms.
    Six cells: three persons × two numbers. -/
inductive PersonNumber where
  | p1sg | p2sg | p3sg | p1pl | p2pl | p3pl
  deriving DecidableEq, Repr

/-- All six person-number values. -/
def personNumbers : List PersonNumber :=
  [.p1sg, .p2sg, .p3sg, .p1pl, .p2pl, .p3pl]

-- ============================================================================
-- § 2: Feature Decomposition (grounded in PersonGeometry.lean)
-- ============================================================================

/-- Person value as `PersonLevel` (the canonical person type). -/
def PersonNumber.person : PersonNumber → Core.Prominence.PersonLevel
  | .p1sg | .p1pl => .first
  | .p2sg | .p2pl => .second
  | .p3sg | .p3pl => .third

/-- Is this person-number [+plural]? -/
def PersonNumber.isPlural : PersonNumber → Bool
  | .p1pl | .p2pl | .p3pl => true
  | .p1sg | .p2sg | .p3sg => false

/-- Is this person-number [+participant]? Derived from the feature
    geometry in `PersonGeometry.lean` (@cite{preminger-2014}, §4.3, (55)):
    [participant] ⊂ [PERSON] ⊂ [φ]. -/
def PersonNumber.isParticipant (pn : PersonNumber) : Bool :=
  (decomposePerson pn.person).hasParticipant

/-- Is this person-number [+author]? Derived from the feature geometry:
    [author] ⊂ [participant] ⊂ [PERSON]. -/
def PersonNumber.isAuthor (pn : PersonNumber) : Bool :=
  (decomposePerson pn.person).hasAuthor

/-- Convert to PhiFeature list for the Agree infrastructure. -/
def PersonNumber.toPhiFeatures : PersonNumber → List PhiFeature
  | .p1sg => [.person .first, .number .sg]
  | .p2sg => [.person .second, .number .sg]
  | .p3sg => [.person .third, .number .sg]
  | .p1pl => [.person .first, .number .pl]
  | .p2pl => [.person .second, .number .pl]
  | .p3pl => [.person .third, .number .pl]

-- ============================================================================
-- § 3: Set A (ERG) Vocabulary
-- ============================================================================

/-- Set A (ERG) markers: prefixes on Voice/v cross-referencing the
    transitive agent (@cite{preminger-2014}, Ch. 3, table (29)).
    Parenthesized segments are dropped in certain phonological
    contexts; the grapheme *j* represents a voiceless velar fricative. -/
def setAExponent : PersonNumber → String
  | .p1sg => "n/w-"
  | .p2sg => "a(w)-"
  | .p3sg => "r(u)/u-"
  | .p1pl => "q(a)-"
  | .p2pl => "i(w)-"
  | .p3pl => "k(i)-"

/-- Set A as Vocabulary entries for Spellout, contextualized to Voice/v. -/
def setAVocab : Vocabulary :=
  personNumbers.map λ pn =>
    { features := pn.toPhiFeatures.map (λ p => .valued (.phi p))
    , exponent := setAExponent pn
    , context := some .v }

-- ============================================================================
-- § 4: Set B (ABS) Vocabulary
-- ============================================================================

/-- Set B (ABS) markers: preverbal markers on Infl/T cross-referencing
    the absolutive argument. The 3SG form (∅) is
    also the Elsewhere entry — the default when no more specific entry
    matches, as in the failure case of obligatory agreement (Ch. 5). -/
def setBExponent : PersonNumber → String
  | .p1sg => "in-"
  | .p2sg => "at-"
  | .p3sg => "∅"
  | .p1pl => "oj-"
  | .p2pl => "ix-"
  | .p3pl => "e-"

/-- Set B as Vocabulary entries for Spellout, contextualized to Infl/T. -/
def setBVocab : Vocabulary :=
  personNumbers.map λ pn =>
    { features := pn.toPhiFeatures.map (λ p => .valued (.phi p))
    , exponent := setBExponent pn
    , context := some .T }

-- ============================================================================
-- § 5: Argument Positions
-- ============================================================================

/-- Argument positions in a Kaqchikel clause. -/
inductive KaqArgPosition where
  /-- A: transitive agent (external argument, Spec,vP → Spec,TP) -/
  | agent
  /-- P: transitive patient (internal argument, complement of V) -/
  | patient
  /-- S: intransitive subject (sole argument) -/
  | intranS
  deriving DecidableEq, Repr

/-- Case assignment in perfective (ergative) clauses: ergative-absolutive alignment.
    Agent gets ERG (from Voice/v); patient and intranS both get ABS
    (from Infl/T). -/
def KaqArgPosition.case : KaqArgPosition → CaseVal
  | .agent   => .erg
  | .patient => .abs
  | .intranS => .abs

/-- Case assignment in non-perfective (accusative) clauses
    (@cite{imanishi-2020}, tables (4)/(115)).
    Due to the Restriction on Nominalization, the external argument cannot
    appear inside the nominalized clause. The subject is base-generated as
    the argument of *ajin* in the matrix clause and receives ABS from matrix
    Infl. The object is the only DP inside the nominalized clause and
    receives GEN from D. -/
def KaqArgPosition.accCase : KaqArgPosition → CaseVal
  | .agent   => .abs  -- from matrix Infl (argument of ajin)
  | .patient => .gen  -- from D of nominalized clause
  | .intranS => .abs  -- from matrix Infl

/-- Is this position φ-Agreed-with?
    In Kaqchikel, ALL three argument positions trigger agreement:
    agent via Set A on Voice/v, patient and intranS via Set B on
    Infl/T. This contrasts with Mam, where the patient is NOT
    agreed with (Infl's probe is blocked by VoiceP; @cite{scott-2023}). -/
def KaqArgPosition.isPhiAgreed : KaqArgPosition → Bool
  | .agent   => true
  | .patient => true
  | .intranS => true

/-- Which head agrees with this position? -/
def KaqArgPosition.agreeProbe : KaqArgPosition → Cat
  | .agent   => .v   -- Voice/v probes for agent φ → Set A
  | .patient => .T   -- Infl/T probes for patient φ → Set B
  | .intranS => .T   -- Infl/T probes for intranS φ → Set B

/-- The three argument positions. -/
def kaqArgPositions : List KaqArgPosition :=
  [.agent, .patient, .intranS]

-- ============================================================================
-- § 6: AF Agreement — Omnivorous Hierarchy
-- ============================================================================

/-- The omnivorous agreement hierarchy for AF.

    Derived from `probeResolutionRank` (PersonGeometry.lean), which
    computes rank from the two-probe system:
    - Rank 2: visible to π⁰ ([+participant])
    - Rank 1: visible to #⁰ only ([+plural, −participant])
    - Rank 0: invisible to both probes (3SG, default/Elsewhere)

    The hierarchy is not stipulated — it follows from the feature
    geometry and the probe targets. -/
def PersonNumber.afRank (pn : PersonNumber) : Nat :=
  probeResolutionRank pn.person pn.isPlural

/-- Person restriction (@cite{preminger-2014}, (25)): at most one core
    argument can be [+participant]. Returns `true` if the combination
    is licit. -/
def personRestrictionOk (subj obj : PersonNumber) : Bool :=
  !(subj.isParticipant && obj.isParticipant)

/-- Compute the AF agreement target: whichever argument has the higher
    rank in the omnivorous hierarchy. When both have the same rank, the
    subject is chosen (both yield the same marker, so the choice is
    observationally inert). Returns `none` if the person restriction
    is violated. -/
def afAgreementTarget (subj obj : PersonNumber) : Option PersonNumber :=
  if !personRestrictionOk subj obj then none
  else if subj.afRank ≥ obj.afRank then some subj
  else some obj

/-- The AF agreement marker for a given subject-object combination.
    Returns the Set B exponent of the omnivorous target, or `none`
    if the person restriction is violated. -/
def afMarker (subj obj : PersonNumber) : Option String :=
  (afAgreementTarget subj obj).map setBExponent

-- ============================================================================
-- § 7: AF Agreement Paradigm (@cite{preminger-2014}, table 22)
-- ============================================================================

/-- An AF agreement datum: subject φ, object φ, and the resulting
    single agreement marker (or `none` for person-restriction
    violations). -/
structure AFAgreementDatum where
  subject : PersonNumber
  object : PersonNumber
  marker : Option String
  deriving Repr

/-- The empirical AF agreement paradigm (@cite{preminger-2014}, table (22)).
    Each row records the observed agreement marker for a given
    subject-object combination in clause-local agent extraction.

    The first 11 rows reproduce the paper's table exactly. Rows 12–15
    demonstrate commutativity (§3.2, fn. a): the table uses set notation
    {φ₁, φ₂}, so swapping subj/obj yields the same marker. Rows 16–17
    test person restriction violations ((25)). -/
def afParadigm : List AFAgreementDatum :=
  [ -- Table (22), rows 1–3: both 3rd person, number determines marker
    ⟨.p3sg, .p3sg, some "∅"⟩         -- default: 3SG×3SG → ∅
  , ⟨.p3pl, .p3sg, some "e-"⟩        -- [+plural] outranks default
  , ⟨.p3pl, .p3pl, some "e-"⟩        -- [+plural] both → 3PL
    -- Table (22), rows 4–7: one [+participant] argument with 3SG
  , ⟨.p1sg, .p3sg, some "in-"⟩       -- 1SG [+participant]
  , ⟨.p2sg, .p3sg, some "at-"⟩       -- 2SG [+participant]
  , ⟨.p1pl, .p3sg, some "oj-"⟩       -- 1PL [+participant]
  , ⟨.p2pl, .p3sg, some "ix-"⟩       -- 2PL [+participant]
    -- Table (22), rows 8–11: [+participant] outranks [+plural]
  , ⟨.p1sg, .p3pl, some "in-"⟩       -- 1SG participant > 3PL plural
  , ⟨.p2sg, .p3pl, some "at-"⟩       -- 2SG participant > 3PL plural
  , ⟨.p1pl, .p3pl, some "oj-"⟩       -- 1PL participant > 3PL plural
  , ⟨.p2pl, .p3pl, some "ix-"⟩       -- 2PL participant > 3PL plural
    -- Commutativity (§3.2, fn. a): swapping subj/obj → same marker
  , ⟨.p3sg, .p3pl, some "e-"⟩        -- = {3PL, 3SG} swapped
  , ⟨.p3sg, .p1sg, some "in-"⟩       -- = {1SG, 3SG} swapped
  , ⟨.p3sg, .p2sg, some "at-"⟩       -- = {2SG, 3SG} swapped
  , ⟨.p3pl, .p2sg, some "at-"⟩       -- = {2SG, 3PL} swapped
    -- Person restriction violations (25)
  , ⟨.p1sg, .p2sg, none⟩             -- *two [+participant] args
  , ⟨.p2sg, .p1sg, none⟩             -- *two [+participant] args
  ]

-- ============================================================================
-- § 8: Agreement Slot Count
-- ============================================================================

/-- Number of agreement slots for each verb form.
    Transitive: two slots (Set A + Set B).
    AF: one slot (single omnivorous marker from the ABS paradigm). -/
def VerbForm.agreementSlots : VerbForm → Nat
  | .transitive => 2
  | .agentFocus => 1

-- ============================================================================
-- § 9: Obligatory Operations (@cite{preminger-2014}, Ch. 5)
-- ============================================================================

/-- The result of an obligatory agreement operation.

    Preminger's key insight: the probe *must* attempt to Agree
    (agreement is obligatory), but if it finds no suitable goal,
    the derivation does NOT crash — it continues with the probe's
    features unvalued, and the Elsewhere vocabulary entry (3SG ∅)
    surfaces at PF. -/
inductive AgreeOutcome where
  /-- Probe successfully valued by a goal's φ-features. -/
  | success : PersonNumber → AgreeOutcome
  /-- Probe attempted but found no suitable goal; default surfaces. -/
  | failure : AgreeOutcome
  deriving DecidableEq, Repr

/-- The morphological exponent for an agreement outcome.
    Success: Set B form of the agreed-with argument.
    Failure: Elsewhere entry (3SG ∅). -/
def AgreeOutcome.exponent : AgreeOutcome → String
  | .success pn => setBExponent pn
  | .failure    => "∅"

/-- Failed agreement surfaces as 3SG — the Elsewhere entry. -/
theorem failed_agreement_is_3sg :
    AgreeOutcome.failure.exponent = setBExponent .p3sg := rfl

-- ============================================================================
-- § 10: Verification Theorems — Argument Positions
-- ============================================================================

/-- Agent gets ERG (from Voice). -/
theorem agent_case : KaqArgPosition.agent.case = .erg := rfl

/-- Patient gets ABS (from Infl). -/
theorem patient_case : KaqArgPosition.patient.case = .abs := rfl

/-- Intransitive S gets ABS (from Infl). -/
theorem intranS_case : KaqArgPosition.intranS.case = .abs := rfl

/-- Ergative-absolutive alignment: the agent is distinguished (ERG)
    while patient and intranS share a case value (ABS). -/
theorem erg_abs_alignment :
    KaqArgPosition.agent.case ≠ KaqArgPosition.patient.case ∧
    KaqArgPosition.patient.case = KaqArgPosition.intranS.case :=
  ⟨by decide, rfl⟩

/-- Accusative alignment in non-perfective: S/A pattern together (ABS),
    O is distinct (GEN). Mirror image of Chol/Q'anjob'al. -/
theorem acc_alignment :
    KaqArgPosition.agent.accCase = KaqArgPosition.intranS.accCase ∧
    KaqArgPosition.agent.accCase ≠ KaqArgPosition.patient.accCase :=
  ⟨rfl, by decide⟩

/-- All three argument positions trigger φ-agreement. -/
theorem all_positions_agreed :
    kaqArgPositions.all (λ p => p.isPhiAgreed) = true := by native_decide

-- ============================================================================
-- § 11: Verification Theorems — Feature Decomposition
-- ============================================================================

/-- [+author] entails [+participant] (@cite{preminger-2014}, (55)):
    [author] ⊂ [participant] in the feature geometry. -/
theorem author_entails_participant :
    personNumbers.all (λ pn =>
      if pn.isAuthor then pn.isParticipant else true) = true := by
  native_decide

/-- 3rd person is [-participant]. -/
theorem third_not_participant :
    PersonNumber.p3sg.isParticipant = false ∧
    PersonNumber.p3pl.isParticipant = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 12: Verification — Grounding in PersonGeometry
-- ============================================================================

/-- The AF hierarchy is grounded in the two-probe system: person-number
    values that bear [+participant] get rank 2 (visible to π⁰), 3PL
    gets rank 1 (visible to #⁰ only), and 3SG gets rank 0. -/
theorem af_rank_grounded :
    PersonNumber.p1sg.afRank = 2 ∧
    PersonNumber.p2sg.afRank = 2 ∧
    PersonNumber.p3pl.afRank = 1 ∧
    PersonNumber.p3sg.afRank = 0 := ⟨rfl, rfl, rfl, rfl⟩

/-- isParticipant is derived from decomposePerson, not stipulated.
    Verify it gives the expected values. -/
theorem isParticipant_grounded :
    PersonNumber.p1sg.isParticipant = true ∧
    PersonNumber.p2sg.isParticipant = true ∧
    PersonNumber.p3sg.isParticipant = false ∧
    PersonNumber.p3pl.isParticipant = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 13: Verification Theorems — AF Agreement
-- ============================================================================

/-- The entire AF paradigm (table 22) is correctly predicted by the
    omnivorous hierarchy computation. Each empirical datum matches
    the output of `afMarker`. -/
theorem af_paradigm_correct :
    afParadigm.all (λ d => afMarker d.subject d.object == d.marker) = true := by
  native_decide

/-- AF agreement is commutative: swapping subject and object yields the
    same marker for ALL person-number combinations (@cite{preminger-2014},
    §3.3, (67)). This follows from the omnivorous hierarchy — the
    probe sees both arguments symmetrically. -/
theorem af_commutative :
    personNumbers.all (λ s => personNumbers.all (λ o =>
      afMarker s o == afMarker o s)) = true := by
  native_decide

/-- [+participant] outranks [+plural]: when one argument is 1st/2nd
    person and the other is 3PL, the marker reflects the participant,
    not the plural. -/
theorem participant_over_plural :
    afMarker .p1sg .p3pl = some "in-" ∧
    afMarker .p3pl .p2sg = some "at-" := ⟨rfl, rfl⟩

/-- Person restriction blocks two [+participant] arguments. -/
theorem person_restriction_blocks :
    afMarker .p1sg .p2sg = none ∧
    afMarker .p2sg .p1sg = none := ⟨rfl, rfl⟩

/-- Person restriction is symmetric. -/
theorem person_restriction_symmetric :
    personNumbers.all (λ s => personNumbers.all (λ o =>
      personRestrictionOk s o == personRestrictionOk o s)) = true := by
  native_decide

/-- Default 3SG: when both arguments are 3SG, the Elsewhere entry
    (∅) surfaces — the least specified vocabulary item. -/
theorem default_3sg : afMarker .p3sg .p3sg = some "∅" := rfl

-- ============================================================================
-- § 14: Verification Theorems — Verb Form Connection
-- ============================================================================

/-- AF has a single agreement slot (one marker from the ABS paradigm). -/
theorem af_single_slot : VerbForm.agentFocus.agreementSlots = 1 := rfl

/-- Transitive has dual agreement slots (Set A + Set B). -/
theorem trans_dual_slots : VerbForm.transitive.agreementSlots = 2 := rfl

/-- AF loses ergative (Set A) agreement: the single AF marker is drawn
    from the absolutive paradigm, not the ergative. Cross-references
    `VerbForm.hasSetA` from AgentFocus.lean. -/
theorem af_no_ergative :
    VerbForm.agentFocus.hasSetA = false ∧
    VerbForm.agentFocus.agreementSlots = 1 := ⟨rfl, rfl⟩

/-- Transitive retains ergative (Set A) agreement. -/
theorem trans_has_ergative :
    VerbForm.transitive.hasSetA = true ∧
    VerbForm.transitive.agreementSlots = 2 := ⟨rfl, rfl⟩

-- ============================================================================
-- § 15: Case Inventory Validation (@cite{blake-1994})
-- ============================================================================

/-- Kaqchikel case inventory, derived from argument position case values. -/
def caseInventory : List Core.Case := [.erg, .abs]

/-- The inventory covers all argument positions: every position's case
    is in the inventory. -/
theorem inventory_covers_positions :
    kaqArgPositions.all (λ p => caseInventory.any (· == p.case.toCase)) = true := by
  native_decide

/-- Kaqchikel's {ERG, ABS} inventory is valid per Blake's case hierarchy
    (both are core cases at rank 6, trivially no gaps). -/
theorem inventory_valid : Core.validInventory caseInventory = true := by native_decide

end Fragments.Mayan.Kaqchikel
