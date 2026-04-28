import Linglib.Fragments.Mayan.Kaqchikel.AgentFocus
import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
import Linglib.Features.Prominence
import Linglib.Fragments.Mayan.Params

/-!
# Kaqchikel Agreement Fragment @cite{preminger-2014}

Theory-neutral typological metadata for Kaqchikel (K'ichean, Mayan)
agreement morphology: paradigm exponents, person-number cells, argument
positions, and the empirical AF agreement table.

The theory-laden apparatus that interprets this data — DM Vocabulary
insertion, PersonGeometry feature decomposition, the omnivorous
hierarchy, the AgreeOutcome inductive — lives in
`Phenomena/Agreement/Studies/Preminger2014.lean`. Per the project
Fragment-discipline rule (CLAUDE.md), fragments hold only consensus
typological metadata; paper-specific apparatus is consumed in study
files via projections.

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
arguments (@cite{preminger-2014} Ch. 3 vs. @cite{scott-2023} for Mam).

## Agent Focus Agreement (@cite{preminger-2014} §3.3, table 22)

In AF constructions (clause-local agent extraction), the normal two-slot
agreement collapses to a **single marker** drawn from the absolutive
(Set B) paradigm. The empirical pattern: AF agreement is **commutative**
(⟨1SG subj, 3SG obj⟩ = ⟨3SG subj, 1SG obj⟩ → *in-*) and a person
restriction blocks combinations of two 1st/2nd-person arguments.

The empirical paradigm data sits here as `afParadigm`. The choice rule
that predicts it is theory-laden — see
`Phenomena/Agreement/Studies/Preminger2014.lean` for the two-probe
relativized-probing derivation (after @cite{bejar-rezac-2003}, applied
to Kichean per @cite{preminger-2014} §4.4). Earlier analyses
(@cite{stiebels-2006} and others) framed the same surface pattern as
a salience hierarchy `[+participant] > [+plural] > default`, an account
@cite{preminger-2014} Ch. 7 explicitly argues against; the fragment
deliberately avoids picking sides on that question.

-/

namespace Fragments.Mayan.Kaqchikel

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

/-- Person value as `PersonLevel` (the canonical person type). -/
def PersonNumber.person : PersonNumber → Features.Prominence.PersonLevel
  | .p1sg | .p1pl => .first
  | .p2sg | .p2pl => .second
  | .p3sg | .p3pl => .third

/-- Is this person-number [+plural]? -/
def PersonNumber.isPlural : PersonNumber → Bool
  | .p1pl | .p2pl | .p3pl => true
  | .p1sg | .p2sg | .p3sg => false

-- ============================================================================
-- § 2: Set A (ERG) Vocabulary
-- ============================================================================

/-- Set A (ERG) markers: prefixes on Voice/v cross-referencing the
    transitive agent (@cite{preminger-2014} Ch. 3, table (29)).
    Parenthesized segments are dropped in certain phonological
    contexts; the grapheme *j* represents a voiceless velar fricative. -/
def setAExponent : PersonNumber → String
  | .p1sg => "n/w-"
  | .p2sg => "a(w)-"
  | .p3sg => "r(u)/u-"
  | .p1pl => "q(a)-"
  | .p2pl => "i(w)-"
  | .p3pl => "k(i)-"

-- ============================================================================
-- § 3: Set B (ABS) Vocabulary
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

-- ============================================================================
-- § 4: Argument Positions (alias to canonical SAP type)
-- ============================================================================

/-- Argument positions in a Kaqchikel clause. Aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T) so cross-Mayan and
    cross-framework code shares one inventory. Use the canonical
    constructor names `.A` (transitive agent), `.P` (transitive
    patient), `.S` (intransitive subject) directly. -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Perfective (ergative) case assignment for Kaqchikel. Definitionally
    equal to `Fragments.Mayan.ergCaseKaqchikel`, which derives from
    `Alignment.ergative.assignCase` in
    `Theories/Syntax/Case/Alignment.lean` — A → ERG, S/P → ABS. -/
abbrev ArgPosition.case : ArgPosition → Core.Case :=
  Fragments.Mayan.ergCaseKaqchikel

/-- Non-perfective (PROG `ajin`) case assignment for Kaqchikel.
    Definitionally equal to `Fragments.Mayan.accCaseKaqchikel`, derived
    from `Alignment.invertedErgative.assignCase`. The
    construction-specific inverted pattern (S/A → ABS, P → ERG/GEN)
    documented by @cite{imanishi-2014} §3.3.1 and @cite{imanishi-2020}.
    Per @cite{imanishi-2014}: the Unaccusative Requirement on
    Nominalization passivizes the embedded clause; the object becomes
    the only Case-less DP and receives ERG/GEN from D as phase head;
    the subject is base-generated in matrix Spec-PredP (with `ajin`)
    and gets ABS from matrix Infl. -/
abbrev ArgPosition.accCase : ArgPosition → Core.Case :=
  Fragments.Mayan.accCaseKaqchikel

/-- Does this position participate in φ-Agree?
    In Kaqchikel, ALL core argument positions trigger agreement:
    agent via Set A on Voice/v, patient and intranS via Set B on
    Infl/T. This contrasts with Mam, where the patient is NOT
    agreed with (Infl's probe is blocked by VoiceP; @cite{scott-2023}).
    Ditransitive R/T default to participating (Kaqchikel ditransitive
    agreement not modeled in this fragment). -/
def ArgPosition.IsPhiAgreed : ArgPosition → Prop
  | .A | .P | .S | .R | .T => True

instance : DecidablePred ArgPosition.IsPhiAgreed := fun p =>
  match p with
  | .A | .P | .S | .R | .T => isTrue trivial

/-- The three monotransitive argument positions (omits ditransitive R/T). -/
def kaqArgPositions : List ArgPosition := [.A, .P, .S]

-- ============================================================================
-- § 5: AF Agreement Paradigm Data (@cite{preminger-2014} table 22)
-- ============================================================================

/-- An AF agreement datum: subject φ, object φ, and the resulting
    single agreement marker (or `none` for person-restriction
    violations). -/
structure AFAgreementDatum where
  subject : PersonNumber
  object : PersonNumber
  marker : Option String
  deriving Repr

/-- The empirical AF agreement paradigm (@cite{preminger-2014} table (22)).
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
-- § 6: Agreement Slot Count
-- ============================================================================

/-- Number of agreement slots for each verb form.
    Transitive: two slots (Set A + Set B).
    AF: one slot (single omnivorous marker from the ABS paradigm). -/
def VerbForm.agreementSlots : VerbForm → Nat
  | .transitive => 2
  | .agentFocus => 1

-- ============================================================================
-- § 7: Verification Theorems — Argument Positions
-- ============================================================================

/-- Agent gets ERG (from Voice). -/
theorem A_case : ArgPosition.case .A = .erg := rfl

/-- Patient gets ABS (from Infl). -/
theorem P_case : ArgPosition.case .P = .abs := rfl

/-- Intransitive S gets ABS (from Infl). -/
theorem S_case : ArgPosition.case .S = .abs := rfl

/-- Ergative-absolutive alignment: the agent is distinguished (ERG)
    while patient and intranS share a case value (ABS). -/
theorem erg_abs_alignment :
    ArgPosition.case .A ≠ ArgPosition.case .P ∧
    ArgPosition.case .P = ArgPosition.case .S :=
  ⟨by decide, rfl⟩

/-- Accusative alignment in non-perfective: S/A pattern together (ABS),
    O is distinct (GEN). Mirror image of Chol/Q'anjob'al. -/
theorem acc_alignment :
    ArgPosition.accCase .A = ArgPosition.accCase .S ∧
    ArgPosition.accCase .A ≠ ArgPosition.accCase .P :=
  ⟨rfl, by decide⟩

/-- All three argument positions trigger φ-agreement. -/
theorem all_positions_agreed (p : ArgPosition) (_ : p ∈ kaqArgPositions) :
    ArgPosition.IsPhiAgreed p := by
  cases p <;> trivial

-- ============================================================================
-- § 8: Verification Theorems — Verb Form Connection
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
-- § 9: Case Inventory Validation (@cite{blake-1994})
-- ============================================================================

/-- Kaqchikel case inventory, derived from argument position case values. -/
def caseInventory : Finset Core.Case := {.erg, .abs}

/-- The inventory covers all argument positions: every position's case
    is in the inventory. -/
theorem inventory_covers_positions :
    ∀ p ∈ kaqArgPositions, p.case ∈ caseInventory := by decide

-- Kaqchikel's {ERG, ABS} inventory is valid per Blake's case hierarchy
-- (both are core cases at rank 6, trivially no gaps).
example : Core.Case.IsValidInventory caseInventory := by decide

end Fragments.Mayan.Kaqchikel
