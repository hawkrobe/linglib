import Linglib.Fragments.Mayan.Kaqchikel.AgentFocus
import Linglib.Features.Case.Basic
import Linglib.Features.Prominence
import Linglib.Fragments.Mayan.Params

/-!
# Kaqchikel Agreement Fragment [preminger-2014]

Theory-neutral typological metadata for Kaqchikel (K'ichean, Mayan)
agreement morphology: paradigm exponents, person-number cells, argument
positions, and the empirical AF agreement table.

The theory-laden apparatus that interprets this data — DM Vocabulary
insertion (`setAVocab`/`setBVocab`), Phi.Geometry feature
decomposition (`IsParticipant`), and the two-probe choice rule
(`afRank`, `afMarker`) — lives in
`Studies/Preminger2014.lean`. Per the project
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
arguments ([preminger-2014] Ch. 3 vs. [scott-2023] for Mam).

## Agent Focus Agreement ([preminger-2014] §3.3, table 22)

In AF constructions (clause-local agent extraction), the normal two-slot
agreement collapses to a **single marker** drawn from the absolutive
(Set B) paradigm. The empirical pattern: AF agreement is **commutative**
(⟨1SG subj, 3SG obj⟩ = ⟨3SG subj, 1SG obj⟩ → *in-*) and a person
restriction blocks combinations of two 1st/2nd-person arguments.

The empirical paradigm data sits here as `afParadigm`. The choice rule
that predicts it is theory-laden — see
`Studies/Preminger2014.lean` for the two-probe
relativized-probing derivation (after [bejar-rezac-2003], applied
to Kichean per [preminger-2014] §4.4). Earlier analyses
([stiebels-2006] and others) framed the same surface pattern as
a salience hierarchy `[+participant] > [+plural] > default`, an account
[preminger-2014] Ch. 7 explicitly argues against; the fragment
deliberately avoids picking sides on that question.

-/

namespace Kaqchikel

open Mayan (ExponentTable)
open Agreement

-- ============================================================================
-- § 1: Person-Number Inventory
-- ============================================================================

-- Person-number combinations for Kaqchikel agreement paradigms come from
-- the canonical φ-cell `Agreement.Cell` (six cells: three persons × two
-- numbers). Projections `.toPerson`, `.isPlural`, and the inventory
-- `Agreement.Cell.pnCells` live in `Syntax/Agreement/Paradigm.lean`.

-- ============================================================================
-- § 1b: ABS Position (LOW-ABS / HIGH-ABS)
-- ============================================================================

/-- Kaqchikel's absolutive morphemes appear in HIGH position (between
    aspect marker and the verb stem, pre-stem). Morpheme order:
    ASP-ABS-ERG-Stem (per `## The System` table above). -/
def absPosition : Mayan.ABSPosition := .high

-- ============================================================================
-- § 2: Set A (ERG) Vocabulary
-- ============================================================================

/-- Set A (ERG) markers: prefixes on Voice/v cross-referencing the
    transitive agent ([preminger-2014] Ch. 3, table (29)).
    Parenthesized segments are dropped in certain phonological
    contexts; the grapheme *j* represents a voiceless velar fricative. -/
def setAExponent : ExponentTable :=
  [(.pn .first .Sing, "n/w-"), (.pn .second .Sing, "a(w)-"), (.pn .third .Sing, "r(u)/u-"),
   (.pn .first .Plur, "q(a)-"), (.pn .second .Plur, "i(w)-"), (.pn .third .Plur, "k(i)-")]

-- ============================================================================
-- § 3: Set B (ABS) Vocabulary
-- ============================================================================

/-- Set B (ABS) markers: preverbal markers on Infl/T cross-referencing
    the absolutive argument. The 3SG form (∅) is
    also the Elsewhere entry — the default when no more specific entry
    matches, as in the failure case of obligatory agreement (Ch. 5).
    Citation forms: 1SG and 2SG are *i(n)-* and *a(t)-*, whose
    parenthesized segments drop in certain phonological contexts
    (e.g., 1SG surfaces as *i-* in *x-i-tz'et-ö*). -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, "in-"), (.pn .second .Sing, "at-"), (.pn .third .Sing, "∅"),
   (.pn .first .Plur, "oj-"), (.pn .second .Plur, "ix-"), (.pn .third .Plur, "e-")]

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
    equal to `Mayan.ergCaseKaqchikel`, which derives from
    `Alignment.ergative.assignCase` in
    `Syntax/Case/Alignment.lean` — A → ERG, S/P → ABS. -/
abbrev ArgPosition.case : ArgPosition → Case :=
  Mayan.ergCaseKaqchikel

/-- Non-perfective (PROG `ajin`) case assignment for Kaqchikel.
    Definitionally equal to `Mayan.accCaseKaqchikel`, derived
    from `Alignment.invertedErgative.assignCase`. The
    construction-specific inverted pattern (S/A → ABS, P → ERG/GEN)
    documented by [imanishi-2014] §3.3.1 and [imanishi-2020].
    Per [imanishi-2014]: the Unaccusative Requirement on
    Nominalization passivizes the embedded clause; the object becomes
    the only Case-less DP and receives ERG/GEN from D as phase head;
    the subject is base-generated in matrix Spec-PredP (with `ajin`)
    and gets ABS from matrix Infl. -/
abbrev ArgPosition.accCase : ArgPosition → Case :=
  Mayan.accCaseKaqchikel

/-- Does this position participate in φ-Agree?
    In Kaqchikel, ALL core argument positions trigger agreement:
    agent via Set A on Voice/v, patient and intranS via Set B on
    Infl/T. This contrasts with Mam, where the patient is NOT
    agreed with (Infl's probe is blocked by VoiceP; [scott-2023]).
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
-- § 5: AF Agreement Paradigm Data ([preminger-2014] table 22)
-- ============================================================================

/-- An AF agreement datum: subject φ, object φ, and the resulting
    single agreement marker (or `none` for person-restriction
    violations). -/
structure AFAgreementDatum where
  subject : Cell
  object : Cell
  marker : Option String
  deriving Repr

/-- The empirical AF agreement paradigm ([preminger-2014] table (22)).
    Each row records the observed agreement marker for a given
    subject-object combination in clause-local agent extraction.

    The first 11 rows reproduce the paper's table exactly. Rows 12–15
    demonstrate commutativity (§3.2, fn. a): the table uses set notation
    {φ₁, φ₂}, so swapping subj/obj yields the same marker. Rows 16–17
    test person restriction violations ((25)). -/
def afParadigm : List AFAgreementDatum :=
  [ -- Table (22), rows 1–3: both 3rd person, number determines marker
    ⟨.pn .third .Sing, .pn .third .Sing, some "∅"⟩         -- default: 3SG×3SG → ∅
  , ⟨.pn .third .Plur, .pn .third .Sing, some "e-"⟩        -- [+plural] outranks default
  , ⟨.pn .third .Plur, .pn .third .Plur, some "e-"⟩        -- [+plural] both → 3PL
    -- Table (22), rows 4–7: one [+participant] argument with 3SG
  , ⟨.pn .first .Sing, .pn .third .Sing, some "in-"⟩       -- 1SG [+participant]
  , ⟨.pn .second .Sing, .pn .third .Sing, some "at-"⟩      -- 2SG [+participant]
  , ⟨.pn .first .Plur, .pn .third .Sing, some "oj-"⟩       -- 1PL [+participant]
  , ⟨.pn .second .Plur, .pn .third .Sing, some "ix-"⟩      -- 2PL [+participant]
    -- Table (22), rows 8–11: [+participant] outranks [+plural]
  , ⟨.pn .first .Sing, .pn .third .Plur, some "in-"⟩       -- 1SG participant > 3PL plural
  , ⟨.pn .second .Sing, .pn .third .Plur, some "at-"⟩      -- 2SG participant > 3PL plural
  , ⟨.pn .first .Plur, .pn .third .Plur, some "oj-"⟩       -- 1PL participant > 3PL plural
  , ⟨.pn .second .Plur, .pn .third .Plur, some "ix-"⟩      -- 2PL participant > 3PL plural
    -- Commutativity (§3.2, fn. a): swapping subj/obj → same marker
  , ⟨.pn .third .Sing, .pn .third .Plur, some "e-"⟩        -- = {3PL, 3SG} swapped
  , ⟨.pn .third .Sing, .pn .first .Sing, some "in-"⟩       -- = {1SG, 3SG} swapped
  , ⟨.pn .third .Sing, .pn .second .Sing, some "at-"⟩      -- = {2SG, 3SG} swapped
  , ⟨.pn .third .Plur, .pn .second .Sing, some "at-"⟩      -- = {2SG, 3PL} swapped
    -- Person restriction violations (25)
  , ⟨.pn .first .Sing, .pn .second .Sing, none⟩            -- *two [+participant] args
  , ⟨.pn .second .Sing, .pn .first .Sing, none⟩            -- *two [+participant] args
  ]

-- The per-form agreement slot count (transitive 2, AF 1) is the pan-Mayan
-- `Mayan.VerbForm.agreementSlots`, derived from `hasSetA` in
-- `Fragments/Mayan/Params.lean`; the AF slot's single marker is drawn from
-- the ABS paradigm (`afParadigm` above).

-- ============================================================================
-- § 6: Verification Theorems — Argument Positions
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
-- § 7: Case Inventory Validation ([blake-1994])
-- ============================================================================

/-- Kaqchikel case inventory, derived from argument position case values. -/
def caseInventory : Finset Case := {.erg, .abs}

/-- The inventory covers all argument positions: every position's case
    is in the inventory. -/
theorem inventory_covers_positions :
    ∀ p ∈ kaqArgPositions, p.case ∈ caseInventory := by decide

-- Kaqchikel's {ERG, ABS} inventory is valid per Blake's case hierarchy
-- (both are core cases at rank 6, trivially no gaps).
example : Case.IsValidInventory caseInventory := by decide

end Kaqchikel
