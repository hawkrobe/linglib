import Linglib.Features.Case.Basic
import Linglib.Features.Prominence
import Linglib.Fragments.Mayan.Mam.Pronouns
import Linglib.Fragments.Mayan.Params
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Syntax.Extraction

/-!
# Mam Agreement Fragment [scott-2023]
[deal-2024] [woolford-1997] [blake-1994]

Agreement morphology and pronoun realization data for **San Juan Atitán
Mam (SJA Mam)**, the dialect analyzed in [scott-2023]. Per Scott's
Chapter 3 (titled "Object licensing and agreement: SJA Mam is a
**tripartite high-abs language**"), SJA Mam exhibits morphologically
tripartite agreement alignment: S, A, and O each trigger distinct
marking patterns on the verb.

## Dialect-specificity and the analytical contrast

This fragment encodes Scott's analysis of SJA Mam specifically. Other
Mam dialects (notably Ixtahuacán Mam, the variety described in England
1983b and used by [zavala-maldonado-2017] §4-5) have been
characterized as **ergative with a neutral pattern in aspectless
dependent clauses** — NOT tripartite. Per Zavala 2017 §4 (p. 237),
"Ch'orti' is the only Mayan language that exhibits three sets of
pronominal markers" — making Ch'orti' the canonical tripartite Mayan
language under that framing.

Scott's tripartite analysis of SJA Mam is an **analytical contribution**
that uses a high-abs / Voice Licensing / Ergative Extraction Constraint
framework (her ch. 3 §3.4) to argue for tripartite case (ERG, ACC, ABS)
even though Mam lacks independent DP case morphology. Per Scott §1.2.4
(Mam dialect variation, p. 11) and Table 1.2 (Mam dialect groups,
citing Simon 2019), Mam dialects vary substantially; the SJA Mam
analysis may not extend directly to Ixtahuacán Mam.

## The System

Mam has two agreement paradigms on the verb:
- **Set A** (ERG): prefixes on Voice cross-referencing the transitive agent
- **Set B** (ABS): preverbal markers on Infl cross-referencing the absolutive
  argument (intransitive S). In transitives, Infl's φ-probe is blocked by
  transitive VoiceP and default Set B (∅/tz'=)
  appears instead.

In the default construction, transitive *objects* are not cross-referenced
by either set — they co-occur with default Set B (tz'=) and require
full overt pronouns. However, some speakers accept agreeing Set B
for objects as a more formal variant ([scott-2023], ch. 3, ex. 156).

## Case Licensing (per Scott's analysis)

Case is NOT assigned via dependent case. Instead:
- **ERG**: inherent case from Voice
- **ACC**: structural case from Voice (object licensing; low-abs syntax)
- **ABS**: structural case from Infl (high-abs morphology; for intransitive S)

This gives a tripartite underlying Case system (ERG, ACC, ABS) despite
Mam having no independent case morphology on DPs — case is visible only
through agreement patterns. This tripartite analysis is dialect-specific
to SJA Mam per Scott; alternative analyses (for other Mam dialects or
under different theoretical frameworks) characterize Mam as ergative
with neutral patterns in dependent clauses (England 1983b;
[zavala-maldonado-2017] §4-5).

## Argument Positions

| Position | Case | Agreement | Pronoun |
|----------|------|-----------|---------|
| A (transitive agent) | ERG (from Voice) | Set A | reduced/null |
| S (intransitive subj) | ABS (from Infl) | Set B | reduced/null |
| P (transitive patient) | ACC (from Voice) | default Set B | **overt** |

-/

namespace Mam

open Mayan (MarkerLinearity ExponentTable)
open Agreement

-- ============================================================================
-- § 1: Person-Number Inventory
-- ============================================================================

-- Person-number values are the canonical φ-cells `Agreement.Cell`
-- (six relevant cells: three persons × two numbers). Build them with
-- `Agreement.Cell.pn` (e.g. `.pn .first .Sing`); the six-cell inventory
-- is `Agreement.Cell.pnCells`.

-- ============================================================================
-- § 2: Agreement Marker Paradigms (theory-neutral)
-- ============================================================================

/-- Set A (ERG) markers per cell: prefixes/proclitics on the verb that
    cross-reference the transitive agent ([scott-2023], Table 2.8).
    All six cells have distinct exponents (with t- syncretism for 2sg/3sg
    and ky- syncretism for 2pl/3pl). -/
def setAExponent : ExponentTable :=
  [(.pn .first .Sing, "n-/w-"), (.pn .second .Sing, "t-"), (.pn .third .Sing, "t-"),
   (.pn .first .Plur, "q-"), (.pn .second .Plur, "ky-"), (.pn .third .Plur, "ky-")]

/-- Set B (ABS) markers per cell ([scott-2023], Table 3.5).
    The 2/3SG form tz'= is the **default** — it appears both for real
    agreement with a 2/3SG intransitive S and for default Set B in
    transitives when Infl's probe is blocked by VoiceP.

    Per Scott's DM analysis, 2sg and 3sg are NOT specific entries; they
    surface via the Elsewhere fallback. The total function below
    returns "tz'=" for both, but downstream Vocabulary construction
    should treat them as derived from the Elsewhere entry. See
    `setBSpecificCells` for the cells that have actual specific
    Vocabulary Items in the DM analysis. -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, "chin"), (.pn .second .Sing, "tz'="), (.pn .third .Sing, "tz'="),
   (.pn .first .Plur, "qo"), (.pn .second .Plur, "chi"), (.pn .third .Plur, "chi")]

/-- The four Set B cells that have specific Vocabulary Items (per
    Scott's DM analysis). 2sg and 3sg are NOT included — they fall
    through to the Elsewhere entry. -/
def setBSpecificCells : List Cell :=
  [.pn .first .Sing, .pn .first .Plur, .pn .second .Plur, .pn .third .Plur]

/-- The default (Elsewhere) Set B marker. Surfaces in transitives when
    Infl's probe is blocked, and also for 2/3SG intransitive S. -/
def defaultSetB : String := "tz'="

-- ============================================================================
-- § 2: Argument Positions and Agreement Status (substrate-anchored)
-- ============================================================================

/-- Argument positions in a Mam clause ([scott-2023] ch. 3).
    Aliased to the canonical `Features.Prominence.ArgumentRole`
    (S/A/P/R/T) so cross-Mayan and cross-framework code shares one
    inventory. Use the canonical constructor names `.A` / `.P` / `.S`
    directly. -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- The case each argument position receives. Definitionally equal to
    `Mayan.ergCaseMam`, which derives from
    `Alignment.tripartite.assignCase` in
    `Syntax/Case/Alignment.lean`: A → ERG (inherent from Voice),
    P → ACC (structural from Voice), S → ABS (structural from Infl).
    The three distinct cases are tripartite alignment per Scott's
    analysis (ch. 3 §3.4). -/
abbrev ArgPosition.case : ArgPosition → Case :=
  Mayan.ergCaseMam

/-- Does this argument position participate in φ-Agree?

    Agent: Voice probes for φ, finds agent in Spec,VoiceP → Set A
    Intransitive S: Infl probes for φ, finds S → Set B
    Patient: Infl's φ-probe has a disjunctive satisfaction condition
    [SAT: φ or Voice_TR]. In transitives, the
    probe encounters transitive Voice and stops — no φ-features are
    copied, and default Set B (the Elsewhere form) surfaces.
    Ditransitive R/T default to participating (not modeled). -/
def ArgPosition.IsPhiAgreed : ArgPosition → Prop
  | .A => True   -- φ-Agreed by Voice → Set A
  | .P => False  -- NOT φ-Agreed: Infl probe blocked by Voice_TR
  | .S | .R | .T => True   -- S φ-Agreed by Infl → Set B; R/T default

instance : DecidablePred ArgPosition.IsPhiAgreed := fun p => by
  cases p <;> unfold ArgPosition.IsPhiAgreed <;> infer_instance

-- ============================================================================
-- § 3: Pronoun Realization
-- ============================================================================

/-- Can a pronoun in this argument position undergo reduction?

    Scott's analysis (ch. 4, §4.4.3): first person pronouns in
    agreed-with positions are reduced via an impoverishment rule that
    deletes [±singular] in the context of [+author]^F (where F marks
    that the feature has been agreed with). This bleeds insertion of
    the pronominal base morphemes *qin* ([+author,+singular]) and *qo*
    ([+author,-singular]), leaving only the disagreement enclitic =i.

    Non-first person pronouns are NOT reduced — their subj/poss forms
    are identical to their independent forms (Table 4.25, p. 200).
    Whether actual reduction occurs depends on person (see
    `realizedPronoun`), but only agreed-with positions are eligible. -/
def ArgPosition.CanBeReduced (pos : ArgPosition) : Prop :=
  pos.IsPhiAgreed

instance : DecidablePred ArgPosition.CanBeReduced := fun pos => by
  unfold ArgPosition.CanBeReduced; exact inferInstance

/-- The three monotransitive argument positions. -/
def mamArgPositions : List ArgPosition := [.A, .P, .S]

-- ============================================================================
-- § 4: Per-Position Verification
-- ============================================================================

/-- Agent gets ERG (inherent, from Voice). -/
theorem A_case : ArgPosition.case .A = .erg := rfl

/-- Patient gets ACC (structural, from Voice). -/
theorem P_case : ArgPosition.case .P = .acc := rfl

/-- Intransitive S gets ABS (structural, from Infl). -/
theorem S_case : ArgPosition.case .S = .abs := rfl

/-- Three distinct underlying cases — morphologically tripartite.
    Inherits from `Alignment.tripartite_distinguishes_all` via the
    substrate connection. -/
theorem tripartite_alignment :
    ArgPosition.case .A ≠ ArgPosition.case .P ∧
    ArgPosition.case .A ≠ ArgPosition.case .S ∧
    ArgPosition.case .P ≠ ArgPosition.case .S :=
  Alignment.tripartite_distinguishes_all

/-- Reduction eligibility ≡ φ-agreement: an argument position is
    eligible for pronoun reduction iff it triggers agreement on the
    verb. By `CanBeReduced := IsPhiAgreed`, this is reflexivity. -/
theorem reduction_eligible_iff_phi_agreed (pos : ArgPosition) :
    pos.CanBeReduced ↔ pos.IsPhiAgreed :=
  Iff.rfl

-- ============================================================================
-- § 5: Case Inventory Validation ([blake-1994])
-- ============================================================================

/-- Mam case inventory, derived from argument position case values. -/
def caseInventory : Finset Case := {.erg, .acc, .abs}

/-- The inventory covers all argument positions. -/
theorem inventory_covers_positions :
    ∀ p ∈ mamArgPositions, p.case ∈ caseInventory := by decide

-- Mam's {ERG, ACC, ABS} inventory is valid per Blake's case hierarchy
-- (all are core cases at rank 6, trivially no gaps).
example : Case.IsValidInventory caseInventory := by decide

-- ============================================================================
-- § 6: Pronoun Internal Structure ([scott-2023], ch. 4)
-- ============================================================================

/-- φ-dimensions of the SJA Mam pronominal system ([scott-2023] Table 4.4,
    adopting [harbour-2016]'s bivalent features): [±author], [±participant],
    [±singular]. Per-cell *values* live in `Mam.ScottFeatures`
    (`Fragments/Mayan/Mam/Pronouns.lean`, where the disagreement
    distribution of the =i enclitic is verified); this enum names the
    *dimensions*, for the redundancy calculus below. -/
inductive PhiDimension where
  | author
  | participant
  | singular
  deriving DecidableEq, Repr

/-- Dimensions referenced by Set A/Set B agreement vocabulary items: only
    [±author] and [±singular] (Tables 4.7-4.8) — agreement never copies
    [±participant]. -/
def agreedDimensions : List PhiDimension := [.author, .singular]

/-- Dimensions realized by the pronominal base morphemes *qin*
    [+author,+sg] and *qo* [+author,−sg] (Table 4.10). -/
def baseDimensions : List PhiDimension := [.author, .singular]

/-- Dimensions whose disagreement the =i enclitic realizes
    ([noyer-1992]; [scott-2023] §4.3.3): [±author] and [±participant]. -/
def encliticDimensions : List PhiDimension := [.author, .participant]

/-- A dimension is copied back to the probe by agreement. -/
def PhiDimension.Copied (d : PhiDimension) : Prop := d ∈ agreedDimensions

instance : DecidablePred PhiDimension.Copied := fun d => by
  unfold PhiDimension.Copied; infer_instance

/-- The pronominal base is fully redundant under agreement: every dimension
    it realizes is copied — the configuration in which impoverishment bleeds
    base insertion (§4.4). -/
theorem base_is_redundant : ∀ d ∈ baseDimensions, d.Copied := by decide

/-- The =i enclitic is not fully redundant: [±participant] is never copied
    by agreement — so the enclitic survives reduction. -/
theorem enclitic_survives : ¬ (∀ d ∈ encliticDimensions, d.Copied) := by decide

/-- Pronoun realization by argument position ([scott-2023], her (3)/(8):
    nominative alignment of reduction). φ-agreed positions (A, S — and
    possessors) take the subject/possessor series; the unagreed object
    position takes the independent series. The impoverishment rule
    (ex. 84/94) `[±singular] → ∅ / [+author]^F` targets [+author] features
    bearing the agreed-with diacritic F, bleeding insertion of the bases
    *qin*/*qo* — so agreed-with first person surfaces as bare *=i*
    (or ∅ for 1PL.INCL), while everything else keeps its independent
    form. Realization is *selection among the API's `PersonalPronoun`
    entries*, not a separate form classification. -/
def realizedPronoun (pos : ArgPosition) (c : PronCell) : Option PersonalPronoun :=
  if pos.IsPhiAgreed then subjPoss c else independent c

/-- 1SG agent: reduced to the bare disagreement enclitic (base bled by
    impoverishment). -/
theorem first_A_reduced :
    realizedPronoun .A .firstSg = some iDisagr := by decide

/-- 1SG intransitive subject: likewise reduced (Set B agreement). -/
theorem first_S_reduced :
    realizedPronoun .S .firstSg = some iDisagr := by decide

/-- 1SG patient: the full independent pronoun *qini* (no agreement → no
    F diacritic → no impoverishment). -/
theorem first_P_full :
    realizedPronoun .P .firstSg = some qini := by decide

/-- 2SG agent: unreduced — *=i* IS the independent 2SG form (Scott's
    fn. 2), so the agreed-with cell coincides with the independent one. -/
theorem second_A_unreduced :
    realizedPronoun .A .secondSg = independent .secondSg := by decide

/-- 3PL agent: full *qa* (impoverishment does not apply to [−author]). -/
theorem third_A_full :
    realizedPronoun .A .thirdPl = some qa := by decide

/-- The nominative-alignment contrast: the same 1SG argument is *=i* as
    agent but *qini* as patient. -/
theorem first_A_vs_P :
    realizedPronoun .A .firstSg ≠ realizedPronoun .P .firstSg := by decide

/-- Agreed-with first person differs from agreed-with third person — the
    impoverishment rule targets [+author] only. -/
theorem first_vs_nonfirst_asymmetry :
    realizedPronoun .A .firstSg ≠ realizedPronoun .A .thirdSg ∧
    realizedPronoun .S .firstSg ≠ realizedPronoun .S .thirdSg := by
  exact ⟨by decide, by decide⟩

/-- The unagreed object position realizes the independent series, for
    every cell — person is irrelevant without the F diacritic. -/
theorem patient_takes_independent (c : PronCell) :
    realizedPronoun .P c = independent c := by
  cases c <;> decide

-- ============================================================================
-- § 7: Mayan Absolutive Parameter
-- ============================================================================

/-- Mam is HIGH-ABS: Set B (absolutive) markers appear pre-stem on Infl,
    immediately following the aspect marker. Morpheme template:
    ASP-**ABS**-ERG-ROOT-SUFFIX ([scott-2023], §2.5.1). -/
def absPosition : Mayan.ABSPosition := .high

/-- HIGH-ABS yields ABS=NOM case locus: Infl assigns case to the
    absolutive argument ([scott-2023], §3.3). -/
theorem mam_case_locus :
    Mayan.toCaseLocus absPosition = .absNom := rfl

/-- Set A linearity: prefixal (per [scott-2023] ch. 2; pan-Mayan). -/
def setALinearity : MarkerLinearity := .prefixal

/-- Set B linearity: prefixal (HIGH-ABS Mam morphology; pre-stem on Infl,
    per [scott-2023] §2.5.1). -/
def setBLinearity : MarkerLinearity := .prefixal

/-- Mam's extraction strategy: AF morphology is productive in SJA Mam
    ([scott-2023] §2.5.4.1 ex. 169 + §2.7.1 syntactic ergativity).
    The construction combines the antipassive suffix *-(a)n* with the
    AF-specific suffix *-ta* (e.g., `b'yo-n-ta` 'hit-AP-AF'), making
    SJA Mam's AF morphologically distinct from K'iche''s (which uses
    bare antipassive *-n* in AF contexts per [mondloch-2017]
    Lesson 22 — no extra AF morpheme).

    For the cross-Mayan typology, we mark the strategy as
    `dedicatedMorpheme` (the descriptive surface category) to parallel
    Q'anjob'al/Kaqchikel/K'iche'. The analytical claim that AF is an
    SSAL repair (Erlewine-line) lives in
    `Studies/Erlewine2016.lean`; rival accounts
    (Coon-Mateo Pedro-Preminger absolutive licensing, Coon-Keine
    Feature Gluttony) are not encoded in the typology enum.

    Language: "Mam (SJA)". Notes: AF (-(a)n + -ta) for A-extraction;
    HIGH-ABS tripartite Mam (Scott 2023 §2.5.4.1). -/
def extractionStrategy : Extraction.ExtractionMarkingStrategy := .dedicatedMorpheme
def extractionMarkedPositions : List Extraction.ExtractionTarget := [.subject]
def extractionDistinguishesPosition : Bool := true

-- ============================================================================
-- § 8: Theory-Neutral Marker Verification
-- ============================================================================

/-- Set A 1SG marker. -/
theorem setA_1sg : setAExponent.realize (.pn .first .Sing) = some "n-/w-" := rfl

/-- Set A 3SG marker is "t-" (the default singular Set A — syncretic with 2SG). -/
theorem setA_3sg : setAExponent.realize (.pn .third .Sing) = some "t-" := rfl

/-- Set B 1SG marker is "chin". -/
theorem setB_1sg : setBExponent.realize (.pn .first .Sing) = some "chin" := rfl

/-- Set B 3SG marker is the default "tz'=". -/
theorem setB_3sg : setBExponent.realize (.pn .third .Sing) = some defaultSetB := rfl

/-- A controller's φ-features index the agreement paradigm directly: a 1sg agent
    selects its first-person-singular ergative prefix. The Set A table
    (`setAExponent`) is keyed by canonical φ-cells, so a pronoun's `Word.agrCell`
    drives agreement realization in one shared feature space ([corbett-1998];
    [scott-2023] Ch. 2). The realizational account (impoverishment /
    Elsewhere; [scott-2023] Ch. 4) is theory and stays in the study. -/
theorem erg_1sg_from_phi :
    setAExponent.realizeFor
      { form :="", cat := .PRON, features := { person := some .first, number := some .Sing }} = some "n-/w-" := by
  rfl

end Mam
