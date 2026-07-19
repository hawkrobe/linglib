import Linglib.Features.Case.Basic
import Linglib.Phonology.Segmental.Defs
import Linglib.Features.Prominence
import Linglib.Fragments.Mayan.Mam.Pronouns
import Linglib.Fragments.Mayan.Params
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Syntax.Extraction

/-!
# Mam Agreement Fragment

Agreement morphology and pronoun realization data for San Juan Atitán
Mam (SJA Mam, Mayan), following [scott-2023]. SJA Mam has morphologically
tripartite agreement alignment — S, A, and O each trigger distinct
verbal marking (Scott's ch. 3, "Object licensing and agreement: SJA Mam
is a tripartite high-abs language") — realized through two paradigms:
Set A (ERG) prefixes on Voice cross-referencing the transitive agent,
and Set B (ABS) preverbal markers on Infl cross-referencing the
absolutive (intransitive S). Transitive objects are cross-referenced by
neither set: they co-occur with default Set B (tz'=) and require full
overt pronouns, though some speakers accept agreeing Set B for objects
as a more formal variant ([scott-2023] ch. 3, ex. 156).

## Main declarations

* `Mam.setAExponent`, `Mam.setBExponent`: the Set A (ERG) and Set B
  (ABS) exponent tables ([scott-2023] Tables 2.8, 3.5).
* `Mam.ArgPosition` with `.case`, `.IsPhiAgreed`, `.CanBeReduced`:
  argument positions, their tripartite case values, φ-agreement status,
  and reduction eligibility.
* `Mam.PhiDimension` with `.Copied`, `agreedDimensions`,
  `baseDimensions`, `encliticDimensions`: the φ-feature redundancy
  calculus behind pronoun reduction.
* `Mam.realizedPronoun`: pronoun realization by argument position, as a
  selection among the shared `PersonalPronoun` entries.
* `Mam.caseInventory`: the {ERG, ACC, ABS} inventory, validated against
  [blake-1994]'s hierarchy.
* `Mam.absPosition`: HIGH-ABS morpheme placement (extraction marking
  lives in `Mam/Extraction.lean`).

## Implementation notes

This fragment encodes Scott's tripartite analysis of SJA Mam
specifically — an analytical contribution using a high-abs / Voice
Licensing / Ergative Extraction Constraint framework ([scott-2023] ch. 3
§3.4) to argue for tripartite case (ERG, ACC, ABS) even though Mam lacks
independent DP case morphology; case is visible only through agreement.
Other Mam dialects (notably Ixtahuacán Mam, described in England 1983b
and used by [zavala-maldonado-2017] §4-5) are characterized as ergative
with a neutral pattern in aspectless dependent clauses — not tripartite;
per [zavala-maldonado-2017] §4 (p. 237), "Ch'orti' is the only Mayan
language that exhibits three sets of pronominal markers", the canonical
tripartite Mayan language under that framing. Per [scott-2023] §1.2.4
and Table 1.2 (citing Simon 2019), Mam dialects vary substantially, so
the SJA analysis may not extend to Ixtahuacán Mam.

Case is not dependent case ([scott-2023]; cf. [woolford-1997],
[deal-2024]): ERG is inherent case from Voice, ACC structural case from
Voice (object licensing, low-abs syntax), ABS structural case from Infl
(high-abs morphology, for intransitive S). In transitives, Infl's φ-probe
is blocked by transitive VoiceP and default Set B (∅/tz'=) surfaces.
Person-number cells are the canonical φ-cells `Agreement.Cell`
(`Syntax/Agreement/Paradigm.lean`), built with `Agreement.Cell.pn` (the
six-cell inventory `Agreement.Cell.pnCells`); per-cell pronoun feature
values live in `Mam.ScottFeatures` (`Fragments/Mayan/Mam/Pronouns.lean`).
-/

namespace Mam

open Mayan (MarkerLinearity ExponentTable)
open Agreement
open Features.Prominence (ArgumentRole)

/-! ### Agreement marker paradigms -/

/-- Set A (ERG) markers cross-referencing the transitive agent
    ([scott-2023] Table 2.8) by following-segment environment; t- is
    syncretic for 2/3SG, ky- for 2/3PL. Scott: 1SG is the sole Set A
    allomorphy — pre-consonantal `n-`, pre-vocalic `w-` (exx. (28)-(29));
    the other markers do not alternate. -/
def setAExponent : Phonology.SegmentClass → ExponentTable
  | .consonant =>
    [(.pn .first .Sing, [.pref "n"]), (.pn .second .Sing, [.pref "t"]),
     (.pn .third .Sing, [.pref "t"]), (.pn .first .Plur, [.pref "q"]),
     (.pn .second .Plur, [.pref "ky"]), (.pn .third .Plur, [.pref "ky"])]
  | .vowel =>
    [(.pn .first .Sing, [.pref "w"]), (.pn .second .Sing, [.pref "t"]),
     (.pn .third .Sing, [.pref "t"]), (.pn .first .Plur, [.pref "q"]),
     (.pn .second .Plur, [.pref "ky"]), (.pn .third .Plur, [.pref "ky"])]

/-- Set B (ABS) markers ([scott-2023] Table 3.5). The 2/3SG form tz'= is
    the Elsewhere default: it realizes both real 2/3SG intransitive-S
    agreement and default Set B in transitives when Infl's probe is
    blocked by VoiceP. Per Scott's DM analysis 2SG and 3SG are not
    specific Vocabulary Items but surface via Elsewhere fallback (see
    `setBSpecificCells`). -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, [.free "chin"]), (.pn .second .Sing, [.procl "tz'"]),
   (.pn .third .Sing, [.procl "tz'"]), (.pn .first .Plur, [.free "qo"]),
   (.pn .second .Plur, [.free "chi"]), (.pn .third .Plur, [.free "chi"])]

/-- The four Set B cells with specific Vocabulary Items ([scott-2023]);
    2SG and 3SG fall through to the Elsewhere entry. -/
def setBSpecificCells : List Cell :=
  [.pn .first .Sing, .pn .first .Plur, .pn .second .Plur, .pn .third .Plur]

/-- The Elsewhere Set B marker, surfacing in transitives when Infl's
    probe is blocked and for 2/3SG intransitive S. -/
def defaultSetB : Morphology.Exponent := [.procl "tz'"]

/-! ### Argument positions and agreement status -/

/-- Argument positions, aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T) ([scott-2023] ch. 3). -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Tripartite case assignment: `Mayan.ergCaseMam` (A → ERG inherent
    from Voice, P → ACC structural from Voice, S → ABS structural from
    Infl; [scott-2023] ch. 3 §3.4). -/
abbrev ArgPosition.case : ArgPosition → Case :=
  Mayan.ergCaseMam

/-- Whether a position triggers φ-Agree. A is probed by Voice (→ Set A),
    S by Infl (→ Set B); the transitive patient is not, because Infl's
    φ-probe has a disjunctive satisfaction condition [SAT: φ or Voice_TR]
    and stops at transitive Voice before copying features, so default Set
    B surfaces. R/T default to participating (not modeled). -/
def ArgPosition.IsPhiAgreed : ArgPosition → Prop
  | .A => True   -- φ-Agreed by Voice → Set A
  | .P => False  -- NOT φ-Agreed: Infl probe blocked by Voice_TR
  | .S | .R | .T => True   -- S φ-Agreed by Infl → Set B; R/T default

instance : DecidablePred ArgPosition.IsPhiAgreed := fun p => by
  cases p <;> unfold ArgPosition.IsPhiAgreed <;> infer_instance

/-! ### Pronoun reduction eligibility -/

/-- Whether a pronoun here is eligible for reduction (≡ φ-agreement).
    Under Scott's analysis (ch. 4 §4.4.3), agreed-with first-person
    pronouns undergo an impoverishment rule deleting [±singular] in the
    context of [+author]^F (F = agreed-with), bleeding the base morphemes
    *qin* [+author,+sg] and *qo* [+author,−sg] and leaving only the
    disagreement enclitic =i; non-first-person pronouns are not reduced,
    their subject/possessor forms matching the independent ones
    ([scott-2023] Table 4.25, p. 200). Only agreed-with positions are
    eligible; whether reduction actually applies depends on person (see
    `realizedPronoun`). -/
def ArgPosition.CanBeReduced (pos : ArgPosition) : Prop :=
  pos.IsPhiAgreed

instance : DecidablePred ArgPosition.CanBeReduced := fun pos => by
  unfold ArgPosition.CanBeReduced; exact inferInstance

/-! ### Per-position verification -/

-- The per-position case facts are the tripartite-alignment facts
-- (`Alignment.tripartite`) — SJA Mam's case function is
-- `Alignment.tripartite.assignCase` by definition, so each theorem below
-- is a re-export of the substrate lemma.

/-- Agent gets ERG (inherent, from Voice). -/
theorem A_case : ArgPosition.case .A = .erg := Alignment.tripartite.assignCase_A

/-- Patient gets ACC (structural, from Voice). -/
theorem P_case : ArgPosition.case .P = .acc := Alignment.tripartite.assignCase_P

/-- Intransitive S gets ABS (structural, from Infl). -/
theorem S_case : ArgPosition.case .S = .abs := Alignment.tripartite.assignCase_S

/-- Three distinct underlying cases (morphologically tripartite),
    inherited from `Alignment.tripartite_distinguishes_all`. -/
theorem tripartite_alignment :
    ArgPosition.case .A ≠ ArgPosition.case .P ∧
    ArgPosition.case .A ≠ ArgPosition.case .S ∧
    ArgPosition.case .P ≠ ArgPosition.case .S :=
  Alignment.tripartite_distinguishes_all

/-- Reduction eligibility coincides with φ-agreement — reflexivity,
    since `CanBeReduced := IsPhiAgreed`. -/
theorem reduction_eligible_iff_phi_agreed (pos : ArgPosition) :
    pos.CanBeReduced ↔ pos.IsPhiAgreed :=
  Iff.rfl

/-! ### Case inventory ([blake-1994]) -/

/-- The case inventory realized by the core positions: {ERG, ACC, ABS}. -/
def caseInventory : Finset Case := (ArgumentRole.core.map ArgPosition.case).toFinset

/-- The inventory covers all argument positions. -/
theorem inventory_covers_positions :
    ∀ p ∈ ArgumentRole.core, ArgPosition.case p ∈ caseInventory := by decide

-- Mam's {ERG, ACC, ABS} inventory is valid per Blake's case hierarchy
-- (all are core cases at rank 6, trivially no gaps).
example : Case.IsValidInventory caseInventory := by decide

/-! ### Pronoun internal structure ([scott-2023] ch. 4) -/

/-- The three φ-dimensions of the SJA Mam pronominal system ([scott-2023]
    Table 4.4, after [harbour-2016]'s bivalent features): [±author],
    [±participant], [±singular]. This enum names the dimensions for the
    redundancy calculus below; per-cell values live in `Mam.ScottFeatures`
    (`Fragments/Mayan/Mam/Pronouns.lean`). -/
inductive PhiDimension where
  | author
  | participant
  | singular
  deriving DecidableEq, Repr

/-- Dimensions referenced by Set A and Set B agreement Vocabulary Items —
    [±author] and [±singular] only ([scott-2023] Tables 4.7-4.8);
    agreement never copies [±participant]. -/
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

/-- The pronominal base is fully redundant under agreement — every
    dimension it realizes is copied, the configuration in which
    impoverishment bleeds base insertion ([scott-2023] §4.4). -/
theorem base_is_redundant : ∀ d ∈ baseDimensions, d.Copied := by decide

/-- The =i enclitic is not fully redundant: [±participant] is never copied
    by agreement — so the enclitic survives reduction. -/
theorem enclitic_survives : ¬ (∀ d ∈ encliticDimensions, d.Copied) := by decide

/-- Pronoun realization by argument position — the nominative alignment
    of reduction ([scott-2023] (3)/(8)). φ-agreed positions (A, S, and
    possessors) take the subject/possessor series, the unagreed object
    the independent series. The impoverishment rule
    `[±singular] → ∅ / [+author]^F` (ex. 84/94) targets [+author] under
    the agreed-with diacritic F, bleeding the bases *qin*/*qo*, so
    agreed-with first person surfaces as bare *=i* (∅ for 1PL.INCL) while
    everything else keeps its independent form. Realization selects among
    the shared `PersonalPronoun` entries, not a separate form
    classification. -/
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

/-! ### Mayan absolutive parameter -/

/-- HIGH-ABS: Set B (absolutive) markers sit pre-stem on Infl, right
    after the aspect marker — template ASP-**ABS**-ERG-ROOT-SUFFIX
    ([scott-2023] §2.5.1). -/
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

/-! ### Marker verification -/

/-- Set A 1SG marker: pre-consonantal `n-`, pre-vocalic `w-`. -/
theorem setA_1sg :
    (setAExponent .consonant).realize (.pn .first .Sing) = some [.pref "n"] ∧
    (setAExponent .vowel).realize (.pn .first .Sing) = some [.pref "w"] := ⟨rfl, rfl⟩

/-- Set A 3SG marker is `t-` (the default singular Set A — syncretic with 2SG). -/
theorem setA_3sg :
    (setAExponent .consonant).realize (.pn .third .Sing) = some [.pref "t"] := rfl

/-- Set B 1SG marker is *chin*. -/
theorem setB_1sg : setBExponent.realize (.pn .first .Sing) = some [.free "chin"] := rfl

/-- Set B 3SG marker is the default `tz'=`. -/
theorem setB_3sg : setBExponent.realize (.pn .third .Sing) = some defaultSetB := rfl

/-- A controller's φ-features index the agreement paradigm directly: the
    Set A table is keyed by canonical φ-cells, so a pronoun's
    `Word.agrCell` drives realization in one shared feature space
    ([corbett-1998]; [scott-2023] Ch. 2). The realizational account
    (impoverishment, Elsewhere; [scott-2023] Ch. 4) stays in the study. -/
theorem erg_1sg_from_phi :
    (setAExponent .consonant).realizeFor
      { form :="", cat := .PRON, features := { person := some .first, number := some .Sing }} =
      some [.pref "n"] := by
  rfl

end Mam
