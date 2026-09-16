import Linglib.Syntax.Case.Basic
import Linglib.Phonology.Segmental.Defs
import Linglib.Fragments.Mayan.Mam.Pronouns
import Linglib.Fragments.Mayan.Params
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Syntax.Clause.ArgumentRole
import Linglib.Syntax.Person.Basic

/-!
# Mam Agreement Fragment

Agreement morphology of San Juan Atitán Mam (SJA Mam, Mayan), following [scott-2023]. Two
paradigms cross-reference arguments on the verb: Set A prefixes on Voice for the transitive
subject (Table 2.8, `Mam.setAExponent`), and Set B markers on Infl for the intransitive subject
(Table 3.5, `Mam.setBExponent`). Transitive objects are cross-referenced by neither set: they
co-occur with the default Set B marker *tz'=* (`Mam.defaultSetB`) and are full pronouns, though
some speakers accept agreeing Set B for objects as a more formal variant (ch. 3, ex. 156). The
underlying case system is tripartite, ERG from Voice, ACC from Voice and ABS from Infl, visible
only through agreement (`Mam.caseInventory`); Set B sits pre-stem on Infl, the high-absolutive
placement (`Mam.absPosition`).

## Implementation notes

This fragment records SJA Mam specifically. Other Mam dialects, notably Ixtahuacán Mam
(England 1983b, used by [zavala-maldonado-2017] §4–5), are characterized as ergative with a
neutral pattern in aspectless dependent clauses; per [scott-2023] §1.2.4 and Table 1.2, Mam
dialects vary substantially. The tripartite case function is `Alignment.tripartite.assignCase`
via `Mayan.caseMam`. Person-number cells are the canonical φ-cells `Agreement.Bundle`; the
pronoun lexicon and its feature values live in `Fragments/Mayan/Mam/Pronouns.lean`, and the
derivation of the paradigms from a Vocabulary in `Studies/Scott2023.lean`.
-/

namespace Mam

open Mayan (MarkerLinearity ExponentTable)
open Agreement

/-! ### Agreement marker paradigms -/

/-- Set A (ERG) markers cross-referencing the transitive agent
    ([scott-2023] Table 2.8) by following-segment environment; t- is
    syncretic for 2/3SG, ky- for 2/3PL. Scott: 1SG is the sole Set A
    allomorphy — pre-consonantal `n-`, pre-vocalic `w-` (exx. (28)-(29));
    the other markers do not alternate. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.pn .first .singular, [.pref "n"]), (.pn .second .singular, [.pref "t"]),
     (.pn .third .singular, [.pref "t"]), (.pn .first .plural, [.pref "q"]),
     (.pn .second .plural, [.pref "ky"]), (.pn .third .plural, [.pref "ky"])]
  | .vowel =>
    [(.pn .first .singular, [.pref "w"]), (.pn .second .singular, [.pref "t"]),
     (.pn .third .singular, [.pref "t"]), (.pn .first .plural, [.pref "q"]),
     (.pn .second .plural, [.pref "ky"]), (.pn .third .plural, [.pref "ky"])]

/-- Set B (ABS) markers ([scott-2023] Table 3.5). The 2/3SG form tz'= is
    the Elsewhere default: it realizes both real 2/3SG intransitive-S
    agreement and default Set B in transitives when Infl's probe is
    blocked by VoiceP. Per Scott's DM analysis 2SG and 3SG are not
    specific Vocabulary Items but surface via Elsewhere fallback (see
    `setBSpecificCells`). -/
def setBExponent : ExponentTable :=
  [(.pn .first .singular, [.free "chin"]), (.pn .second .singular, [.procl "tz'"]),
   (.pn .third .singular, [.procl "tz'"]), (.pn .first .plural, [.free "qo"]),
   (.pn .second .plural, [.free "chi"]), (.pn .third .plural, [.free "chi"])]

/-- The four Set B cells with specific Vocabulary Items ([scott-2023]);
    2SG and 3SG fall through to the Elsewhere entry. -/
def setBSpecificCells : List Bundle :=
  [.pn .first .singular, .pn .first .plural, .pn .second .plural, .pn .third .plural]

/-- The Elsewhere Set B marker, surfacing in transitives when Infl's
    probe is blocked and for 2/3SG intransitive S. -/
def defaultSetB : List Morphology.Morph := [.procl "tz'"]

/-! ### Case -/

-- The per-position case facts are the tripartite-alignment facts
-- (`Alignment.tripartite`) — SJA Mam's case function is
-- `Alignment.tripartite.assignCase` by definition, so each theorem below
-- is a re-export of the substrate lemma.

/-- Agent gets ERG (inherent, from Voice). -/
theorem A_case : (Mayan.caseMam .Perf) .A = .erg := Alignment.tripartite.assignCase_A

/-- Patient gets ACC (structural, from Voice). -/
theorem P_case : (Mayan.caseMam .Perf) .P = .acc := Alignment.tripartite.assignCase_P

/-- Intransitive S gets ABS (structural, from Infl). -/
theorem S_case : (Mayan.caseMam .Perf) .S = .abs := Alignment.tripartite.assignCase_S

/-- Three distinct underlying cases (morphologically tripartite),
    inherited from `Alignment.tripartite_distinguishes_all`. -/
theorem tripartite_alignment :
    (Mayan.caseMam .Perf) .A ≠ (Mayan.caseMam .Perf) .P ∧
    (Mayan.caseMam .Perf) .A ≠ (Mayan.caseMam .Perf) .S ∧
    (Mayan.caseMam .Perf) .P ≠ (Mayan.caseMam .Perf) .S :=
  Alignment.tripartite_distinguishes_all

/-! ### Case inventory ([blake-1994]) -/

/-- The case inventory realized by the core positions: {ERG, ACC, ABS}. -/
def caseInventory : Finset Case := (ArgumentRole.core.map (Mayan.caseMam .Perf)).toFinset

/-- The inventory covers all argument positions. -/
theorem inventory_covers_positions :
    ∀ p ∈ ArgumentRole.core, (Mayan.caseMam .Perf) p ∈ caseInventory := by decide

-- Mam's {ERG, ACC, ABS} inventory is valid per Blake's case hierarchy
-- (all are core cases at rank 6, trivially no gaps).
example : Case.IsValidInventory caseInventory := by decide

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
    (setAExponent .consonant).realize (.pn .first .singular) = some [.pref "n"] ∧
    (setAExponent .vowel).realize (.pn .first .singular) = some [.pref "w"] := ⟨rfl, rfl⟩

/-- Set A 3SG marker is `t-` (the default singular Set A — syncretic with 2SG). -/
theorem setA_3sg :
    (setAExponent .consonant).realize (.pn .third .singular) = some [.pref "t"] := rfl

/-- Set B 1SG marker is *chin*. -/
theorem setB_1sg : setBExponent.realize (.pn .first .singular) = some [.free "chin"] := rfl

/-- Set B 3SG marker is the default `tz'=`. -/
theorem setB_3sg : setBExponent.realize (.pn .third .singular) = some defaultSetB := rfl

/-- A controller's φ-features index the agreement paradigm directly: the
    Set A table is keyed by canonical φ-cells, so a pronoun's
    `Word.phi` drives realization in one shared feature space
    ([corbett-1998]; [scott-2023] Ch. 2). The realizational account
    (impoverishment, Elsewhere; [scott-2023] Ch. 4) stays in the study. -/
theorem erg_1sg_from_phi :
    (setAExponent .consonant).realizeFor
      { form :="", cat := .PRON,
        features := Morphology.Features.of (person := some .first) (number := some .singular) } =
      some [.pref "n"] := by
  rfl

end Mam
