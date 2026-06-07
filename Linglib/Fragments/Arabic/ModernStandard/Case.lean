import Linglib.Features.Case.Basic
import Linglib.Typology.Case

/-!
# Modern Standard Arabic Case Inventory
[ryding-2005]

Three-case nominal inflection (Ryding §5, p. 165): nominative *raf ʿ*
(`-u`), genitive *jarr* (`-i`), accusative *naSb* (`-a`). Case marking
attaches as a word-final short-vowel suffix on triptote nouns, with
nunation (final `-n`) on indefinite nouns (Ryding §4.2.1, pp. 162–163).

The diptote declension (Ryding §4.2.1.4 p. 162; §5.4.2 p. 164) and the
sound-feminine-plural pattern (`kalimaat-un` / `kalimaat-in` /
`kalimaat-in` — genitive and accusative syncretized) are documented in
the typology-feature section below as syncretism in selected NP types.
The dual takes its own pair of suffixes: `-aani` (nom) / `-ayni` (gen
& acc; Ryding p. 164). The sound-masculine-plural pattern parallels
this with `-uuna` (nom) / `-iina` (gen & acc).

## Variety scope

The MSA case system is largely absent from spoken Arabics (Ryding
§5 p. 166: "colloquial forms of Arabic do not have case marking").
This file is therefore MSA-specific; if an Egyptian-Arabic Case
fragment is added later it should expose `caseInventory := ∅`.
-/

namespace Arabic.ModernStandard.Case

/-! ## Inventory -/

/-- The three-case core: nominative, accusative, genitive (Ryding §5 p. 166). -/
abbrev caseInventory : Finset Case := {.nom, .acc, .gen}

theorem caseInventory_card : caseInventory.card = 3 := by decide

/-! ## WALS-typology summary (Chs 49–52)

These four named values bundle Ryding's §5 description into the
typological substrate's per-chapter enums. Each is purely descriptive
of the surface system; no theoretical commitment to abstract case
or feature-checking. -/

/-- WALS Ch 49 (number of cases): 3 cases falls into the `threeFour` bin. -/
def caseCount : Typology.Case.CaseCount := .threeFour

/-- WALS Ch 50 (asymmetrical case marking): the sound-feminine plural
    (`kalimaat-in` for both gen and acc), the dual (`-ayni` for both gen
    and acc), the sound-masculine plural (`-iina` for both gen and acc),
    and the diptote declension all collapse case distinctions on selected
    NP types. Per Ryding §4.2.1 pp. 162–163 + §5.4. -/
def asymmetricalMarking : Typology.Case.AsymmetricalCaseMarking :=
  .syncretismInRelevantNpTypes

/-- WALS Ch 51 (position of case affixes): word-final short-vowel
    suffixes (Ryding §5 p. 166). -/
def caseAffixPosition : Typology.Case.CaseAffixPosition := .suffixesOnly

/-- WALS Ch 52 (comitative–instrumental): MSA distinguishes them —
    *maʿa* '(together) with' (comitative) vs `bi-` 'by means of'
    (instrumental). Different markers, hence `differentiation`. -/
def comitativeInstrumental : Typology.Case.ComitativeInstrumental :=
  .differentiation

end Arabic.ModernStandard.Case
