import Linglib.Features.Case.Basic

/-!
# Modern Standard Arabic Case Inventory
[ryding-2005]

Three-case nominal inflection (Ryding §5, p. 165): nominative *raf ʿ*
(`-u`), genitive *jarr* (`-i`), accusative *naSb* (`-a`). Case marking
attaches as a word-final short-vowel suffix on triptote nouns, with
nunation (final `-n`) on indefinite nouns (Ryding §4.2.1, pp. 162–163).

The diptote declension (Ryding §4.2.1.4 p. 162; §5.4.2 p. 164) and the
sound-feminine-plural pattern (`kalimaat-un` / `kalimaat-in` /
`kalimaat-in` — genitive and accusative syncretized) collapse case
distinctions on selected NP types.
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

end Arabic.ModernStandard.Case
