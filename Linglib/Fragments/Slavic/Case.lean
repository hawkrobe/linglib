import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy

/-!
# Shared Slavic Case Inventories
@cite{comrie-corbett-1993} @cite{blake-1994}

The 6-case core (NOM/ACC/GEN/DAT/LOC/INST) attested across all modern
Slavic case-bearing languages, plus a 7-case extension (with VOC) for
Ukrainian/Polish/Czech/Serbo-Croat. Factored from per-language
Fragments to remove byte-identical duplication.

Per-language sources (chapters of @cite{comrie-corbett-1993}):
@cite{shevelov-1993} (p. 956), @cite{rothstein-1993} (p. 696),
@cite{short-1993-czech} (p. 466), @cite{browne-1993} (p. 319),
@cite{timberlake-1993} (p. 836), @cite{priestly-1993} (p. 399).

Caha-containment lemmas live in `Studies/Caha2009.lean`
(paper-anchored, keeps this substrate file Theory-import-free).
-/

namespace Fragments.Slavic.Case

/-! ## Inventories -/

/-- The 6-case core: NOM, ACC, GEN, DAT, LOC, INST. -/
abbrev coreInventory : Finset Core.Case :=
  {.nom, .acc, .gen, .dat, .loc, .inst}

/-- The 6-case core extended with vocative; the inventory of
    Ukrainian, Polish, Czech, and Serbo-Croat. Does **not** satisfy
    `Core.Case.IsValidInventory` — see `sevenCaseInventory_not_isValid`. -/
abbrev sevenCaseInventory : Finset Core.Case :=
  {.nom, .acc, .gen, .dat, .loc, .inst, .voc}

/-! ## API -/

theorem coreInventory_card : coreInventory.card = 6 := by decide

theorem sevenCaseInventory_card : sevenCaseInventory.card = 7 := by decide

/-! ## Blake (typological hierarchy) -/

theorem coreInventory_isValid :
    Core.Case.IsValidInventory coreInventory := by decide

/-- VOC at Blake-rank 0 leaves a gap at rank 1 (COM/spatial), breaking
    contiguity. -/
theorem sevenCaseInventory_not_isValid :
    ¬ Core.Case.IsValidInventory sevenCaseInventory := by decide

end Fragments.Slavic.Case
