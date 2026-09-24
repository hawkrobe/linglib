module

public import Linglib.Syntax.Case.Basic

/-!
# Shared Slavic Case Inventories
[comrie-corbett-1993] [blake-1994]

The 6-case core (NOM/ACC/GEN/DAT/LOC/INST) attested across all modern
Slavic case-bearing languages, plus a 7-case extension (with VOC) for
Ukrainian/Polish/Czech/Serbo-Croat. Factored from per-language
Fragments to remove byte-identical duplication.

Per-language sources (chapters of [comrie-corbett-1993]):
[shevelov-1993] (p. 956), [rothstein-1993] (p. 696),
[short-1993-czech] (p. 466), [browne-1993] (p. 319),
[timberlake-1993] (p. 836), [priestly-1993] (p. 399).

-/

@[expose] public section

namespace Slavic.Case

/-! ## Inventories -/

/-- The 6-case core: NOM, ACC, GEN, DAT, LOC, INST. -/
abbrev coreInventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .loc, .inst}

/-- The 6-case core extended with vocative; the inventory of
    Ukrainian, Polish, Czech, and Serbo-Croat. -/
abbrev fullInventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .loc, .inst, .voc}

end Slavic.Case
