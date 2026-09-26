module

public import Linglib.Syntax.Case.Basic

/-!
# Slavic case inventories

This file defines the two case inventories of the modern Slavic languages that decline for case:
the six cases all of them share, nominative, accusative, genitive, dative, locative and
instrumental, and the seven of the languages that keep the vocative besides. The per-language
`Case` files take their inventories from here. The inventories are those of the chapters of
[comrie-corbett-1993]: Ukrainian (p. 956), Polish (p. 696), Cassubian (p. 768), Upper Sorbian
(p. 614), Czech (p. 465) and Serbo-Croat (p. 318) have seven cases, and Russian (p. 836),
Belorussian (p. 900), Slovak (p. 540), Lower Sorbian (p. 614) and Slovene (p. 399) six.

## References

* [comrie-corbett-1993]
* [shevelov-1993]
* [rothstein-1993]
* [stone-1993-cassubian]
* [stone-1993-sorbian]
* [short-1993-czech]
* [browne-1993]
* [timberlake-1993]
* [mayo-1993]
* [short-1993-slovak]
* [priestly-1993]
-/

@[expose] public section

namespace Slavic.Case

/-! ## Inventories -/

/-- The six cases the Slavic languages with case share are the nominative, accusative, genitive,
dative, locative and instrumental. -/
abbrev coreInventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .loc, .inst}

/-- The seven cases of the languages that keep the vocative are the six shared cases and the
vocative. -/
abbrev fullInventory : Finset Case :=
  insert .voc coreInventory

theorem coreInventory_subset_fullInventory : coreInventory ⊆ fullInventory :=
  Finset.subset_insert _ _

end Slavic.Case
