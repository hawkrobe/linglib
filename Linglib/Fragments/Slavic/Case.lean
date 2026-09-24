module

public import Linglib.Syntax.Case.Basic

/-!
# Slavic case inventories

This file defines the two case inventories of the modern Slavic languages that decline for case:
the six cases all of them share, nominative, accusative, genitive, dative, locative and
instrumental, and the seven of Ukrainian, Polish, Czech and Serbo-Croat, which keep the vocative
besides. The per-language `Case` files take their inventories from here. The inventories are those
of the chapters of Comrie and Corbett's handbook: Shevelov on Ukrainian (p. 956), Rothstein on
Polish (p. 696), Short on Czech (p. 465), Browne on Serbo-Croat (p. 319), Timberlake on Russian
(p. 836) and Priestly on Slovene (p. 399).

## References

* [comrie-corbett-1993]
* [shevelov-1993]
* [rothstein-1993]
* [short-1993-czech]
* [browne-1993]
* [timberlake-1993]
* [priestly-1993]
* [blake-1994]
-/

@[expose] public section

namespace Slavic.Case

/-! ## Inventories -/

/-- The six cases the Slavic languages with case share are the nominative, accusative, genitive,
dative, locative and instrumental. -/
abbrev coreInventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .loc, .inst}

/-- The seven cases of Ukrainian, Polish, Czech and Serbo-Croat are the six shared cases and the
vocative. -/
abbrev fullInventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .loc, .inst, .voc}

end Slavic.Case
