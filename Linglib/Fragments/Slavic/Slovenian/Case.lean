module

public import Linglib.Fragments.Slavic.Case

/-!
# Slovene case inventory

This file defines the Slovene cases, the six the Slavic languages share: "There are six cases:
nominative, accusative, genitive, dative, instrumental and locative. There is no separate vocative
case" ([priestly-1993], p. 399). The locative and the instrumental occur only in prepositional
phrases. The directory is named for Slovenian; Priestly's chapter is "Slovene".

## References

* [priestly-1993]
-/

@[expose] public section

namespace Slovenian.Case

/-- The Slovene cases are the six the Slavic languages share. -/
abbrev inventory : Finset Case := Slavic.Case.coreInventory

end Slovenian.Case
