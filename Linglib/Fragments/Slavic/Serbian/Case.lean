module

public import Linglib.Fragments.Slavic.Case

/-!
# Serbo-Croat case inventory

This file defines the Serbo-Croat cases, the seven of the Slavic inventory: "There are seven cases:
nominative, vocative, accusative, genitive, dative, instrumental, locative. Dative and locative
have merged; only certain inanimate monosyllabic nouns distinguish them accentually in the
singular" ([browne-1993], p. 318). The directory is named for Serbian; Browne's chapter describes
the Serbo-Croat standard.

## References

* [browne-1993]
-/

@[expose] public section

namespace Serbian.Case

/-- The Serbo-Croat cases are the seven of the Slavic inventory. -/
abbrev inventory : Finset Case := Slavic.Case.fullInventory

end Serbian.Case
