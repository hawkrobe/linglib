module

public import Linglib.Fragments.Slavic.Case

/-!
# Sorbian case inventories

This file defines the cases of Upper and of Lower Sorbian: "Upper Sorbian has seven cases
(nominative, vocative, accusative, genitive, dative, instrumental and locative). Lower Sorbian,
having lost the vocative, has only six cases" ([stone-1993-sorbian], p. 614). Even in Upper
Sorbian only masculine nouns have a separate vocative form, and only in the singular, save *mać*
'mother', vocative *maći*. In both languages the instrumental has lost its prepositionless
function.

## References

* [stone-1993-sorbian]
-/

@[expose] public section

namespace Sorbian.Upper.Case

/-- The Upper Sorbian cases are the seven of the Slavic inventory. -/
abbrev inventory : Finset Case := Slavic.Case.fullInventory

end Sorbian.Upper.Case

namespace Sorbian.Lower.Case

/-- The Lower Sorbian cases are the six the Slavic languages share. -/
abbrev inventory : Finset Case := Slavic.Case.coreInventory

end Sorbian.Lower.Case
