module

public import Linglib.Fragments.Slavic.Case

/-!
# Ukrainian case inventory

This file defines the Ukrainian cases, the seven of the Slavic inventory: "Ukrainian preserves the
original set of cases: nominative, accusative, genitive, dative, instrumental and locative. In
addition, the vocative is preserved even though the vocative singular in colloquial speech is
occasionally replaced by the nominative and in the plural the vocative has no forms of its own,
except in the word панове/panove 'gentlemen'" ([shevelov-1993], p. 956).

## References

* [shevelov-1993]
-/

@[expose] public section

namespace Ukrainian.Case

/-- The Ukrainian cases are the seven of the Slavic inventory. -/
abbrev inventory : Finset Case := Slavic.Case.fullInventory

end Ukrainian.Case
