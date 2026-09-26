module

public import Linglib.Fragments.Slavic.Case

/-!
# Russian case inventory

This file defines the Russian cases, the six the Slavic languages share. [timberlake-1993] (p. 836)
takes Russian to have "six primary cases and two secondary cases (second genitive and second
locative), the secondary cases being available for a decreasing number of masculines", and finds
the historical vocative moribund. The secondary cases are cells of the paradigms of some nouns and
not cases of the inventory.

## References

* [timberlake-1993]
-/

@[expose] public section

namespace Russian.Case

/-- The Russian cases are the six primary cases, those the Slavic languages share. -/
abbrev inventory : Finset Case := Slavic.Case.coreInventory

end Russian.Case
