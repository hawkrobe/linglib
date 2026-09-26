module

public import Linglib.Fragments.Slavic.Case

/-!
# Cassubian case inventory

This file defines the Cassubian cases, the seven of the Slavic inventory: "The seven cases are the
same as in Polish, but the tendency for the nominative to replace the vocative is greater than in
Polish. The locative never occurs without a preposition, and there is a strong tendency for the
instrumental to acquire the preposition z(s)/ze(se) 'with', when used with its basic function as
an expression of instrument (but not in the complement of the copula)" ([stone-1993-cassubian],
p. 768).

## References

* [stone-1993-cassubian]
-/

@[expose] public section

namespace Cassubian.Case

/-- The Cassubian cases are the seven of the Slavic inventory. -/
abbrev inventory : Finset Case := Slavic.Case.fullInventory

end Cassubian.Case
