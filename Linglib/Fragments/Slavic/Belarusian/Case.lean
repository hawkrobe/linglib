module

public import Linglib.Fragments.Slavic.Case

/-!
# Belarusian case inventory

This file defines the Belarusian cases, the six the Slavic languages share. "Modern standard
Belorussian has two numbers, six cases and three genders", and "The vocative case can no longer be
regarded as a living category in the standard language, which has only the remnants божа/boža from
бог/boh 'god' (as an exclamation) and браце/brace from брат/brat 'brother', дружа/druža from
друг/druh 'friend' and сынку/synku (with stress shift) from сынок/synók 'son' (as modes of
address)" ([mayo-1993], p. 900).

## References

* [mayo-1993]
-/

@[expose] public section

namespace Belarusian.Case

/-- The Belarusian cases are the six the Slavic languages share. -/
abbrev inventory : Finset Case := Slavic.Case.coreInventory

end Belarusian.Case
