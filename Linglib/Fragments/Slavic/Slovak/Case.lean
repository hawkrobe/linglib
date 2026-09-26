module

public import Linglib.Fragments.Slavic.Case

/-!
# Slovak case inventory

This file defines the Slovak cases, the six the Slavic languages share: "The case system has shrunk
from seven members to six, the vocative being replaced by the nominative. Some vocative forms
survive, but are not considered part of their respective paradigms" ([short-1993-slovak], p. 540).

## References

* [short-1993-slovak]
-/

@[expose] public section

namespace Slovak.Case

/-- The Slovak cases are the six the Slavic languages share. -/
abbrev inventory : Finset Case := Slavic.Case.coreInventory

end Slovak.Case
