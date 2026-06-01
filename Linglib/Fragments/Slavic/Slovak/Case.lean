import Linglib.Fragments.Slavic.Case

/-!
# Slovak Case Inventory
@cite{short-1993-slovak} @cite{blake-1994}

Per @cite{short-1993-slovak} (p. 541): "The case system has shrunk
from seven members to six, the vocative being replaced by the
nominative. Some vocative forms survive, but are not considered part
of their respective paradigms. They occur in addressing kin, close
friends, the deity and high dignitaries and are essentially formulaic,
whether familiar, jocular or formal."

Slovak thus patterns with Russian, Slovene, and Belarusian as 6-case
without productive VOC. `caseInventory` aliases the shared
`Slavic.Case.coreInventory`.
-/

namespace Slovak.Case

abbrev caseInventory : Finset Features.Case := Slavic.Case.coreInventory

end Slovak.Case
