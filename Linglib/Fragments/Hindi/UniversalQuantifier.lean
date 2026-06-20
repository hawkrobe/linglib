import Linglib.Typology.UniversalQuantifier

/-!
# Hindi universal-quantifier inventory

[haslinger-etal-2025-nllt]

Hindi (Indo-Aryan) is a **2-form** language: a [+dist] form `praty-ek` (lit.
'each-one') and a [−dist] form `saar-` ('whole'/'all'). Data as reported by
Mahajan (2017) and surveyed in [haslinger-etal-2025-nllt] (Table 1).
-/

namespace Hindi

open Typology.UniversalQuantifier

/-- Hindi UQ inventory: 2-form. [+dist] `praty-ek`, [−dist] `saar-`. -/
def universalQuantifier : UQProfile :=
  { language := "Hindi"
  , family := "Indo-European (Indic)"
  , systemType := .twoForm
  , distForm := "praty-ek"
  , nonDistForm := "saar-"
  , source := "[haslinger-etal-2025-nllt] Table 1 (Mahajan 2017)" }

end Hindi
