import Linglib.Typology.UniversalQuantifier

/-!
# Telugu universal-quantifier inventory

[haslinger-etal-2025-nllt]

Telugu (Dravidian) is a **2-form** language: a [+dist] form `prɨti` and [−dist]
forms `ăndărŭ` (and `ăn:ı̆`, `ănta:`). Data as reported by Ponangi (2012) and
surveyed in [haslinger-etal-2025-nllt] (Table 1).
-/

namespace Telugu

open Typology.UniversalQuantifier

/-- Telugu UQ inventory: 2-form. [+dist] `prɨti`, [−dist] `ăndărŭ` (a.o.). -/
def universalQuantifier : UQProfile :=
  { language := "Telugu"
  , family := "Dravidian"
  , systemType := .twoForm
  , distForm := "prɨti"
  , nonDistForm := "ăndărŭ"
  , source := "[haslinger-etal-2025-nllt] Table 1 (Ponangi 2012)" }

end Telugu
