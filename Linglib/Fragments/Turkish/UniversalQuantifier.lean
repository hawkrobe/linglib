import Linglib.Typology.UniversalQuantifier

/-!
# Turkish universal-quantifier inventory

[haslinger-etal-2025-nllt]

Turkish (Turkic) is a **2-form** language: a [+dist] form `her` and [−dist]
forms `bütün`, `hepsi` ('all'). Data as reported by Özyıldız (2017) and surveyed
in [haslinger-etal-2025-nllt] (Table 1).
-/

namespace Turkish

open Typology.UniversalQuantifier

/-- Turkish UQ inventory: 2-form. [+dist] `her`, [−dist] `bütün`/`hepsi`. -/
def universalQuantifier : UQProfile :=
  { language := "Turkish"
  , family := "Turkic"
  , systemType := .twoForm
  , distForm := "her"
  , nonDistForm := "bütün, hepsi"
  , source := "[haslinger-etal-2025-nllt] Table 1 (Özyıldız 2017)" }

end Turkish
