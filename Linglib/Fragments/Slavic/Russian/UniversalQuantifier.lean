import Linglib.Typology.UniversalQuantifier

/-!
# Russian universal-quantifier inventory

[haslinger-etal-2025-nllt]

Russian (Slavic) is a **2-form** language: a [+dist] form `každyj` ('every/each')
and a [−dist] form `vse` ('all'). With a singular complement the [−dist] form
yields only a 'whole' meaning. Data as reported by Paperno (2012) and surveyed in
[haslinger-etal-2025-nllt] (Table 1).
-/

namespace Russian

open Typology.UniversalQuantifier

/-- Russian UQ inventory: 2-form. [+dist] `každyj`, [−dist] `vse`. -/
def universalQuantifier : UQProfile :=
  { language := "Russian"
  , family := "Indo-European (Slavic)"
  , systemType := .twoForm
  , distForm := "každyj"
  , nonDistForm := "vse"
  , source := "[haslinger-etal-2025-nllt] Table 1 (Paperno 2012)" }

end Russian
