import Linglib.Typology.UniversalQuantifier

/-!
# Hausa universal-quantifier inventory

[haslinger-etal-2025-nllt]

Hausa (West Chadic) is a **2-form** language: a [+dist] form `koowànè` and a
[−dist] form `duk` ('all'). Data as reported by Zimmermann (2008) and surveyed
in [haslinger-etal-2025-nllt] (Table 1).
-/

namespace Hausa

open Typology.UniversalQuantifier

/-- Hausa UQ inventory: 2-form. [+dist] `koowànè`, [−dist] `duk`. -/
def universalQuantifier : UQProfile :=
  { language := "Hausa"
  , family := "Afro-Asiatic (West Chadic)"
  , systemType := .twoForm
  , distForm := "koowànè"
  , nonDistForm := "duk"
  , source := "[haslinger-etal-2025-nllt] Table 1 (Zimmermann 2008)" }

end Hausa
