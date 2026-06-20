import Linglib.Typology.UniversalQuantifier

/-!
# Basque universal-quantifier inventory

[haslinger-etal-2025-nllt]

Basque (isolate) is a **2-form** language: a [+dist] form `bakoitz` and [−dist]
forms `guzti`, `den`, `oro` ('all'). Data as reported by Etxeberria (2012) and
surveyed in [haslinger-etal-2025-nllt] (Table 1).
-/

namespace Basque

open Typology.UniversalQuantifier

/-- Basque UQ inventory: 2-form. [+dist] `bakoitz`, [−dist] `guzti`/`den`/`oro`. -/
def universalQuantifier : UQProfile :=
  { language := "Basque"
  , family := "isolate"
  , systemType := .twoForm
  , distForm := "bakoitz"
  , nonDistForm := "guzti, den, oro"
  , source := "[haslinger-etal-2025-nllt] Table 1 (Etxeberria 2012)" }

end Basque
