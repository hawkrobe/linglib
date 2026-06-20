import Linglib.Typology.UniversalQuantifier

/-!
# Imbabura Quichua universal-quantifier inventory

[haslinger-etal-2025-nllt]

Imbabura Quichua (Quechuan) is a **2-form** language: a [+dist] form `kada` and
a [−dist] form `tukuy(-lla)`. Data as reported by Barchas-Lichtenstein et al.
(2017) and surveyed in [haslinger-etal-2025-nllt] (Table 1).
-/

namespace Quechua.Imbabura

open Typology.UniversalQuantifier

/-- Imbabura Quichua UQ inventory: 2-form. [+dist] `kada`, [−dist]
`tukuy(-lla)`. -/
def universalQuantifier : UQProfile :=
  { language := "Imbabura Quichua"
  , family := "Quechuan"
  , systemType := .twoForm
  , distForm := "kada"
  , nonDistForm := "tukuy(-lla)"
  , source := "[haslinger-etal-2025-nllt] Table 1 (Barchas-Lichtenstein et al. 2017)" }

end Quechua.Imbabura
