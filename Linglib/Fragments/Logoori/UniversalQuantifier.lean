import Linglib.Typology.UniversalQuantifier

/-!
# Logoori universal-quantifier inventory

[haslinger-etal-2025-nllt]

Logoori (Bantu) is a **2-form** language: a [+dist] form `vuri` and a [−dist]
form `-oosi` ('all'). With a plural complement the [+dist] `vuri` permits only a
'subgroup' (distribution-over-subgroups) reading, noted as a refinement point in
[haslinger-etal-2025-nllt]. Data as reported by Landman (2016).
-/

namespace Logoori

open Typology.UniversalQuantifier

/-- Logoori UQ inventory: 2-form. [+dist] `vuri`, [−dist] `-oosi`. -/
def universalQuantifier : UQProfile :=
  { language := "Logoori"
  , family := "Niger-Congo (Bantu)"
  , systemType := .twoForm
  , distForm := "vuri"
  , nonDistForm := "-oosi"
  , source := "[haslinger-etal-2025-nllt] Table 1 (Landman 2016)" }

end Logoori
