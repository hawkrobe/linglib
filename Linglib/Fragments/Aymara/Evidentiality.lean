import Linglib.Semantics.Evidential.Defs

/-!
# Aymara Evidentiality
[aikhenvald-2004]

Three-or-more system: direct, reportative, non-personal/inferential. Andean
areal feature shared with Quechua. WALS Ch 77 has no entry; fallback fires.
-/

namespace Aymara.Evidentiality

/-! ### Typed evidential inventory

Aymara's 3-way Andean system: direct `-wa`, reportative `-sa`,
inferential `-pacha`. Obligatory verbal affixes. -/

open Semantics.Evidential

def evidentials : List Evidential :=
  [ { form := "-wa", exponent := .verbalAffix, covers := {.visual, .sensory} },
    { form := "-sa", exponent := .verbalAffix, covers := {.hearsay} },
    { form := "-pacha", exponent := .verbalAffix, covers := {.inference, .assumption} } ]

end Aymara.Evidentiality
