import Linglib.Semantics.Evidential.Defs

/-!
# Tariana Evidentiality
[aikhenvald-2004] [de-haan-2013]

Five-term system in the Vaupés multilingual area: visual, nonvisual,
inferred, assumed, reported. WALS [de-haan-2013] F77A codes Tariana as
`directAndIndirect`; [aikhenvald-2004] classes it as the five-choice type
D1 (`Studies/Aikhenvald2004.lean`).
-/

namespace Tariana.Evidentiality

/-! ### Typed evidential inventory

Tariana's classic D1 5-term Vaupés system per [aikhenvald-2004]:
visual, non-visual sensory, inferred (from result), assumed (from
reasoning), reported. -/

open Semantics.Evidential

def evidentials : List Evidential :=
  [ { form := "-ka", exponent := .verbalAffix, covers := {.visual} },
    { form := "-mha", exponent := .verbalAffix, covers := {.sensory} },
    { form := "-nihka", exponent := .verbalAffix, covers := {.inference} },
    { form := "-sika", exponent := .verbalAffix, covers := {.assumption} },
    { form := "-pidaka", exponent := .verbalAffix, covers := {.hearsay} } ]

end Tariana.Evidentiality
