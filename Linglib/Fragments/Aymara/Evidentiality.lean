import Linglib.Semantics.Evidential.Defs

/-!
# Aymara evidentiality

Aymara (Jaqi) has a three-choice system of Aikhenvald's type B1, an areal feature shared with
Quechua: personal knowledge, acquired visually, hearsay (knowledge through language) and
non-personal knowledge (inferred).

## References

* [aikhenvald-2004], §2.2
-/

namespace Aymara.Evidentiality

open Evidential

/-- Personal knowledge *-wa*, hearsay *-sa* and non-personal knowledge *-pacha*. -/
def evidentials : List Evidential :=
  [ { form := "-wa", exponent := .verbalAffix, covers := {.visual, .sensory} },
    { form := "-sa", exponent := .verbalAffix, covers := {.hearsay} },
    { form := "-pacha", exponent := .verbalAffix, covers := {.inference, .assumption} } ]

end Aymara.Evidentiality
