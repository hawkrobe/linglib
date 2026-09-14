import Linglib.Semantics.Evidential.Defs

/-!
# Quechua (Cuzco) evidentiality

Cuzco Quechua has a three-choice system of Aikhenvald's type B1, the canonical Andean system:
direct *-mi*, reportative *-si* and conjectural *-chá*, second-position enclitics on finite
clauses.

## References

* [aikhenvald-2004], §2.2
-/

namespace Quechua.Evidentiality

open Evidential

/-- Direct *-mi*, reportative *-si* and conjectural *-chá*. -/
def evidentials : List Evidential :=
  [ { form := "-mi", exponent := .clitic2P, covers := {.visual, .sensory} },
    { form := "-si", exponent := .clitic2P, covers := {.hearsay} },
    { form := "-chá", exponent := .clitic2P, covers := {.inference, .assumption} } ]

end Quechua.Evidentiality
