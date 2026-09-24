module

public import Linglib.Semantics.Evidential.Defs

/-!
# Quechua (Cuzco) evidentiality

Cuzco Quechua has a three-choice system of Aikhenvald's type B1, the canonical Andean system:
direct *-mi*, reportative *-si* and conjectural *-chá*, second-position enclitics on finite
clauses.

## References

* [aikhenvald-2004], §2.2
-/

@[expose] public section

namespace Quechua.Evidentiality

open Evidential

/-- Direct *-mi*, reportative *-si* and conjectural *-chá*. -/
def evidentials : List Evidential :=
  [ { form := "-mi", exponent := .clitic, covers := {.visual, .sensory} },
    { form := "-si", exponent := .clitic, covers := {.hearsay} },
    { form := "-chá", exponent := .clitic, covers := {.inference, .assumption} } ]

end Quechua.Evidentiality
