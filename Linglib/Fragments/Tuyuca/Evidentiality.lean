module

public import Linglib.Semantics.Evidential.Defs

/-!
# Tuyuca evidentiality

Tuyuca (East Tucanoan, Vaupés) has a five-choice system of Aikhenvald's type D1, the most
frequently cited example of its kind: visual *-wi*, non-visual sensory *-ti*, apparent
(inferred) *-yi*, secondhand (reported) *-yigi* and assumed *-hiyi*, obligatory verbal
suffixes; [barnes-1984] is the classic description. WALS codes the language as having direct
and indirect evidentials.

## References

* [aikhenvald-2004], §2.4
* [barnes-1984]
* [de-haan-2013]
-/

@[expose] public section

namespace Tuyuca.Evidentiality

open Evidential

/-- Visual *-wi*, non-visual *-ti*, apparent *-yi*, secondhand *-yigi* and assumed *-hiyi*. -/
def evidentials : List Evidential :=
  [ { form := "-wi", exponent := .verbalAffix, covers := {.visual} },
    { form := "-ti", exponent := .verbalAffix, covers := {.sensory} },
    { form := "-yi", exponent := .verbalAffix, covers := {.inference} },
    { form := "-yigi", exponent := .verbalAffix, covers := {.hearsay} },
    { form := "-hiyi", exponent := .verbalAffix, covers := {.assumption} } ]

end Tuyuca.Evidentiality
