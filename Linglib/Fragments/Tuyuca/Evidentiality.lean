import Linglib.Semantics.Evidential.Defs

/-!
# Tuyuca Evidentiality
[aikhenvald-2004] [barnes-1984] [de-haan-2013]

Five-term system: visual, nonvisual, apparent (inferential), secondhand
(reported), assumed. Obligatory verbal suffixes. [barnes-1984] is the
classic description. Vaupés multilingual area.

WALS [de-haan-2013] F77A codes Tuyuca as `directAndIndirect`, lumping
the 5-term system into the canonical 2-way bucket; [aikhenvald-2004]
classes it as the five-choice type D1 (`Studies/Aikhenvald2004.lean`).
-/

namespace Tuyuca.Evidentiality

/-! ### Typed evidential inventory

Tuyuca's 5-term D1 system per [aikhenvald-2004] Ch 2 §2.4 and
[barnes-1984]. -/

open Evidential

/-- Tuyuca evidential inventory in the new typed form. Five entries:
    two `Direct` (visual/non-visual sensory), two `Inferential`
    (from-result/from-assumption), one `Reportative` (unidentified). -/
def evidentials : List Evidential :=
  [ { form := "-wi", exponent := .verbalAffix, covers := {.visual} },
    { form := "-ti", exponent := .verbalAffix, covers := {.sensory} },
    { form := "-yi", exponent := .verbalAffix, covers := {.inference} },
    { form := "-yigi", exponent := .verbalAffix, covers := {.hearsay} },
    { form := "-hiyi", exponent := .verbalAffix, covers := {.assumption} } ]

end Tuyuca.Evidentiality
