import Linglib.Semantics.Evidential.Defs

/-!
# Tibetan (Lhasa) Evidentiality
[aikhenvald-2004]

Two-choice direct vs indirect via copula/auxiliary contrast. *red*/*yod*
(personal knowledge) vs *yin*/*'dug* (indirect or new information).
Egophoric system. WALS Ch 77 has no entry; the fallback fires.
-/

namespace Tibetan.Evidentiality

/-! ### Typed evidential inventory

Lhasa Tibetan's 2-way direct/indirect contrast realized in the copula
and auxiliary system: `red`/`yod` (direct, personal knowledge) vs
`'dug`/`yin` (indirect, new information). Grammaticalized lexical
opposition. -/

open Semantics.Evidential

def evidentials : List Evidential :=
  [ { form := "red", exponent := .lexicalFrame, covers := {.visual, .sensory} },
    { form := "yod", exponent := .lexicalFrame, covers := {.visual, .sensory} },
    { form := "'dug", exponent := .lexicalFrame, covers := {.inference, .assumption} },
    { form := "yin", exponent := .lexicalFrame, covers := {.inference, .assumption} } ]

end Tibetan.Evidentiality
