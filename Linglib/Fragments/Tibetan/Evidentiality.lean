import Linglib.Semantics.Evidential.Defs

/-!
# Tibetan (Lhasa) Evidentiality
@cite{aikhenvald-2004}

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

def evidentials : List Entry :=
  [ .direct      { form := "red", exponent := .lexicalFrame },
    .direct      { form := "yod", exponent := .lexicalFrame },
    .inferential { form := "'dug", exponent := .lexicalFrame },
    .inferential { form := "yin", exponent := .lexicalFrame } ]

example : evidentials.length = 4 := by decide
example : (evidentials.filter Entry.IsDirect).length = 2 := by decide
example : (evidentials.filter Entry.IsInferential).length = 2 := by decide

end Tibetan.Evidentiality
