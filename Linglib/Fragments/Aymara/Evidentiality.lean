import Linglib.Semantics.Evidential.Defs

/-!
# Aymara Evidentiality
@cite{aikhenvald-2004}

Three-or-more system: direct, reportative, non-personal/inferential. Andean
areal feature shared with Quechua. WALS Ch 77 has no entry; fallback fires.
-/

namespace Aymara.Evidentiality

/-! ### Typed evidential inventory

Aymara's 3-way Andean system: direct `-wa`, reportative `-sa`,
inferential `-pacha`. Obligatory verbal affixes. -/

open Semantics.Evidential

def evidentials : List Entry :=
  [ .direct      { form := "-wa",     exponent := .verbalAffix },
    .reportative { form := "-sa",     exponent := .verbalAffix,
                   sourceIdentity := .unidentified },
    .inferential { form := "-pacha",  exponent := .verbalAffix } ]

example : evidentials.length = 3 := by decide
example : (evidentials.filter Entry.IsDirect).length = 1 := by decide
example : (evidentials.filter Entry.IsReportative).length = 1 := by decide
example : (evidentials.filter Entry.IsInferential).length = 1 := by decide

end Aymara.Evidentiality
