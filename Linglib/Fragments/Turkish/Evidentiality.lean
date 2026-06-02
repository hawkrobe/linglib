import Linglib.Semantics.Evidential.Defs

/-!
# Turkish Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

Two-choice direct vs indirect. Past-tense paradigm contrasts *-DI*
(witnessed) with *-mIş* (inferred or reported). The canonical
indirect-evidential of a major language. Fused with TAM. WALS and
Aikhenvald agree.
-/

namespace Turkish.Evidentiality

/-! ### Typed evidential inventory

Turkish's canonical 2-way contrast: `-DI` (direct/witnessed) vs `-mIş`
(indirect, covering inference and report). Fused with past tense. The
`-mIş` is Aikhenvald's classic example of an A2 non-firsthand marker. -/

open Semantics.Evidential

def evidentials : List Entry :=
  [ .direct      { form := "-DI",  exponent := .tamFusion },
    .inferential { form := "-mIş", exponent := .tamFusion } ]

example : evidentials.length = 2 := by decide
example : (evidentials.filter Entry.IsDirect).length = 1 := by decide
example : (evidentials.filter Entry.IsInferential).length = 1 := by decide

end Turkish.Evidentiality
