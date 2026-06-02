import Linglib.Semantics.Evidential.Defs

/-!
# Georgian Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `directAndIndirect`. @cite{aikhenvald-2004}
analyzes Georgian's evidential perfect ("I screeve") as marking inference
or report only — `indirectOnly`. Studies-side override.
-/

namespace Georgian.Evidentiality

/-! ### Typed evidential inventory

Georgian's evidential perfect (the I screeve), marking inference or
report. Per @cite{aikhenvald-2004}, this is indirect-only. Fused
with TAM (the perfect/screeve system). -/

open Semantics.Evidential

def evidentials : List Entry :=
  [ .inferential { form := "evidential perfect (I screeve)",
                   exponent := .tamFusion } ]

example : evidentials.length = 1 := by decide
example : (evidentials.filter Entry.IsDirect).length = 0 := by decide
example : (evidentials.filter Entry.IsInferential).length = 1 := by decide

end Georgian.Evidentiality
