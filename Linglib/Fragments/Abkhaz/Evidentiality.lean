import Linglib.Semantics.Evidential.Defs

/-!
# Abkhaz Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `indirectOnly` (verbal-affix coding).
@cite{aikhenvald-2004} analyzes Abkhaz as 2-way direct/indirect (fused with
TAM). Studies-side override.
-/

namespace Abkhaz.Evidentiality

/-! ### Typed evidential inventory

Abkhaz's 2-way direct/indirect contrast per @cite{aikhenvald-2004}: the
finite-verb form (direct) vs the nonfinite + copula construction
(indirect, covering inference and report). Fused with TAM. -/

open Semantics.Evidential

def evidentials : List Entry :=
  [ .direct      { form := "finite verb",       exponent := .tamFusion },
    .inferential { form := "nonfinite + copula", exponent := .tamFusion } ]

example : evidentials.length = 2 := by decide
example : (evidentials.filter Entry.IsDirect).length = 1 := by decide
example : (evidentials.filter Entry.IsInferential).length = 1 := by decide
example : (evidentials.filter Entry.IsReportative).length = 0 := by decide

end Abkhaz.Evidentiality
