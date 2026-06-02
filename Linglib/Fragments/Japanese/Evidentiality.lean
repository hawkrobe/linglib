import Linglib.Semantics.Evidential.Defs

/-!
# Japanese Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `indirectOnly` (de Haan classifies *soo da*,
*rashii* as grammatical evidentials). @cite{aikhenvald-2004} treats these as
modal rather than evidential; Studies-side override.
-/

namespace Japanese.Evidentiality

/-! ### Typed evidential inventory (Aikhenvald-strict view)

No grammatical evidentials per @cite{aikhenvald-2004}. WALS divergence
(modal *soo da* / *rashii*) is documented in `Studies/Aikhenvald2004.lean`. -/

def evidentials : List Semantics.Evidential.Entry := []

example : evidentials.length = 0 := by decide

end Japanese.Evidentiality
