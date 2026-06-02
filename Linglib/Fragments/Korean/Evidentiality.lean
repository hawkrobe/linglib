import Linglib.Semantics.Evidential.Defs

/-!
# Korean Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `indirectOnly` (de Haan counts *-deo-*
retrospective as grammatical evidential). @cite{aikhenvald-2004} treats it
as not classified as grammatical evidential; Studies-side override.
-/

namespace Korean.Evidentiality

/-! ### Typed evidential inventory (Aikhenvald-strict view)

No grammatical evidentials per @cite{aikhenvald-2004}. WALS divergence
(retrospective `-deo-`) is documented in `Studies/Aikhenvald2004.lean`. -/

def evidentials : List Semantics.Evidential.Entry := []

example : evidentials.length = 0 := by decide

end Korean.Evidentiality
