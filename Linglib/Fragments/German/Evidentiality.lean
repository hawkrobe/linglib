import Linglib.Semantics.Evidential.Defs

/-!
# German Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `indirectOnly` (de Haan counts modal verbs
*sollen* / *wollen* as grammatical reportatives). @cite{aikhenvald-2004}'s
stricter criterion treats German as having no grammatical evidentials;
Studies-side override in `Studies/Aikhenvald2004.lean`.
-/

namespace German.Evidentiality

/-! ### Typed evidential inventory (Aikhenvald-strict view)

No grammatical evidentials per @cite{aikhenvald-2004}. WALS divergence
(modal verbs *sollen*/*wollen*) is documented in `Studies/Aikhenvald2004.lean`. -/

def evidentials : List Semantics.Evidential.Entry := []

example : evidentials.length = 0 := by decide

end German.Evidentiality
