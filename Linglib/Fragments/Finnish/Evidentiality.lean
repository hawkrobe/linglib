import Linglib.Semantics.Evidential.Defs

/-!
# Finnish Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `indirectOnly` (de Haan counts modal verbs
as grammatical evidentials). @cite{aikhenvald-2004} treats Finnish as having
no grammatical evidentials; modality via modal verbs (*voida* 'can',
*täytyä* 'must', *saattaa* 'may'). Studies-side override.
-/

namespace Finnish.Evidentiality

/-! ### Typed evidential inventory (Aikhenvald-strict view)

No grammatical evidentials per @cite{aikhenvald-2004}. WALS divergence
(modal verbs) is documented in `Studies/Aikhenvald2004.lean`. -/

def evidentials : List Semantics.Evidential.Entry := []

example : evidentials.length = 0 := by decide

end Finnish.Evidentiality
