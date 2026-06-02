import Linglib.Semantics.Evidential.Defs

/-!
# Finnish Evidentiality
[de-haan-2013] [aikhenvald-2004]

WALS [de-haan-2013] F77A: `indirectOnly` (de Haan counts modal verbs
as grammatical evidentials). [aikhenvald-2004] treats Finnish as having
no grammatical evidentials; modality via modal verbs (*voida* 'can',
*täytyä* 'must', *saattaa* 'may'). Studies-side override.
-/

namespace Finnish.Evidentiality

/-! ### Typed evidential inventory (Aikhenvald-strict view)

No grammatical evidentials per [aikhenvald-2004]. WALS divergence
(modal verbs) is documented in `Studies/Aikhenvald2004.lean`. -/

def evidentials : List Semantics.Evidential.Entry := []

example : evidentials.length = 0 := by decide

end Finnish.Evidentiality
