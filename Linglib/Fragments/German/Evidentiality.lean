import Linglib.Semantics.Evidential.Defs

/-!
# German Evidentiality
[de-haan-2013] [aikhenvald-2004]

WALS [de-haan-2013] F77A: `indirectOnly` (de Haan counts modal verbs
*sollen* / *wollen* as grammatical reportatives). [aikhenvald-2004]'s
stricter criterion treats German as having no grammatical evidentials;
Studies-side override in `Studies/Aikhenvald2004.lean`.
-/

namespace German.Evidentiality

/-! ### Typed evidential inventory (Aikhenvald-strict view)

No grammatical evidentials per [aikhenvald-2004]. WALS divergence
(modal verbs *sollen*/*wollen*) is documented in `Studies/Aikhenvald2004.lean`. -/

def evidentials : List Semantics.Evidential.Entry := []

example : evidentials.length = 0 := by decide

end German.Evidentiality
