import Linglib.Semantics.Evidential.Defs

/-!
# French Evidentiality
[de-haan-2013] [aikhenvald-2004]

WALS [de-haan-2013] F77A: `indirectOnly` (de Haan codes the conditional
as a grammatical reportative). [aikhenvald-2004]'s stricter criterion
treats French as having no grammatical evidentials; Studies-side override
in `Studies/Aikhenvald2004.lean`.
-/

namespace French.Evidentiality

/-! ### Typed evidential inventory (Aikhenvald-strict view)

No grammatical evidentials per [aikhenvald-2004]. WALS divergence
(conditional reportative use) is documented in `Studies/Aikhenvald2004.lean`. -/

def evidentials : List Semantics.Evidential.Entry := []

example : evidentials.length = 0 := by decide

end French.Evidentiality
