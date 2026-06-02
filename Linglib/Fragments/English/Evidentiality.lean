import Linglib.Semantics.Evidential.Defs

/-!
# English Evidentiality
[de-haan-2013] [aikhenvald-2004]

WALS [de-haan-2013] F77A: `noGrammaticalEvidentials`. Evidential source
is conveyed lexically by adverbs ("apparently", "reportedly") or hedging
expressions, never by obligatory verbal morphology.
-/

namespace English.Evidentiality

/-! ### Typed evidential inventory

No grammatical evidentials per [aikhenvald-2004]; lexical
strategies only. -/

def evidentials : List Semantics.Evidential.Entry := []

example : evidentials.length = 0 := by decide

end English.Evidentiality
