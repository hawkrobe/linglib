import Linglib.Semantics.Evidential.Defs

/-!
# English Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `noGrammaticalEvidentials`. Evidential source
is conveyed lexically by adverbs ("apparently", "reportedly") or hedging
expressions, never by obligatory verbal morphology.
-/

namespace English.Evidentiality

/-! ### Typed evidential inventory

No grammatical evidentials per @cite{aikhenvald-2004}; lexical
strategies only. -/

def evidentials : List Semantics.Evidential.Entry := []

example : evidentials.length = 0 := by decide

end English.Evidentiality
