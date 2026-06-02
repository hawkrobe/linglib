import Linglib.Semantics.Evidential.Defs

/-!
# Mandarin Chinese Evidentiality
[de-haan-2013] [aikhenvald-2004]

WALS [de-haan-2013] F77A: `noGrammaticalEvidentials`. Lexical
strategies: *tinshuo* (听说), *juede* (觉得), sentence-final *ba* (吧).
-/

namespace Mandarin.Evidentiality

/-! ### Typed evidential inventory

No grammatical evidentials per [aikhenvald-2004]; lexical
strategies only. -/

def evidentials : List Semantics.Evidential.Entry := []

example : evidentials.length = 0 := by decide

end Mandarin.Evidentiality
