/-
# Montague Numerals (Re-export)

This module re-exports numeral semantics from the Lexicon.

See `Montague.Determiner.Numeral` for the full implementation including:
- `Theory.lean`: Core numeral theory infrastructure
- `LowerBound.lean`: Horn (1972) lower-bound semantics
- `Bilateral.lean`: Exact/bilateral semantics
- `Compare.lean`: Theory comparison theorems
-/

import Linglib.Theories.Montague.Determiner.Numeral.Theory
import Linglib.Theories.Montague.Determiner.Numeral.LowerBound
import Linglib.Theories.Montague.Determiner.Numeral.Bilateral
import Linglib.Theories.Montague.Determiner.Numeral.Compare

namespace Montague.Numbers

-- Re-export key types and functions
export Montague.Determiner.Numeral (
  NumWord
  NumeralTheory
  LowerBound
  Bilateral
)

end Montague.Numbers
