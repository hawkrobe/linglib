/-
# Montague Numerals (Re-export)

This module re-exports numeral semantics from the Lexicon.

See `Montague.Lexicon.Numerals` for the full implementation including:
- `Theory.lean`: Core numeral theory infrastructure
- `LowerBound.lean`: Horn (1972) lower-bound semantics
- `Bilateral.lean`: Exact/bilateral semantics
- `Compare.lean`: Theory comparison theorems
-/

import Linglib.Theories.Montague.Lexicon.Numerals.Theory
import Linglib.Theories.Montague.Lexicon.Numerals.LowerBound
import Linglib.Theories.Montague.Lexicon.Numerals.Bilateral
import Linglib.Theories.Montague.Lexicon.Numerals.Compare

namespace Montague.Numbers

-- Re-export key types and functions
export Montague.Lexicon.Numerals (
  NumWord
  NumeralTheory
  LowerBound
  Bilateral
)

end Montague.Numbers
