/-
# Quantification Phenomena

Quantifier scope and numeral semantics.

## Main definitions
- `ScopeFreezing.Availability`, `ScopeFreezing.FreezingContext`
- `Numerals.NumeralImprecisionDatum`, `Numerals.RoundnessLevel`

## References
- May (1985). Logical Form.
- Krifka (2007). Approximate interpretation.
- Solt (2014, 2018). Imprecise numerals.
-/

import Linglib.Phenomena.Quantification.ScopeFreezing
import Linglib.Phenomena.Quantification.ScopeWordOrder
import Linglib.Phenomena.Quantification.Numerals

namespace Phenomena.Quantification

export ScopeFreezing (Availability FreezingContext)
export Numerals (NumeralImprecisionDatum RoundnessLevel)

end Phenomena.Quantification
