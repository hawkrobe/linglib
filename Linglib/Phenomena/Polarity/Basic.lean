/-
# Polarity Phenomena

This module covers polarity-sensitive items and environments:
- Negative Polarity Items (NPIs): any, ever, at all
- Positive Polarity Items (PPIs): some (preferred), already
- Disjunction ignorance inferences
- Exceptive constructions

## Cross-references
- Related to Negation/: Licensing environments
- Related to Monotonicity: Entailment-based analysis
- Related to FreeChoice/: FC any vs NPI any
-/

import Linglib.Phenomena.Polarity.NPIs
import Linglib.Phenomena.Polarity.DisjunctionIgnorance
import Linglib.Phenomena.Polarity.Exceptives

namespace Phenomena.Polarity

-- Re-export for convenience
export NPIs (NPIType NPIDatum LicensingContext)
export DisjunctionIgnorance (DisjunctionIgnoranceDatum DisjunctionReading)
export Exceptives (ButExceptiveExample ExceptiveConstruction)

end Phenomena.Polarity
