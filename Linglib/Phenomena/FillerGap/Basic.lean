/-
# Dependencies Phenomena

This module covers syntactic dependency phenomena:
- Long-distance dependencies (wh-movement, topicalization)
- Cross-serial dependencies (Dutch verb raising, Swiss German)

## Cross-references
- Related to Islands/: Constraints on extraction
- Related to Ellipsis/: Sluicing as island repair
-/

import Linglib.Phenomena.FillerGap.LongDistance
import Linglib.Phenomena.FillerGap.CrossSerial

namespace Phenomena.FillerGap

export LongDistance (longDistanceData)
export CrossSerial (Dependency DependencyPattern DutchExample)

end Phenomena.FillerGap
