/-
# Dependencies Phenomena

This module covers filler-gap dependency phenomena:
- Long-distance dependencies (wh-movement, topicalization)

Cross-serial dependencies (Dutch verb clusters) are in `Phenomena.WordOrder.CrossSerial`.

## Cross-references
- Related to Islands/: Constraints on extraction
- Related to Ellipsis/: Sluicing as island repair
-/

import Linglib.Phenomena.FillerGap.LongDistance
import Linglib.Phenomena.FillerGap.Studies.Sag2010

namespace Phenomena.FillerGap

export LongDistance (longDistanceData)
export Sag2010 (FGClauseType FGParameters fgParams)

end Phenomena.FillerGap
