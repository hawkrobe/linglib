import Linglib.Core.Scales.Defs
import Linglib.Core.Scales.Rat01
import Linglib.Core.Scales.Comparative
import Linglib.Core.Scales.DirectedMeasure
import Linglib.Core.Scales.Predicate
import Linglib.Core.Scales.Bounds
import Linglib.Core.Scales.HasMeasure
import Linglib.Core.Scales.HasComparison
import Linglib.Core.Scales.LawfulComparison
import Linglib.Core.Scales.HasPositiveForm

/-!
# Core/Scales/Scale.lean — re-export shim (A.9)

Per master plan v4 Phase A.9, this file is a thin re-export shim of the
decomposed `Core/Scales/` substrate. The original 1150-LOC dumping-ground
content has been carved into:

- `Defs.lean` — Boundedness, MereoTag, LicensingPipeline, ScalePolarity
- `Rat01.lean` — rational unit interval [0, 1]
- `Comparative.lean` — ComparativeScale + AdditiveScale
- `DirectedMeasure.lean` — DirectedMeasure + Kennedy/Rouillard MIP-domain operators
  (the framework operators move to `Theories/Semantics/Gradability/{Kennedy,Rouillard}.lean`
  in Phase B)
- `Predicate.lean` — IsUpwardMonotone/etc. + eqDeg/atLeastDeg/etc. + relationalGQ
- `Bounds.lean` — typeclass licensing theorems + maxOnScale/IsMaxDetermined
- `HasMeasure.lean` — HasMeasure typeclass (renames HasDegree) + Degree/Threshold types
- `HasComparison.lean` — primitive comparison typeclass + ofMeasure smart constructor
- `LawfulComparison.lean` — opt-in lawfulness mixin (extends mathlib IsStrictOrder)
- `HasPositiveForm.lean` — positive-form typeclass parameterized by Source

All sub-files declare `namespace Core.Scale` (do-no-harm constraint #23).
Consumers continue to work via this shim's re-exports through end of Phase F;
the shim is deleted in Phase F.6 after gradual per-consumer import migration
in Phase F.5b.
-/
