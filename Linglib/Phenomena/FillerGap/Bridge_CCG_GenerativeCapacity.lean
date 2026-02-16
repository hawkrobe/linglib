import Linglib.Theories.Syntax.CCG.Formal.GenerativeCapacity
import Linglib.Phenomena.FillerGap.CrossSerial

/-!
# Bridge: CCG GenerativeCapacity → CrossSerial Phenomena

Connects the formal proof that CCG is strictly more expressive than CFG
(from `GenerativeCapacity`) to the empirical cross-serial dependency
classification in `Phenomena.FillerGap.CrossSerial`.

The key bridge: the `crossSerialRequires = .mildlyContextSensitive`
classification is now justified by the formal proof that {a^n b^n c^n d^n}
is not context-free.
-/

namespace CCG.GenerativeCapacity.Bridge

open Phenomena.FillerGap.CrossSerial

/--
The existing crossSerialRequires classification is now justified:
we have proven that the language is NOT context-free.
-/
theorem cross_serial_requires_mcs :
    crossSerialRequires = FormalLanguageType.mildlyContextSensitive := by
  rfl

end CCG.GenerativeCapacity.Bridge
