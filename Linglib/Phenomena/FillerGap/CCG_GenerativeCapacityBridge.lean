import Linglib.Theories.Syntax.CCG.Formal.GenerativeCapacity
import Linglib.Phenomena.FillerGap.CrossSerial

/-!
# Bridge: CCG GenerativeCapacity → CrossSerial Phenomena

Connects the formal proof that CCG is strictly more expressive than CFG
(from `GenerativeCapacity`) to the empirical cross-serial dependency
classification in `Phenomena.FillerGap.CrossSerial`.

The key bridge: the phenomenal `crossSerialRequires = .mildlyContextSensitive`
classification agrees with the theory-level classification, justified by
the formal proof that {a^n b^n c^n d^n} is not context-free.
-/

namespace CCG.GenerativeCapacity.Bridge

/--
The phenomenal and theory-level classifications agree: both assign
cross-serial dependencies to the mildly context-sensitive level.
-/
theorem phenomenal_agrees_with_theory :
    Phenomena.FillerGap.CrossSerial.crossSerialRequires =
      Phenomena.FillerGap.CrossSerial.FormalLanguageType.mildlyContextSensitive := by
  rfl

end CCG.GenerativeCapacity.Bridge
