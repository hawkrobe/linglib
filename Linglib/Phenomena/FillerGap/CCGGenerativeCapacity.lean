import Linglib.Theories.Syntax.CCG.Formal.GenerativeCapacity
import Linglib.Phenomena.WordOrder.CrossSerial

/-!
# Bridge: CCG GenerativeCapacity → CrossSerial Phenomena

Connects the formal proof that CCG is strictly more expressive than CFG
(from `GenerativeCapacity`) to the empirical cross-serial dependency
classification in `Phenomena.WordOrder.CrossSerial`.

Both layers now use the canonical `Core.FormalLanguageType`, so the
agreement is definitional.
-/

namespace CCG.GenerativeCapacity.Bridge

/--
The phenomenal classification agrees with the theory-level result: both assign
cross-serial dependencies to the mildly context-sensitive level.

`Phenomena.WordOrder.CrossSerial.crossSerialRequires` reduces to
`Core.FormalLanguageType.mildlyContextSensitive`, matching the
generative capacity established by `CCG.GenerativeCapacity.ccg_exceeds_cfg`.
-/
theorem phenomenal_agrees_with_theory :
    Phenomena.WordOrder.CrossSerial.crossSerialRequires =
      Core.FormalLanguageType.mildlyContextSensitive := by
  rfl

end CCG.GenerativeCapacity.Bridge
