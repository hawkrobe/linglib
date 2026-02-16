import Linglib.Theories.Pragmatics.RSA.Implementations.VanTielEtAl2021
import Linglib.Phenomena.ScalarImplicatures.Studies.VanTielEtAl2021

/-!
# Bridge: van Tiel et al. (2021) RSA Model → Scalar Implicature Phenomena

Connects the RSA quantity-word production model to empirical
monotonicity classifications from `Phenomena.ScalarImplicatures.Studies.VanTielEtAl2021`.
-/

namespace RSA.VanTielEtAl2021.Bridge

open RSA.VanTielEtAl2021
open VanTielQuantity

/-- Convert our QuantityWord to Phenomena type -/
def toDataWord : VanTielQuantity.Utterance → Phenomena.VanTielEtAl2021.QuantityWord
  | .none_ => .none_
  | .few   => .few
  | .some_ => .some_
  | .half  => .half
  | .most  => .most
  | .all   => .all

/-- Our monotonicity matches empirical classification for clear cases.

Note: "half" is classified as nonMonotone in our three-way system but as
"increasing" in the binary empirical classification. This is because the
empirical classification only distinguishes licensing upward vs downward
inferences, while we add a third category for non-monotonic quantifiers.
-/
theorem monotonicity_matches_data_increasing (q : VanTielQuantity.Utterance) :
    q ≠ .half →
    (monotonicity q = .increasing) ↔
    (Phenomena.VanTielEtAl2021.monotonicity (toDataWord q) = .increasing) := by
  cases q <;> native_decide

theorem monotonicity_matches_data_decreasing (q : VanTielQuantity.Utterance) :
    (monotonicity q = .decreasing) ↔
    (Phenomena.VanTielEtAl2021.monotonicity (toDataWord q) = .decreasing) := by
  cases q <;> native_decide

end RSA.VanTielEtAl2021.Bridge
