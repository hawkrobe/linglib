import Linglib.Theories.Pragmatics.RSA.Implementations.VanTielEtAl2021
import Linglib.Phenomena.ScalarImplicatures.Studies.VanTielEtAl2021

/-!
# Bridge: van Tiel et al. (2021) RSA Model → Scalar Implicature Phenomena
@cite{van-tiel-franke-sauerland-2021}

Connects the RSA quantity-word production model to empirical
monotonicity classifications from `Phenomena.ScalarImplicatures.Studies.VanTielEtAl2021`.
-/

namespace Phenomena.ScalarImplicatures.Bridge.RSAVanTielEtAl2021

open RSA.VanTielEtAl2021

/-- Convert our QuantityWord to Phenomena type -/
def toDataWord : VanTielQuantity.Utterance → Phenomena.ScalarImplicatures.Studies.VanTielEtAl2021.QuantityWord
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
    (monotonicity q = Fragments.English.Determiners.Monotonicity.increasing) ↔
    (Phenomena.ScalarImplicatures.Studies.VanTielEtAl2021.monotonicity (toDataWord q) =
      Phenomena.ScalarImplicatures.Studies.VanTielEtAl2021.Monotonicity.increasing) := by
  cases q <;> native_decide

theorem monotonicity_matches_data_decreasing (q : VanTielQuantity.Utterance) :
    (monotonicity q = Fragments.English.Determiners.Monotonicity.decreasing) ↔
    (Phenomena.ScalarImplicatures.Studies.VanTielEtAl2021.monotonicity (toDataWord q) =
      Phenomena.ScalarImplicatures.Studies.VanTielEtAl2021.Monotonicity.decreasing) := by
  cases q <;> native_decide

end Phenomena.ScalarImplicatures.Bridge.RSAVanTielEtAl2021
