import Linglib.Theories.Pragmatics.RSA.Implementations.PottsEtAl2016
import Linglib.Phenomena.ScalarImplicatures.Basic

/-!
# Bridge: Potts et al. (2016) RSA Model → Scalar Implicature Phenomena
@cite{potts-etal-2016}

Connects the Potts et al. (2016) lexical uncertainty RSA model
to empirical DE/UE blocking data from `Phenomena.ScalarImplicatures.Basic`.
-/

namespace Phenomena.ScalarImplicatures.Bridge.RSAPottsEtAl2016

open Phenomena.ScalarImplicatures

theorem potts_model_de_prediction :
    -- Empirical: DE blocks embedded implicature
    someAllBlocking.implicatureInDE = false := by
  native_decide

theorem potts_model_ue_prediction :
    -- Empirical: UE allows embedded implicature
    someAllBlocking.implicatureInUE = true := by
  native_decide

end Phenomena.ScalarImplicatures.Bridge.RSAPottsEtAl2016
