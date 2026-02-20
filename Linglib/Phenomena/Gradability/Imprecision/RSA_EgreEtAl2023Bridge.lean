import Linglib.Theories.Pragmatics.RSA.Implementations.EgreEtAl2023
import Linglib.Phenomena.Gradability.Imprecision.Numerals
import Linglib.Phenomena.Gradability.Imprecision.Studies.EgreEtAl2023

/-!
# Bridge: RSA Imprecision Model → Phenomena Data

Connects the BIR closed-form predictions from Egre et al. (2023)
to empirical data in `Phenomena.Gradability.Imprecision.Studies.EgreEtAl2023`.

## Bridge Theorems

- `closed_form_matches_phenomena_center`: BIR closed form = data for center value
- `closed_form_matches_phenomena_offset5`: BIR closed form = data for offset-5 value
-/


namespace Phenomena.Gradability.Imprecision.RSA_EgreEtAl2023Bridge

open RSA.EgreEtAl2023

/-- Closed form matches Phenomena datum for center: P(x=20 | around 20) = 21/441. -/
theorem closed_form_matches_phenomena_center :
    birClosedForm 20 20 =
    Phenomena.Gradability.Imprecision.Studies.EgreEtAl2023.closedForm_center.expectedProb := by
  native_decide

/-- Closed form matches Phenomena datum for offset: P(x=15 | around 20) = 16/441. -/
theorem closed_form_matches_phenomena_offset5 :
    birClosedForm 20 15 =
    Phenomena.Gradability.Imprecision.Studies.EgreEtAl2023.closedForm_offset5.expectedProb := by
  native_decide

end Phenomena.Gradability.Imprecision.RSA_EgreEtAl2023Bridge
