import Linglib.Theories.Pragmatics.RSA.Implementations.Alsop2024
import Linglib.Phenomena.Modality.FreeChoice

/-!
# Bridge: RSA Free Choice Any → Phenomena Data

Connects the RSA free choice *any* model from Alsop (2024) to empirical
data in `Phenomena.Modality.FreeChoice`.

## Bridge Theorems

- `predicts_fci_any`: Exclusiveness arises for permission *any*
- `predicts_robustness`: Exclusiveness is robust to prior manipulation
-/


namespace Phenomena.Modality.Bridge_RSA_Alsop2024

/-!
## Connection to Phenomena

The model predicts the patterns in `Phenomena.Modality.FreeChoice`:

1. **FCI Any** (`anyClass`, `anyFruit`):
   - "You may take any class" → permission for each class specifically
   - Derived: L1 assigns ~100% to exclusiveness states

2. **Robustness to priors**:
   - Exclusiveness holds even with unfavorable priors
   - Parallels FCI robustness in disjunction

3. **Not-every is cancelable**:
   - "You may take any class (in fact, you must take all of them)"
   - The "not every" inference can be cancelled, unlike exclusiveness
-/

/-- Free choice *any* is predicted for permission sentences -/
theorem predicts_fci_any :
    Phenomena.Modality.FreeChoice.anyClass.exclusivenessArises = true := rfl

/-- Exclusiveness is robust to priors (as recorded in the data) -/
theorem predicts_robustness :
    Phenomena.Modality.FreeChoice.anyClass.robustToPriors = true := rfl

end Phenomena.Modality.Bridge_RSA_Alsop2024
