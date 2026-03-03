import Linglib.Theories.Pragmatics.RSA.ScalarImplicatures.Embedded.Basic
import Linglib.Phenomena.ScalarImplicatures.Basic

/-!
# RSA Embedded Scalar Implicatures → Phenomena
@cite{geurts-2010}

Connects the RSA embedded scalar implicature model (`RSA.EmbeddedScalars`)
to empirical data from `Phenomena.ScalarImplicatures.Basic`.

## Content

- `empirical_pattern_documented`: Verifies the DE blocking / UE allowing
  pattern from @cite{geurts-2010} against the `someAllBlocking` data.
-/


namespace Phenomena.ScalarImplicatures.Studies.Geurts2010

open RSA.EmbeddedScalars
open Phenomena.ScalarImplicatures

/--
**Connection to empirical pattern**.

The empirical data shows:
- DE: implicature blocked (global preferred)
- UE: implicature arises (local preferred)

Our simple LU model predicts the opposite.
The full Potts et al. model derives the correct pattern.
-/
theorem empirical_pattern_documented :
    -- Empirical: DE blocks, UE allows
    someAllBlocking.implicatureInDE = false ∧
    someAllBlocking.implicatureInUE = true := by
  native_decide

end Phenomena.ScalarImplicatures.Studies.Geurts2010
