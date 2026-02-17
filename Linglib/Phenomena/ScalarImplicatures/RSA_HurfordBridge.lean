import Linglib.Theories.Pragmatics.RSA.ScalarImplicatures.Hurford
import Linglib.Phenomena.ScalarImplicatures.Basic

/-!
# Bridge: RSA Hurford Constraint → Phenomena

Connects the RSA Hurford constraint model (`RSA.Hurford`) to empirical
data from `Phenomena.ScalarImplicatures.Basic`.

## Bridge content

- `rsa_matches_data_someOrAll`: RSA predicts "some or all" is felicitous
- `rsa_matches_data_americanCalifornian`: RSA predicts "American or Californian" is infelicitous
-/


namespace RSA.Hurford.Bridge

open RSA.Hurford
open Phenomena.ScalarImplicatures

/--
RSA prediction matches empirical data for "some or all".

The model predicts "some or all" is felicitous (disjunction informative under
refined lexicon), matching the empirical judgment in Data.lean.
-/
theorem rsa_matches_data_someOrAll :
    rsaPredictsFelicitous_someOrAll = someOrAll.felicitous := by
  native_decide

/--
RSA prediction matches empirical data for "American or Californian".

RSA predicts infelicity (disjunction always redundant), matching the empirical judgment.
-/
theorem rsa_matches_data_americanCalifornian :
    rsaPredictsFelicitous_americanCalifornian = americanCalifornian.felicitous := by
  native_decide

end RSA.Hurford.Bridge
