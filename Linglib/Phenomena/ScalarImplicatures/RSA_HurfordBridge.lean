import Linglib.Theories.Pragmatics.RSA.ScalarImplicatures.Hurford
import Linglib.Phenomena.ScalarImplicatures.Basic

/-!
# Bridge: RSA Hurford Constraint → Phenomena

Connects the RSA Hurford constraint model (`RSA.Hurford`) to empirical
data from `Phenomena.ScalarImplicatures.Basic`.

## Status

The ℚ-based RSA computation functions have been removed. Bridge theorems
need to be re-derived using the new RSAConfig framework.

## Bridge content (to be re-derived)

- `rsa_matches_data_someOrAll`: RSA predicts "some or all" is felicitous
- `rsa_matches_data_americanCalifornian`: RSA predicts "American or Californian" is infelicitous
-/


namespace RSA.Hurford.Bridge

open Phenomena.ScalarImplicatures

/--
RSA prediction matches empirical data for "some or all".

The model predicts "some or all" is felicitous (disjunction informative under
refined lexicon), matching the empirical judgment in Data.lean.
-/
theorem rsa_matches_data_someOrAll :
    someOrAll.felicitous = true := by
  sorry  -- TODO: re-derive with RSAConfig

/--
RSA prediction matches empirical data for "American or Californian".

RSA predicts infelicity (disjunction always redundant), matching the empirical judgment.
-/
theorem rsa_matches_data_americanCalifornian :
    americanCalifornian.felicitous = false := by
  sorry  -- TODO: re-derive with RSAConfig

end RSA.Hurford.Bridge
