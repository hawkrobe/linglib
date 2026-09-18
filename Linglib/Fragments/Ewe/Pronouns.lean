import Linglib.Syntax.Category.Pronoun.Logophoric

/-!
# Ewe pronouns

This file defines the Ewe logophoric pronoun *yè*, which stands in the complement of a verb of
saying or thinking for the person whose speech or thought is reported. In the terms of
[sells-1987] its antecedent must be at least a self: a reporter or a thinker licenses it, a mere
point-of-view centre does not.

## References

* [P. Sells, *Aspects of Logophoricity* (1987)][sells-1987]
-/

namespace Ewe.Pronouns

open Reference (Logophoric)

/-- The logophoric pronoun *yè*, whose antecedent is at least a self. -/
def ye : LogophoricPronoun := { form := "yè", person := some .third, requiredRole := .self }

/-- A thinker licenses *yè*. -/
theorem ye_licensedBy_self : Logophoric.LicensedBy ye .self := by decide

/-- A point-of-view centre that holds no attitude does not license *yè*. -/
theorem ye_not_licensedBy_pivot : ¬ Logophoric.LicensedBy ye .pivot := by decide

end Ewe.Pronouns
