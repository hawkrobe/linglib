module

public import Linglib.Syntax.Category.Pronoun.Logophoric

/-!
# Ewe pronouns

This file defines the Ewe logophoric pronoun *yè*, which occurs in the scope of an attitude
predicate such as 'say' or 'believe' and refers to the bearer of the attitude ([pearson-2015]);
it also appears under psychological predicates ([sells-1987], after Clements). In the role
terms of [sells-1987] its antecedent is therefore at least a self: a reporter or a thinker
licenses it, a mere point-of-view centre does not. Sells himself suggests that logophoric
pronouns proper are source-oriented, since their complementizer derives from 'say'.

## References

* [H. Pearson, *The interpretation of the logophoric pronoun in Ewe* (2015)][pearson-2015]
* [P. Sells, *Aspects of Logophoricity* (1987)][sells-1987]
-/

@[expose] public section

namespace Ewe.Pronouns

open Reference (Logophoric)

/-- The logophoric pronoun *yè*, whose antecedent is at least a self. -/
def ye : LogophoricPronoun := { form := "yè", person := some .third, requiredRole := .self }

/-- A thinker licenses *yè*. -/
theorem ye_licensedBy_self : Logophoric.LicensedBy ye .self := by decide

/-- A point-of-view centre that holds no attitude does not license *yè*. -/
theorem ye_not_licensedBy_pivot : ¬ Logophoric.LicensedBy ye .pivot := by decide

end Ewe.Pronouns
