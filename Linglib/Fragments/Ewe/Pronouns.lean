module

public import Linglib.Syntax.Category.Pronoun.Logophoric

/-!
# Ewe pronouns

The Ewe logophoric pronoun *yè* occurs in the scope of an attitude predicate such as 'say' or
'believe' and refers to the bearer of the attitude, as Pearson describes. Sells, after Clements,
gives it also under psychological predicates.

## References

* [pearson-2015]
* [sells-1987]
-/

@[expose] public section

namespace Ewe.Pronouns

/-- The logophoric pronoun *yè*. -/
def ye : LogophoricPronoun Empty := { form := "yè", person := some .third }

end Ewe.Pronouns
