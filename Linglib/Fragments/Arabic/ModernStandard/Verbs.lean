module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Gender.Basic
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Basic

/-!
# Modern Standard Arabic verbs

The Modern Standard Arabic past tense suffixes to its stem a person marker that also marks
number and gender: *katab-tu* 'I wrote', *katab-at* 'she wrote', *katab-uu* 'they (m.) wrote'.
Ryding counts thirteen markers. The first person does not mark gender, and the dual has no first
person and one marker for both genders of the second.

## Main definitions

* `Arabic.ModernStandard.pastSuffix`: the person marker of the past tense in each cell.

## References

* [ryding-2005]
-/

@[expose] public section

open Morphology

namespace Arabic.ModernStandard

/-- `pastSuffix p n g` is the person marker of the past tense in person `p`, number `n` and gender
`g`, as in Ryding's paradigm of *katab-* 'wrote' ([ryding-2005] p. 443). The first person dual
has none, nor do the numbers and genders the language lacks. -/
def pastSuffix : Person → Number → Gender → Option Morph
  | .first, .singular, .masculine | .first, .singular, .feminine => some (.suff "tu")
  | .second, .singular, .masculine => some (.suff "ta")
  | .second, .singular, .feminine => some (.suff "ti")
  | .third, .singular, .masculine => some (.suff "a")
  | .third, .singular, .feminine => some (.suff "at")
  | .second, .dual, .masculine | .second, .dual, .feminine => some (.suff "tumaa")
  | .third, .dual, .masculine => some (.suff "aa")
  | .third, .dual, .feminine => some (.suff "ataa")
  | .first, .plural, .masculine | .first, .plural, .feminine => some (.suff "naa")
  | .second, .plural, .masculine => some (.suff "tum")
  | .second, .plural, .feminine => some (.suff "tunna")
  | .third, .plural, .masculine => some (.suff "uu")
  | .third, .plural, .feminine => some (.suff "na")
  | _, _, _ => none

/-- The first person does not mark gender. -/
theorem pastSuffix_first_masculine (n : Number) :
    pastSuffix .first n .masculine = pastSuffix .first n .feminine := by
  cases n <;> rfl

end Arabic.ModernStandard
