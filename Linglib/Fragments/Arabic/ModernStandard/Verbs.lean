module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Agreement.Paradigm

/-!
# Modern Standard Arabic verbs

The Modern Standard Arabic past tense suffixes to its stem a person marker that also marks
number and gender: *katab-tu* 'I wrote', *katab-at* 'she wrote', *katab-uu* 'they (m.) wrote'.
Ryding counts thirteen markers. The first person does not mark gender, and the dual has no first
person and one marker for both genders of the second.

## Main definitions

* `Arabic.ModernStandard.pastSuffix`: the person markers of the past tense, by cell.

## References

* [ryding-2005]
-/

@[expose] public section

open Morphology

namespace Arabic.ModernStandard

open Agreement

/-- The person markers of the past tense, by person, number and gender, as in Ryding's paradigm
of *katab-* 'wrote' ([ryding-2005] p. 443). -/
def pastSuffix : Paradigm Morph :=
  [(Bundle.pn .first .singular, .suff "tu"),
   (Function.update (Bundle.pn .second .singular) .gender ↑Gender.masculine, .suff "ta"),
   (Function.update (Bundle.pn .second .singular) .gender ↑Gender.feminine, .suff "ti"),
   (Function.update (Bundle.pn .third .singular) .gender ↑Gender.masculine, .suff "a"),
   (Function.update (Bundle.pn .third .singular) .gender ↑Gender.feminine, .suff "at"),
   (Bundle.pn .second .dual, .suff "tumaa"),
   (Function.update (Bundle.pn .third .dual) .gender ↑Gender.masculine, .suff "aa"),
   (Function.update (Bundle.pn .third .dual) .gender ↑Gender.feminine, .suff "ataa"),
   (Bundle.pn .first .plural, .suff "naa"),
   (Function.update (Bundle.pn .second .plural) .gender ↑Gender.masculine, .suff "tum"),
   (Function.update (Bundle.pn .second .plural) .gender ↑Gender.feminine, .suff "tunna"),
   (Function.update (Bundle.pn .third .plural) .gender ↑Gender.masculine, .suff "uu"),
   (Function.update (Bundle.pn .third .plural) .gender ↑Gender.feminine, .suff "na")]

/-- A person marker of the past tense marks gender except in the first person and the second
person dual. -/
theorem pastSuffix_gender_eq_bot_iff :
    ∀ c ∈ pastSuffix.cells, c .gender = ⊥ ↔ c .person = ↑Person.first ∨ c = .pn .second .dual := by
  decide

end Arabic.ModernStandard
