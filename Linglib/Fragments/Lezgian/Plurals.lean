import Linglib.Morphology.Number

/-!
# Lezgian plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace Lezgian

/-- Lezgian (Daghestanian): suffix plural (*-ar*, *-er*), obligatory on all
    nouns (but absent with numerals); person-number stems in pronouns;
    associative plural uses the same suffix. -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "Lezgian"
  , iso := "lez"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

end Lezgian
