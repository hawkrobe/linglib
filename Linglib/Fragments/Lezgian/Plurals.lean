import Linglib.Typology.Plurals

/-!
# Lezgian plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Lezgian

/-- Lezgian (Daghestanian): suffix plural (*-ar*, *-er*), obligatory on all
    nouns (but absent with numerals); person-number stems in pronouns;
    associative plural uses the same suffix. -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Lezgian"
  , iso := "lez"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

end Fragments.Lezgian
