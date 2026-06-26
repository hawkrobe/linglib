import Linglib.Morphology.Number

/-!
# Turkish plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace Turkish

/-- Turkish: suffix plural (`-ler`, `-lar` with vowel harmony), obligatory on
    all nouns (except after numerals); person-number stems in pronouns
    (*ben*/*biz*, *sen*/*siz*); associative plural uses the same `-ler` marker
    (*Ali-ler* 'Ali and associates'). -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "Turkish"
  , iso := "tur"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

end Turkish
