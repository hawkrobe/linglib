import Linglib.Typology.Plurals

/-!
# Turkish plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Turkish

/-- Turkish: suffix plural (`-ler`, `-lar` with vowel harmony), obligatory on
    all nouns (except after numerals); person-number stems in pronouns
    (*ben*/*biz*, *sen*/*siz*); associative plural uses the same `-ler` marker
    (*Ali-ler* 'Ali and associates'). -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Turkish"
  , iso := "tur"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

end Fragments.Turkish
