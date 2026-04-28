import Linglib.Typology.Plurals

/-!
# Hawaiian plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Hawaiian

/-- Hawaiian: plural word (*mau*, prenominal), optional on all nouns;
    person-number stems in pronouns; associative plural absent. -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Hawaiian"
  , iso := "haw"
  , coding := .pluralWord
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .absent }

end Fragments.Hawaiian
