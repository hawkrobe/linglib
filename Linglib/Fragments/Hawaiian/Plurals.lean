import Linglib.Morphology.Number

/-!
# Hawaiian plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace Hawaiian

/-- Hawaiian: plural word (*mau*, prenominal), optional on all nouns;
    person-number stems in pronouns; associative plural absent. -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "Hawaiian"
  , iso := "haw"
  , coding := .pluralWord
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .absent }

end Hawaiian
