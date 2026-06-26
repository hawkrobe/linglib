import Linglib.Morphology.Number

/-!
# Japanese plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace Japanese

/-- Japanese: no morphological plural on common nouns; plural marking is always
    optional (suffix `-tachi` is limited and optional); person-number stems in
    pronouns; unique periphrastic associative plural (`-tachi` on proper names:
    *Tanaka-tachi* 'Tanaka and associates'). -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , coding := .noPlural
  , occurrence := .noNominalPlural
  , pronounPlurality := .personNumberStem
  , associativePlural := .uniquePeriphrastic }

end Japanese
