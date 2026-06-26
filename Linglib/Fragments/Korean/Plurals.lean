import Linglib.Morphology.Number

/-!
# Korean plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace Korean

/-- Korean: suffix plural (*-tul*), optional on all nouns (number-neutral bare
    forms are common); person-number stems in pronouns (*na*/*uri*);
    associative plural uses the same `-tul` marker. -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "Korean"
  , iso := "kor"
  , coding := .suffix
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

end Korean
