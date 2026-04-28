import Linglib.Typology.Plurals

/-!
# Korean plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Korean

/-- Korean: suffix plural (*-tul*), optional on all nouns (number-neutral bare
    forms are common); person-number stems in pronouns (*na*/*uri*);
    associative plural uses the same `-tul` marker. -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Korean"
  , iso := "kor"
  , coding := .suffix
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

end Fragments.Korean
