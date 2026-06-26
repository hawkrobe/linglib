import Linglib.Morphology.Number

/-!
# Indonesian plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace Indonesian

/-- Indonesian: complete reduplication (*rumah-rumah* 'houses'); plural marking
    optional on all nouns; person-number stems in pronouns (*saya*/*kami*);
    no productive associative plural. -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "Indonesian"
  , iso := "ind"
  , coding := .reduplication
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .absent }

end Indonesian
