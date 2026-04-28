import Linglib.Typology.Plurals

/-!
# Indonesian plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Indonesian

/-- Indonesian: complete reduplication (*rumah-rumah* 'houses'); plural marking
    optional on all nouns; person-number stems in pronouns (*saya*/*kami*);
    no productive associative plural. -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Indonesian"
  , iso := "ind"
  , coding := .reduplication
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .absent }

end Fragments.Indonesian
