import Linglib.Morphology.Number

/-!
# Zulu plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace Zulu

/-- Zulu (Bantu): prefix plural (class prefixes: *umu-ntu*/*aba-ntu*),
    obligatory on all nouns; person-number stems in pronouns; associative
    plural uses the same prefix system (*o-Faku* 'Faku and company'). -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "Zulu"
  , iso := "zul"
  , coding := .prefix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

end Zulu
