import Linglib.Morphology.Number

/-!
# Swahili plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace Swahili

/-- Swahili: plural marked by noun class prefixes (*wa-*, *vi-*, *mi-*, *ma-*),
    obligatory on all nouns; person-number stems in pronouns (*mimi*/*sisi*);
    no productive associative plural. -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "Swahili"
  , iso := "swh"
  , coding := .prefix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .absent }

end Swahili
