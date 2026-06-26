import Linglib.Morphology.Number

/-!
# English plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace English

/-- English: suffix plural (-s), obligatory on all nouns, person-number
    stems in pronouns, no productive associative plural. -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "English"
  , iso := "eng"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .absent }

end English
