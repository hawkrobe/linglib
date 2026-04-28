import Linglib.Typology.Plurals

/-!
# English plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.English

/-- English: suffix plural (-s), obligatory on all nouns, person-number
    stems in pronouns, no productive associative plural. -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "English"
  , iso := "eng"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .absent }

end Fragments.English
