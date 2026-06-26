import Linglib.Morphology.Number

/-!
# Hindi plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace Hindi

/-- Hindi: suffix plural (*-e*, *-en*, *-iya*), obligatory on all nouns;
    person-number stems in pronouns (*main* vs *ham*); associative plural
    uses the same plural marker (*Sharma-log* 'Sharma and family'). -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "Hindi"
  , iso := "hin"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

end Hindi
