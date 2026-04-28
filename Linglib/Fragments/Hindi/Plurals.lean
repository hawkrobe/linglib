import Linglib.Typology.Plurals

/-!
# Hindi plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Hindi

/-- Hindi: suffix plural (*-e*, *-en*, *-iya*), obligatory on all nouns;
    person-number stems in pronouns (*main* vs *ham*); associative plural
    uses the same plural marker (*Sharma-log* 'Sharma and family'). -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Hindi"
  , iso := "hin"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

end Fragments.Hindi
