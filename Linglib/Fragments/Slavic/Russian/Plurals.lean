import Linglib.Typology.Plurals

/-!
# Russian plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Slavic.Russian

/-- Russian: suffix plural (*-y*, *-i*, *-a*), obligatory on all nouns;
    person-number stem + nominal plural affix in pronouns (*ja* vs *m-y*);
    no productive associative plural. -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Russian"
  , iso := "rus"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .pnStemNominalAffix
  , associativePlural := .absent }

end Fragments.Slavic.Russian
