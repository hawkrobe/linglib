import Linglib.Morphology.Number

/-!
# Russian plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace Russian

/-- Russian: suffix plural (*-y*, *-i*, *-a*), obligatory on all nouns;
    person-number stem + nominal plural affix in pronouns (*ja* vs *m-y*);
    no productive associative plural. -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "Russian"
  , iso := "rus"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .pnStemNominalAffix
  , associativePlural := .absent }

end Russian
