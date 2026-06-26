import Linglib.Morphology.Number

/-!
# Finnish plurality profile (WALS Chs 33–36)
[wals-2013]
-/

namespace Finnish

/-- Finnish: suffix plural (*-t* nominative, *-i-* oblique), obligatory on all
    nouns; person-number stem + pronominal affix in pronouns (*minä*/*me*);
    no productive associative plural. -/
def pluralityProfile : Morphology.Number.PluralityProfile :=
  { language := "Finnish"
  , iso := "fin"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .pnStemPronominalAffix
  , associativePlural := .absent }

end Finnish
