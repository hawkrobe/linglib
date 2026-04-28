import Linglib.Typology.Plurals

/-!
# Finnish plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Finnish

/-- Finnish: suffix plural (*-t* nominative, *-i-* oblique), obligatory on all
    nouns; person-number stem + pronominal affix in pronouns (*minä*/*me*);
    no productive associative plural. -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Finnish"
  , iso := "fin"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .pnStemPronominalAffix
  , associativePlural := .absent }

end Fragments.Finnish
