import Linglib.Typology.Plurals

/-!
# Arabic plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Arabic

/-- Standard Arabic: mixed morphological plural — both suffixation
    (*-aat*, *-uun*) and "broken" stem-internal changes are productive,
    neither clearly primary. Obligatory on all nouns; person-number stem in
    pronouns (*ana*/*nahnu*); associative plural same as additive. -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Arabic"
  , iso := "arb"
  , coding := .mixedMorphological
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .personNumberStem
  , associativePlural := .sameAsAdditive }

end Fragments.Arabic
