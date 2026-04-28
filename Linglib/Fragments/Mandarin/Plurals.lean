import Linglib.Typology.Plurals

/-!
# Mandarin plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Mandarin

/-- Mandarin Chinese: no morphological plural on common nouns (bare nouns are
    number-neutral); person stem + nominal plural affix `-men` on pronouns
    (*wo* / *wo-men* 'I/we'); associative plural uses the same `-men` marker. -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Mandarin"
  , iso := "cmn"
  , coding := .noPlural
  , occurrence := .noNominalPlural
  , pronounPlurality := .personStemNominalAffix
  , associativePlural := .sameAsAdditive }

end Fragments.Mandarin
