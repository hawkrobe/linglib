import Linglib.Typology.Directives

/-!
# Mandarin imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Mandarin

/-- Mandarin Chinese: no morphological imperative (commands via bare verb,
    intonation, sentence-final particles *ba*, *a*); special prohibitive
    particle *bie* (别), distinct from declarative *bu*/*mei* — coded as
    Type 2 (special negation); no hortative or jussive morphology;
    no optative. -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , morphImp := .noMorphological
  , prohibitive := .normalImpSpecialNeg
  , impHortSystem := .imperativeOnly
  , optative := some .absent
  , impForms := ["Zou!", "Bie zou!"]
  , notes := "No morphological imperative; bare verb + intonation/particles; " ++
             "special prohibitive bie (别) vs declarative bu/mei." }

end Fragments.Mandarin
