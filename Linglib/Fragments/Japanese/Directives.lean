import Linglib.Typology.Directives

/-!
# Japanese imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Japanese

/-- Japanese: second-person-only morphological imperative (suffix *-e*/*-ro*:
    *ike!* 'go!', *tabero!* 'eat!'); Type 2 prohibitive (*iku-na!* — imperative
    stem + special negation *-na*, distinct from declarative *-nai*); no
    dedicated hortative (volitional *-ou*/*-you* serves a related but distinct
    function); no morphological optative. -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , morphImp := .secondOnly
  , prohibitive := .normalImpSpecialNeg
  , impHortSystem := .imperativeOnly
  , optative := some .absent
  , impForms := ["ike!", "iku-na!"]
  , notes := "Plain imperative -e/-ro; prohibitive -na is special negation; " ++
             "volitional -ou/-you is distinct from hortative." }

end Fragments.Japanese
