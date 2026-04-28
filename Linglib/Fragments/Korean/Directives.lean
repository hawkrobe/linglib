import Linglib.Typology.Directives

/-!
# Korean imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Korean

/-- Korean: second-person morphological imperative with speech-level
    distinctions (*-a*/*-eo* plain, *-seyo* polite, *-(eu)sipsiyo* formal);
    Type 1 prohibitive (*ga-ji ma!* — regular negation pattern with verbal
    *mal-*, retains imperative construction); imperative + hortative *-ja* for
    1PL; no dedicated optative. -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Korean"
  , iso := "kor"
  , morphImp := .secondOnly
  , prohibitive := .normalImpNormalNeg
  , impHortSystem := .imperativeAndHortative
  , optative := some .absent
  , impForms := ["Ga!", "Gaseyo!", "Gaji ma!"]
  , notes := "Multiple speech levels for imperative; hortative -ja; " ++
             "prohibitive -ji mal- retains imperative construction." }

end Fragments.Korean
