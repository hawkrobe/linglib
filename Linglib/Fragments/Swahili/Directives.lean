import Linglib.Typology.Directives

/-!
# Swahili imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Swahili

/-- Swahili: second-and-other-person morphological imperative (2SG bare stem
    *njoo!*, 2PL *njooni!*; subjunctive forms *tu-some* hortative,
    *a-some* jussive); Type 3 prohibitive (*usisome!* — special verb form
    [negative subjunctive] + normal negation strategy); all three (imperative
    + hortative + jussive); no dedicated optative. -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Swahili"
  , iso := "swh"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpNormalNeg
  , impHortSystem := .allThree
  , optative := some .absent
  , impForms := ["Njoo!", "Njooni!", "Usisome!"]
  , notes := "Bare stem 2SG imperative; subjunctive for hortative/jussive; " ++
             "prohibitive uses negative subjunctive (usi-)." }

end Fragments.Swahili
