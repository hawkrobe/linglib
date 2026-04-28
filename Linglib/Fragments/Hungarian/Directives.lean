import Linglib.Typology.Directives

/-!
# Hungarian imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Hungarian

/-- Hungarian: second-person-only morphological imperative (*menj!*,
    *menjetek!*); Type 1 prohibitive (*ne menj!* — regular *ne* negation
    with imperative/subjunctive form); imperative + jussive (subjunctive
    serves as 3SG/3PL jussive); no dedicated optative. -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , morphImp := .secondOnly
  , prohibitive := .normalImpNormalNeg
  , impHortSystem := .imperativeAndJussive
  , optative := some .absent
  , impForms := ["Menj!", "Menjetek!", "Ne menj!"]
  , notes := "Imperative/subjunctive paradigm; prohibitive = ne + " ++
             "imperative; subjunctive used for 3SG/3PL jussive." }

end Fragments.Hungarian
