import Linglib.Typology.Directives

/-!
# Russian imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Slavic.Russian

/-- Russian: second-person-only morphological imperative (*idi!*, *idite!*);
    Type 1 prohibitive (*ne idi!* — regular *ne* negation with imperative);
    periphrastic hortative *davaj(te)* + infinitive/verb; no dedicated
    optative. -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Russian"
  , iso := "rus"
  , morphImp := .secondOnly
  , prohibitive := .normalImpNormalNeg
  , impHortSystem := .imperativeOnly
  , optative := some .absent
  , impForms := ["Idi!", "Idite!", "Ne idi!"]
  , notes := "Imperative suffix -i/-'te; prohibitive = ne + imperative; " ++
             "periphrastic hortative davaj(te)." }

end Fragments.Slavic.Russian
