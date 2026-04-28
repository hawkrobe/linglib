import Linglib.Typology.Directives

/-!
# English imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.English

/-- English: second-person-only morphological imperative (*Go!*, *Be quiet!*) —
    typically the bare stem; Type 1 prohibitive (*Don't go!* — normal imperative
    with do-support negation); no dedicated hortative (periphrastic *Let's go*);
    no morphological optative (wishes via *may* or subjunctive relics like
    *Long live the king*). -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "English"
  , iso := "eng"
  , morphImp := .secondOnly
  , prohibitive := .normalImpNormalNeg
  , impHortSystem := .imperativeOnly
  , optative := some .absent
  , impForms := ["Go!", "Don't go!"]
  , notes := "Bare-stem imperative; periphrastic 'let's' for hortative; " ++
             "do-support in prohibitives." }

end Fragments.English
