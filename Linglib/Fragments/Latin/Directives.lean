import Linglib.Typology.Directives

/-!
# Latin imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Latin

/-- Latin: full imperative paradigm (2SG *i*, 2PL *ite*, future imperatives;
    subjunctive *eamus* hortative 1PL, *eat* jussive 3SG); Type 4 prohibitive
    (*ne eas!* — special negation *ne* + subjunctive replacing imperative);
    all three (imperative + hortative + jussive); no dedicated optative
    (wishes via subjunctive). -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Latin"
  , iso := "lat"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpSpecialNeg
  , impHortSystem := .allThree
  , optative := some .absent
  , impForms := ["I!", "Ite!", "Eamus!", "Ne eas!"]
  , notes := "Future imperative (2SG -to, 3SG -to); prohibitive uses " ++
             "special ne (not non) + subjunctive (not imperative)." }

end Fragments.Latin
