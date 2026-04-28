import Linglib.Typology.Directives

/-!
# Turkish imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Turkish

/-- Turkish: full imperative paradigm (2SG *gel*, 2PL *gelin*, 3SG *gelsin*,
    3PL *gelsinler*, 1PL hortative *gelelim*); Type 1 prohibitive (*gelme!* —
    regular *-mA-* negation with imperative); all three (imperative + hortative
    + jussive); optative *-sA* suffix (desiderative/conditional). -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Turkish"
  , iso := "tur"
  , morphImp := .secondAndOther
  , prohibitive := .normalImpNormalNeg
  , impHortSystem := .allThree
  , optative := some .present
  , impForms := ["Gel!", "Gelin!", "Gelsin!", "Gelelim!", "Gelme!"]
  , notes := "Full imperative paradigm 2SG/2PL/3SG/3PL + hortative 1PL; " ++
             "optative -sA suffix; prohibitive with regular -mA- negation." }

end Fragments.Turkish
