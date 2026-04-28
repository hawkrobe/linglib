import Linglib.Typology.Directives

/-!
# Hindi-Urdu imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.HindiUrdu

/-- Hindi-Urdu: second-and-other-person morphological imperative with three
    politeness levels (*ja* intimate, *jao* familiar, *jaiye* polite, *jaae*
    3SG jussive); Type 2 prohibitive (*mat jao!* — special negative particle
    *mat*, distinct from declarative *nahin*); imperative + jussive (no
    hortative); no dedicated optative. -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , morphImp := .secondAndOther
  , prohibitive := .normalImpSpecialNeg
  , impHortSystem := .imperativeAndJussive
  , optative := some .absent
  , impForms := ["Ja!", "Jao!", "Jaiye!", "Mat jao!"]
  , notes := "Three politeness levels in imperative; prohibitive uses " ++
             "special mat (not nahin); 3SG jussive jaae." }

end Fragments.HindiUrdu
