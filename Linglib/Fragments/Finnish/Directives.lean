import Linglib.Typology.Directives

/-!
# Finnish imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Finnish

/-- Finnish: second-person morphological imperative (*mene!*, *menkää!*);
    Type 3 prohibitive (*älä mene* — imperative form of negative auxiliary
    *ei* + connegative; verb form changes from imperative to connegative);
    all three (imperative + hortative + jussive *menköön*); no dedicated
    optative (conditional *-isi-* serves optative functions). -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Finnish"
  , iso := "fin"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpNormalNeg
  , impHortSystem := .allThree
  , optative := some .absent
  , impForms := ["Mene!", "Menkää!", "Älä mene!"]
  , notes := "Negative auxiliary verb has its own imperative form älä; " ++
             "connegative in prohibitive; 3SG jussive menköön." }

end Fragments.Finnish
