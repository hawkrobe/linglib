import Linglib.Typology.Directives

/-!
# Georgian imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Georgian

/-- Georgian: second-and-other-person morphological imperative within a
    complex verbal system featuring imperative, optative, and conjunctive
    moods; Type 4 prohibitive (preverb *nu-* + conjunctive — special verb
    form + special construction); all three (imperative + hortative + jussive);
    morphologically dedicated optative mood. -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Georgian"
  , iso := "kat"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpSpecialNeg
  , impHortSystem := .allThree
  , optative := some .present
  , impForms := ["Ts'ere!", "Nu ts'er!"]
  , notes := "Complex verbal morphology with multiple mood series; " ++
             "dedicated optative mood; prohibitive uses conjunctive." }

end Fragments.Georgian
