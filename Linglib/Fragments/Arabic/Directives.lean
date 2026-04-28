import Linglib.Typology.Directives

/-!
# Arabic (Modern Standard) imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Arabic

/-- Arabic (Modern Standard): second-and-other-person morphological imperative
    (2SG.M *uktub!*, 2SG.F *uktubī!*; jussive *li-yaktub* 'let him write');
    Type 4 prohibitive (*lā taktub!* — special negation *lā* + jussive verb
    form, neither matching declarative); imperative + jussive (no hortative);
    no dedicated optative. -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Arabic (Modern Standard)"
  , iso := "arb"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpSpecialNeg
  , impHortSystem := .imperativeAndJussive
  , optative := some .absent
  , impForms := ["Uktub!", "Lā taktub!", "Li-yaktub"]
  , notes := "Imperative from jussive stem with initial vowel; " ++
             "prohibitive lā + jussive (not imperative); jussive for 3rd person." }

end Fragments.Arabic
