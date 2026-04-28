import Linglib.Typology.Directives

/-!
# Italian imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Italian

/-- Italian: second-person morphological imperative (2SG *va'!*, 2PL *andate!*);
    Type 3 prohibitive (*Non andare!* — regular *non* negation, but with
    infinitive replacing imperative for 2SG; 2PL retains imperative);
    imperative + jussive (3SG/3PL subjunctive); no dedicated optative
    (subjunctive covers wishes). -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Italian"
  , iso := "ita"
  , morphImp := .secondOnly
  , prohibitive := .specialImpNormalNeg
  , impHortSystem := .imperativeAndJussive
  , optative := some .absent
  , impForms := ["Va'!", "Andate!", "Non andare!"]
  , notes := "2SG prohibitive uses infinitive (not imperative): " ++
             "non andare, not *non va'; 2PL retains imperative: non andate." }

end Fragments.Italian
