import Linglib.Typology.Pronouns

/-!
# Hungarian pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013}
-/

namespace Fragments.Hungarian

/-- Hungarian (Uralic). No incl/excl; no gender distinctions (ő for
    all genders); multiple politeness distinctions (te/Ön/maga);
    interrogative-based indefinites (valaki from val- 'some' + ki
    'who'); intensifier and reflexive identical (maga); person marking
    on adpositions for pronouns only (velem 'with-me'). -/
def pronounProfile : Typology.PronounProfile :=
  { language := "Hungarian"
  , family := "Uralic"
  , iso := "hun"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .noGenderDistinctions
  , politeness := some .multiple
  , indefiniteType := some .interrogativeBased
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .pronounsOnly }

/-- Hungarian pronoun phonological shape (WALS Chs 136–137): paradigmatic M-T
    (Uralic pattern, like Finnish); 1SG has /m/; no N-M; no /m/ in 2SG. -/
def pronounShapeProfile : Typology.PronounShapeProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , mtPronouns := some .paradigmatic
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent }

end Fragments.Hungarian
