import Linglib.Typology.Pronouns

/-!
# French pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013}
-/

namespace Fragments.French

/-- French (Indo-European, Romance). No incl/excl; gender in 3rd sg
    (il/elle); binary politeness (tu/vous); generic-noun-based
    indefinites (quelqu'un); intensifier (même) differentiated from
    reflexive (se); no person marking on adpositions. -/
def pronounProfile : Typology.PronounProfile :=
  { language := "French"
  , family := "Indo-European"
  , iso := "fra"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdPersonSgOnly
  , politeness := some .binary
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noPersonMarking }

/-- French pronoun phonological shape (WALS Chs 136–137): paradigmatic M-T
    (*moi*/*toi*); 1SG has /m/; no N-M; no /m/ in 2SG. -/
def pronounShapeProfile : Typology.PronounShapeProfile :=
  { language := "French"
  , iso := "fra"
  , mtPronouns := some .paradigmatic
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent }

end Fragments.French
