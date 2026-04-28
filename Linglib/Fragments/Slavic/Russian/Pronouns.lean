import Linglib.Typology.Pronouns

/-!
# Russian pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013}
-/

namespace Fragments.Slavic.Russian

/-- Russian (Indo-European, Slavic). No incl/excl; gender in 3rd sg
    (on/ona/ono); binary politeness (ty/vy); interrogative-based
    indefinites (kto-to, kto-nibud'); intensifier (sam) differentiated
    from reflexive (sebja); no person marking on adpositions. -/
def pronounProfile : Typology.PronounProfile :=
  { language := "Russian"
  , family := "Indo-European"
  , iso := "rus"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdPersonSgOnly
  , politeness := some .binary
  , indefiniteType := some .interrogativeBased
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noPersonMarking }

/-- Russian pronoun phonological shape (WALS Chs 136–137): paradigmatic M-T
    (*menja*/*tebja*); 1SG has /m/; no N-M; no /m/ in 2SG. -/
def pronounShapeProfile : Typology.PronounShapeProfile :=
  { language := "Russian"
  , iso := "rus"
  , mtPronouns := some .paradigmatic
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent }

end Fragments.Slavic.Russian
