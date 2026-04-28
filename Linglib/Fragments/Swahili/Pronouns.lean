import Linglib.Typology.Pronouns

/-!
# Swahili pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013}
-/

namespace Fragments.Swahili

/-- Swahili (Niger-Congo, Bantu). No incl/excl; gender in 3rd person
    only including non-singular (via the noun-class system); no
    politeness distinction in pronouns; generic-noun-based indefinites
    (mtu 'person' = 'someone'); intensifier (mwenyewe) differentiated
    from reflexive (ji-); no person marking on adpositions. -/
def pronounProfile : Typology.PronounProfile :=
  { language := "Swahili"
  , family := "Niger-Congo"
  , iso := "swh"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdPersonIncludingNonSg
  , politeness := some .none
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noPersonMarking }

/-- Swahili pronoun phonological shape (WALS Chs 136–137): no M-T pattern;
    1SG has /m/ in *mimi*; no N-M; no /m/ in 2SG. -/
def pronounShapeProfile : Typology.PronounShapeProfile :=
  { language := "Swahili"
  , iso := "swh"
  , mtPronouns := some .absent
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent }

end Fragments.Swahili
