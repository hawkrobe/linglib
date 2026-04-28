import Linglib.Typology.Pronouns

/-!
# Arabic (Egyptian) pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013}
-/

namespace Fragments.Arabic

/-- Egyptian Arabic (Afro-Asiatic, Semitic, ISO `arz`). No incl/excl;
    gender in 3rd AND 1st/2nd person (inta/inti, huwwa/hiyya); no
    politeness distinction in pronouns; generic-noun-based indefinites
    (hadd 'person' = 'someone'); intensifier/reflexive: WALS Ch 47 has
    no datum; person marking on adpositions for pronouns only (fi-ya
    'in-me'). -/
def pronounProfile : Typology.PronounProfile :=
  { language := "Arabic (Egyptian)"
  , family := "Afro-Asiatic"
  , iso := "arz"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdAndOtherPersons
  , politeness := some .none
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := Option.none
  , personMarkingAdpositions := some .pronounsOnly }

/-- Arabic (Egyptian) pronoun phonological shape (WALS Chs 136–137): no M-T;
    no /m/ in 1SG (*ana*); no N-M; no /m/ in 2SG. -/
def pronounShapeProfile : Typology.PronounShapeProfile :=
  { language := "Arabic (Egyptian)"
  , iso := "arz"
  , mtPronouns := some .absent
  , mIn1sg := some .absent
  , nmPronouns := some .absent
  , mIn2sg := some .absent }

end Fragments.Arabic
