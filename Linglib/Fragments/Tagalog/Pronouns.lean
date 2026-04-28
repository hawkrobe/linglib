import Linglib.Typology.Pronouns

/-!
# Tagalog pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013}
-/

namespace Fragments.Tagalog

/-- Tagalog (Austronesian, Philippine). Inclusive/exclusive in
    independent pronouns (kami vs tayo); no person marking on verbs
    (WALS); no gender distinctions (siya is gender-neutral); multiple
    politeness distinctions (ikaw/kayo/po); existential construction
    for indefinite reference; intensifier (mismo) differentiated from
    reflexive (sarili); no adpositions per WALS Ch 48. -/
def pronounProfile : Typology.PronounProfile :=
  { language := "Tagalog"
  , family := "Austronesian"
  , iso := "tgl"
  , inclusiveExclusive := some .inclusiveExclusive
  , inclusiveExclusiveVerbal := some .noPersonMarking
  , genderInPronouns := some .noGenderDistinctions
  , politeness := some .multiple
  , indefiniteType := some .existentialConstruction
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noAdpositions }

/-- Tagalog pronoun phonological shape (WALS Chs 136–137): no M-T; no /m/
    in 1SG (*ako*); no N-M; /m/ present in 2SG (*mo*). -/
def pronounShapeProfile : Typology.PronounShapeProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , mtPronouns := some .absent
  , mIn1sg := some .absent
  , nmPronouns := some .absent
  , mIn2sg := some .present }

end Fragments.Tagalog
