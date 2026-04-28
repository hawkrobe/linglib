import Linglib.Typology.Pronouns

/-!
# Mandarin pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013}
-/

namespace Fragments.Mandarin

/-- Mandarin (Sino-Tibetan). Inclusive/exclusive distinction in
    independent pronouns (women vs zanmen); no person marking on verbs;
    gender in 3rd sg only (ta with different characters); binary
    politeness (ni/nin); mixed indefinite strategy; intensifier and
    reflexive identical (ziji); no person marking on adpositions. -/
def pronounProfile : Typology.PronounProfile :=
  { language := "Mandarin"
  , family := "Sino-Tibetan"
  , iso := "cmn"
  , inclusiveExclusive := some .inclusiveExclusive
  , inclusiveExclusiveVerbal := some .noPersonMarking
  , genderInPronouns := some .in3rdPersonSgOnly
  , politeness := some .binary
  , indefiniteType := some .mixed
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .noPersonMarking }

end Fragments.Mandarin
