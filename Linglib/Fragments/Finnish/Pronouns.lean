import Linglib.Typology.Pronouns

/-!
# Finnish pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013}
-/

namespace Fragments.Finnish

/-- Finnish (Uralic). No incl/excl; no gender distinctions (hän for
    all genders); binary politeness (sinä/te); special indefinite
    forms (joku, jokin); intensifier and reflexive identical (itse);
    person marking on adpositions for pronouns only (kanssa-ni
    'with-me'). -/
def pronounProfile : Typology.PronounProfile :=
  { language := "Finnish"
  , family := "Uralic"
  , iso := "fin"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .noGenderDistinctions
  , politeness := some .binary
  , indefiniteType := some .special
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .pronounsOnly }

end Fragments.Finnish
