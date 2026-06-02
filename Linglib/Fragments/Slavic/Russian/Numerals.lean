import Linglib.Typology.Numeral.WALS

/-!
# Russian numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Russian

/-- Russian: "first" (*pervyj*) suppletive, "second" (*vtoroj*) also
    suppletive, higher ordinals regular (*tretij* 'third', *chetvertyj*
    'fourth'). No morphological distributive (uses prepositional phrase
    *po + dative*). No numeral classifiers. *I* (and) differs from *vse*
    (all). Obligatory plural; decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Russian" "rus" (region := .europe) (pluralMarking := .obligatory)

end Russian
