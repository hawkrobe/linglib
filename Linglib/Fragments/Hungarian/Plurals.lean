import Linglib.Typology.Plurals

/-!
# Hungarian plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Hungarian

/-- Hungarian: suffix plural (`-k`), obligatory on all nouns; person-number
    stem + nominal plural affix on pronouns (*én* vs *mi*, with `-k` also on
    nouns); unique affixal associative plural (`-ék`: *Pál-ék* 'Paul and
    associates', distinct from additive `-k`/`-ak`). -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , coding := .suffix
  , occurrence := .allNounsAlwaysObligatory
  , pronounPlurality := .pnStemNominalAffix
  , associativePlural := .uniqueAffixal }

end Fragments.Hungarian
