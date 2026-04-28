import Linglib.Typology.Plurals

/-!
# Tagalog plurality profile (WALS Chs 33–36)
@cite{wals-2013}
-/

namespace Fragments.Tagalog

/-- Tagalog: plural word (*mga*, prenominal), optional on all nouns;
    person-number stems in pronouns (*ako*/*kami*/*tayo*); unique periphrastic
    associative plural (*sina*: *sina Pedro* 'Pedro and associates'). -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , coding := .pluralWord
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .uniquePeriphrastic }

end Fragments.Tagalog
