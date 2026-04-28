import Linglib.Typology.Directives

/-!
# Tagalog imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Tagalog

/-- Tagalog: no morphological imperative in the strict sense (commands use
    the basic/infinitive verb form); Type 2 prohibitive (*Huwag kang
    pumunta!* — special negative *huwag*, distinct from declarative *hindi*);
    periphrastic hortative *tayo na*; no optative. -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , morphImp := .noMorphological
  , prohibitive := .normalImpSpecialNeg
  , impHortSystem := .imperativeOnly
  , optative := some .absent
  , impForms := ["Pumunta ka!", "Huwag kang pumunta!"]
  , notes := "Imperative = basic/infinitive verb form; special prohibitive " ++
             "huwag (not hindi); no morphological hortative." }

end Fragments.Tagalog
