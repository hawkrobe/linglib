import Linglib.Typology.Directives

/-!
# Ancient Greek imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}

Diachronic variant kept distinct from Modern Greek under the
`Fragments.Greek.Ancient` namespace.
-/

namespace Fragments.Greek.Ancient

/-- Ancient Greek: second-and-other-person morphological imperative with
    present and aorist stems; Type 2 prohibitive (*mē graphe!* — normal
    imperative form + special negation *mē*, distinct from declarative
    *ou*/*ouk*); all three (imperative + hortative + jussive); rich optative
    mood paradigm (*graphoimi* 'may I write'). -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Ancient Greek"
  , iso := "grc"
  , morphImp := .secondAndOther
  , prohibitive := .normalImpSpecialNeg
  , impHortSystem := .allThree
  , optative := some .present
  , impForms := ["Graphe!", "Mē graphe!"]
  , notes := "Present and aorist imperative stems; special prohibitive " ++
             "mē (not ou); rich optative paradigm with dedicated morphology." }

end Fragments.Greek.Ancient
