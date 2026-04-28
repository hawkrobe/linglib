import Linglib.Typology.Directives

/-!
# Quechua (Cuzco) imperative profile (WALS Chs 70, 71, 72, 73)
@cite{wals-2013}
-/

namespace Fragments.Quechua

/-- Quechua (Cuzco): rich morphological imperative paradigm (2SG *-y* in
    *ri-y!*, 2PL *-ychis*; hortative *-sun* in *ri-sun*; jussive *-chun* in
    *ri-chun*); Type 4 prohibitive (*ama ri-y-chu!* — both prohibitive marker
    *ama* and prohibitive suffix *-chu* are special); all three; dedicated
    optative (desiderative) suffix. -/
def directiveProfile : Typology.ImperativeProfile :=
  { language := "Quechua (Cuzco)"
  , iso := "quz"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpSpecialNeg
  , impHortSystem := .allThree
  , optative := some .present
  , impForms := ["Ri-y!", "Ri-sun!", "Ri-chun!", "Ama ri-y-chu!"]
  , notes := "Rich imperative paradigm; hortative -sun; jussive -chun; " ++
             "prohibitive ama...chu is doubly special." }

end Fragments.Quechua
