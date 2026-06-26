import Linglib.Features.WordOrder

/-!
# Hindi/Urdu word-order profile

WALS-derived word-order profile for Hindi (ISO `hin`).
-/

namespace HindiUrdu

/-- Hindi word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : WordOrder.WordOrderProfile :=
  WordOrder.WordOrderProfile.ofWALS "hin"


set_option maxRecDepth 4096 in
/-- Drift sentinel: the profile is internally consistent (basic-order
    projections agree with svOrder and ovOrder when both are WALS-attested). -/
theorem wordOrder_consistent : wordOrder.IsConsistent := by decide

end HindiUrdu
