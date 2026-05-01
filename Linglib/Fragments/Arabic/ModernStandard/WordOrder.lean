import Linglib.Typology.WordOrder

/-!
# Arabic word-order profile

WALS-derived word-order profile for Modern Standard Arabic (ISO `arb`).
-/

namespace Fragments.Arabic.ModernStandard

/-- Arabic word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "arb"


set_option maxRecDepth 4096 in
/-- Drift sentinel: the profile is internally consistent (basic-order
    projections agree with svOrder and ovOrder when both are WALS-attested). -/
theorem wordOrder_consistent : wordOrder.IsConsistent := by decide

end Fragments.Arabic.ModernStandard
