import Linglib.Features.WordOrder

/-!
# German word-order profile

WALS-derived word-order profile for German (ISO `deu`). German is
classified as having no dominant word order in WALS Ch 81/83.
-/

namespace German

/-- German word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : WordOrder.WordOrderProfile :=
  WordOrder.WordOrderProfile.ofWALS "deu"


set_option maxRecDepth 4096 in
/-- Drift sentinel: the profile is internally consistent (basic-order
    projections agree with svOrder and ovOrder when both are WALS-attested). -/
theorem wordOrder_consistent : wordOrder.IsConsistent := by decide

end German
