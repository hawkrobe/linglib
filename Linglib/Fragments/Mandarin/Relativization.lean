import Linglib.Typology.Relativization.Defs

/-!
# Mandarin relativization profile

Typological-summary `RelativizationProfile` for Mandarin (ISO `cmn`).
-/

namespace Fragments.Mandarin

/-- Mandarin relativization: gap + relativizer *de*; pre-nominal RC
    (SVO main clause but RC-N order). -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .gap
  , oblStrategy := .gap
  , rcPosition := .preNominal
  , lowestRelativizable := .oblique
  , notes := "Gap + relativizer de; pre-nominal RC; SVO but RC-N order" }

end Fragments.Mandarin
