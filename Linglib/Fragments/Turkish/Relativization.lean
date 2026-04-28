import Linglib.Typology.Relativization.Defs

/-!
# Turkish relativization profile

Typological-summary `RelativizationProfile` for Turkish (ISO `tur`).
-/

namespace Fragments.Turkish

/-- Turkish relativization: gap throughout; participial suffixes *-en*
    (SU) and *-dik* (non-SU); pre-nominal RC. -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .gap
  , oblStrategy := .gap
  , rcPosition := .preNominal
  , lowestRelativizable := .oblique
  , notes := "Gap strategy; participial suffixes -en (SU), -dik (non-SU); "
          ++ "pre-nominal RC" }

end Fragments.Turkish
