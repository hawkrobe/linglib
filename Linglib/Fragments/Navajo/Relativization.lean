import Linglib.Typology.Relativization.Defs

/-!
# Navajo relativization profile

Typological-summary `RelativizationProfile` for Navajo (ISO `nav`).
-/

namespace Fragments.Navajo

/-- Navajo relativization: gap on subject and direct object; limited
    relativization on lower AH positions; pre-nominal RC; SOV. -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .gap
  , oblStrategy := .notRelativizable
  , rcPosition := .preNominal
  , lowestRelativizable := .directObject
  , notes := "Gap on subject/DO; limited relativization on lower AH "
          ++ "positions; pre-nominal RC; SOV language" }

end Fragments.Navajo
