import Linglib.Syntax.RelativeClause.WALS

/-!
# Navajo relativization profile

Typological-summary `RelativeClause.Profile` for Navajo (ISO `nav`).
-/

namespace Navajo

/-- Navajo relativization: gap on subject and direct object; limited
    relativization on lower AH positions; pre-nominal RC; SOV. -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .gap
  , oblStrategy := .notRelativizable
  , rcPosition := .preNominal
  , lowestRelativizable := .directObject
  , notes := "Gap on subject/DO; limited relativization on lower AH "
          ++ "positions; pre-nominal RC; SOV language" }

end Navajo
