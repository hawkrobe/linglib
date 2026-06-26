import Linglib.Syntax.RelativeClause.WALS

/-!
# Navajo relativization profile

Relativization typology for Navajo (ISO `nav`).
-/

namespace Navajo

/-! Navajo relativization: gap on subject and direct object; limited
    relativization on lower AH positions; pre-nominal RC; SOV. -/
namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .gap
def oblStrategy : RelativeClause.OblStrategy := .notRelativizable
def rcPosition : RelativeClause.RCPosition := .preNominal
def lowestRelativizable : RelativeClause.AHPosition := .directObject
end Relativization

end Navajo
