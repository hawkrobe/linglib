import Linglib.Syntax.RelativeClause.WALS

/-!
# Japanese relativization profile

Relativization typology for Japanese (ISO `jpn`).
-/

namespace Japanese

/-! Japanese relativization: gap throughout; pre-nominal RC; no relative
pronoun; genitive position relativizable but rare. -/
namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .gap
def oblStrategy : RelativeClause.OblStrategy := .gap
def rcPosition : RelativeClause.RCPosition := .preNominal
def lowestRelativizable : RelativeClause.AHPosition := .genitive
end Relativization

end Japanese
