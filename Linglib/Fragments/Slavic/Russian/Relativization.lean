import Linglib.Syntax.RelativeClause.WALS

/-!
# Russian relativization profile

Relativization typology for Russian (ISO `rus`).
-/

namespace Russian

/-! Russian relativization: declining relative pronoun *kotoryj*; all
    AH positions; postnominal RC. -/
namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .relativePronoun
def oblStrategy : RelativeClause.OblStrategy := .relativePronoun
def rcPosition : RelativeClause.RCPosition := .postNominal
def lowestRelativizable : RelativeClause.AHPosition := .objComparison
end Relativization

end Russian
