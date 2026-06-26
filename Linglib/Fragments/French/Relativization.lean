import Linglib.Syntax.RelativeClause.WALS

/-!
# French relativization profile

Relativization typology for French (ISO `fra`).
-/

namespace French

/-! French relativization: relative pronoun system *qui* (SU), *que* (DO),
    *dont* (GEN), *lequel* (OBL); covers all AH positions; postnominal RC. -/
namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .relativePronoun
def oblStrategy : RelativeClause.OblStrategy := .relativePronoun
def rcPosition : RelativeClause.RCPosition := .postNominal
def lowestRelativizable : RelativeClause.AHPosition := .objComparison
end Relativization

end French
