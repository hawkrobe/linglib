import Linglib.Syntax.RelativeClause.WALS

/-!
# German relativization profile

Relativization typology for German (ISO `deu`).
-/

namespace German

/-! German relativization: relative pronoun der/die/das on both subjects
and obliques; postnominal RC; all AH positions relativizable. -/
namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .relativePronoun
def oblStrategy : RelativeClause.OblStrategy := .relativePronoun
def rcPosition : RelativeClause.RCPosition := .postNominal
def lowestRelativizable : RelativeClause.AHPosition := .objComparison
end Relativization

end German
