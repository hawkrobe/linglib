import Linglib.Syntax.RelativeClause.WALS

/-!
# Bambara relativization profile

Relativization typology for Bambara (ISO `bam`).
-/

namespace Bambara

/-! Bambara relativization: internally-headed RC; non-reduction
    strategy; relativization limited to subject and direct object on AH;
    obliques not relativizable. -/
namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .nonReduction
def oblStrategy : RelativeClause.OblStrategy := .notRelativizable
def rcPosition : RelativeClause.RCPosition := .internallyHeaded
def lowestRelativizable : RelativeClause.AHPosition := .directObject
end Relativization

end Bambara
