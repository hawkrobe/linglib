import Linglib.Syntax.RelativeClause.WALS

/-!
# Mandarin relativization profile

Relativization typology for Mandarin (ISO `cmn`).
-/

namespace Mandarin

/-! Mandarin relativization: gap + relativizer *de*; pre-nominal RC
    (SVO main clause but RC-N order). -/
namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .gap
def oblStrategy : RelativeClause.OblStrategy := .gap
def rcPosition : RelativeClause.RCPosition := .preNominal
def lowestRelativizable : RelativeClause.AHPosition := .oblique
end Relativization

end Mandarin
