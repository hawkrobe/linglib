import Linglib.Syntax.RelativeClause.WALS

/-!
# Mam relativization profile
[elkins-torrence-brown-2026]

Relativization typology for Mam (ISO `mam`).
-/

namespace Mam

/-! Mam relativization: gap on subjects (with Agent Focus morphology);
    *=(y)a'* clitic marks oblique extraction; postnominal RC; Mayan;
    [elkins-torrence-brown-2026]. -/
namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .gap
def oblStrategy : RelativeClause.OblStrategy := .gap
def rcPosition : RelativeClause.RCPosition := .postNominal
def lowestRelativizable : RelativeClause.AHPosition := .oblique
end Relativization

end Mam
