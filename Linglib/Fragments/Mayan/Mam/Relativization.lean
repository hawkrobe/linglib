import Linglib.Syntax.RelativeClause.WALS

/-!
# Mam Relativization Profile

Relativization typology for Mam (ISO `mam`, Mayan), following
[elkins-torrence-brown-2026]: subjects relativize by gap (with Agent
Focus morphology) and obliques by gap (the *=(y)a'* clitic marking
oblique extraction), in a postnominal relative clause.
-/

namespace Mam

namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .gap
def oblStrategy : RelativeClause.OblStrategy := .gap
def rcPosition : RelativeClause.RCPosition := .postNominal
def lowestRelativizable : RelativeClause.AHPosition := .oblique
end Relativization

end Mam
