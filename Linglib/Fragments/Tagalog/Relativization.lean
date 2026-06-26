import Linglib.Syntax.RelativeClause.WALS

/-!
# Tagalog relativization profile

Typological-summary relativization fields for Tagalog (ISO `tgl`), as a
`Tagalog.Relativization` namespace of bare `RelativeClause.*` defs.
-/

namespace Tagalog

/-! Tagalog relativization: gap on subjects (*ang*-phrase only); voice
alternation required for non-subject relativization; linker *na ~ ng*;
obliques not directly relativizable. -/
namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .gap
def oblStrategy : RelativeClause.OblStrategy := .notRelativizable
def rcPosition : RelativeClause.RCPosition := .postNominal
def lowestRelativizable : RelativeClause.AHPosition := .subject
end Relativization

end Tagalog
