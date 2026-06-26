import Linglib.Syntax.RelativeClause.WALS

/-!
# Turkish relativization profile

Typological-summary relativization fields for Turkish (ISO `tur`), as a
`Turkish.Relativization` namespace of bare `RelativeClause.*` defs.
-/

namespace Turkish

/-! Turkish relativization: gap throughout; participial suffixes *-en*
(SU) and *-dik* (non-SU); pre-nominal RC. -/
namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .gap
def oblStrategy : RelativeClause.OblStrategy := .gap
def rcPosition : RelativeClause.RCPosition := .preNominal
def lowestRelativizable : RelativeClause.AHPosition := .oblique
end Relativization

end Turkish
