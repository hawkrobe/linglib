import Linglib.Syntax.RelativeClause.WALS

/-!
# Hindi/Urdu relativization profile

Relativization typology for Hindi (ISO `hin`).
-/

namespace HindiUrdu

/-! Hindi/Urdu relativization: correlative jo...vo; relative pronoun jo
declines; correlative position; postnominal RC also possible in formal
register. -/
namespace Relativization
def subjStrategy : RelativeClause.SubjStrategy := .relativePronoun
def oblStrategy : RelativeClause.OblStrategy := .relativePronoun
def rcPosition : RelativeClause.RCPosition := .correlative
def lowestRelativizable : RelativeClause.AHPosition := .oblique
end Relativization

end HindiUrdu
