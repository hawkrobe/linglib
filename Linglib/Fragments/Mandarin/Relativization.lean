import Linglib.Syntax.RelativeClause.WALS

/-!
# Mandarin relativization profile

Typological-summary `RelativeClause.Profile` for Mandarin (ISO `cmn`).
-/

namespace Mandarin

/-- Mandarin relativization: gap + relativizer *de*; pre-nominal RC
    (SVO main clause but RC-N order). -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .gap
  , oblStrategy := .gap
  , rcPosition := .preNominal
  , lowestRelativizable := .oblique
  , notes := "Gap + relativizer de; pre-nominal RC; SVO but RC-N order" }

end Mandarin
