import Linglib.Syntax.RelativeClause.WALS

/-!
# Turkish relativization profile

Typological-summary `RelativeClause.Profile` for Turkish (ISO `tur`).
-/

namespace Turkish

/-- Turkish relativization: gap throughout; participial suffixes *-en*
    (SU) and *-dik* (non-SU); pre-nominal RC. -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .gap
  , oblStrategy := .gap
  , rcPosition := .preNominal
  , lowestRelativizable := .oblique
  , notes := "Gap strategy; participial suffixes -en (SU), -dik (non-SU); "
          ++ "pre-nominal RC" }

end Turkish
