import Linglib.Syntax.RelativeClause.WALS

/-!
# Japanese relativization profile

Typological-summary `RelativeClause.Profile` for Japanese (ISO `jpn`).
-/

namespace Japanese

/-- Japanese relativization: gap throughout; pre-nominal RC; no relative
    pronoun; genitive position relativizable but rare. -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .gap
  , oblStrategy := .gap
  , rcPosition := .preNominal
  , lowestRelativizable := .genitive
  , notes := "Gap strategy throughout; pre-nominal RC; no relative "
          ++ "pronoun; genitive relativization possible but rare" }

end Japanese
