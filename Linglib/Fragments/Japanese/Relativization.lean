import Linglib.Core.Relativization.Profile

/-!
# Japanese relativization profile

Typological-summary `RelativizationProfile` for Japanese (ISO `jpn`).
-/

namespace Fragments.Japanese

/-- Japanese relativization: gap throughout; pre-nominal RC; no relative
    pronoun; genitive position relativizable but rare. -/
def relativization : Core.Relativization.RelativizationProfile :=
  { subjStrategy := .gap
  , oblStrategy := .gap
  , rcPosition := .preNominal
  , lowestRelativizable := .genitive
  , notes := "Gap strategy throughout; pre-nominal RC; no relative "
          ++ "pronoun; genitive relativization possible but rare" }

end Fragments.Japanese
