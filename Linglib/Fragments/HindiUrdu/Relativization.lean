import Linglib.Core.Relativization.Profile

/-!
# Hindi/Urdu relativization profile

Typological-summary `RelativizationProfile` for Hindi (ISO `hin`).
-/

namespace Fragments.HindiUrdu

/-- Hindi/Urdu relativization: correlative *jo...vo*; declining relative
    pronoun *jo*; correlative position; postnominal RC also possible in
    formal register. -/
def relativization : Core.Relativization.RelativizationProfile :=
  { subjStrategy := .relativePronoun
  , oblStrategy := .relativePronoun
  , rcPosition := .correlative
  , lowestRelativizable := .oblique
  , notes := "Correlative jo...vo; rel pronoun jo declines; "
          ++ "post-nominal RC also possible in formal register" }

end Fragments.HindiUrdu
