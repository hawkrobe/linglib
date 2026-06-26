import Linglib.Syntax.RelativeClause.WALS

/-!
# Hindi/Urdu relativization profile

Typological-summary `RelativeClause.Profile` for Hindi (ISO `hin`).
-/

namespace HindiUrdu

/-- Hindi/Urdu relativization: correlative *jo...vo*; declining relative
    pronoun *jo*; correlative position; postnominal RC also possible in
    formal register. -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .relativePronoun
  , oblStrategy := .relativePronoun
  , rcPosition := .correlative
  , lowestRelativizable := .oblique
  , notes := "Correlative jo...vo; rel pronoun jo declines; "
          ++ "post-nominal RC also possible in formal register" }

end HindiUrdu
