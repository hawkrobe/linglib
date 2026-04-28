import Linglib.Typology.Relativization.Defs

/-!
# Russian relativization profile

Typological-summary `RelativizationProfile` for Russian (ISO `rus`).
-/

namespace Fragments.Slavic.Russian

/-- Russian relativization: declining relative pronoun *kotoryj*; all
    AH positions; postnominal RC. -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .relativePronoun
  , oblStrategy := .relativePronoun
  , rcPosition := .postNominal
  , lowestRelativizable := .objComparison
  , notes := "Rel pronoun kotoryj (declines); all AH positions" }

end Fragments.Slavic.Russian
