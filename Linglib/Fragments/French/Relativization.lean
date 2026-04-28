import Linglib.Core.Relativization.Profile

/-!
# French relativization profile

Typological-summary `RelativizationProfile` for French (ISO `fra`).
-/

namespace Fragments.French

/-- French relativization: relative pronoun system *qui* (SU), *que* (DO),
    *dont* (GEN), *lequel* (OBL); covers all AH positions; postnominal RC. -/
def relativization : Core.Relativization.RelativizationProfile :=
  { subjStrategy := .relativePronoun
  , oblStrategy := .relativePronoun
  , rcPosition := .postNominal
  , lowestRelativizable := .objComparison
  , notes := "Rel pronoun system: qui (SU), que (DO), dont (GEN), "
          ++ "lequel (OBL); all AH positions" }

end Fragments.French
