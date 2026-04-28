import Linglib.Core.Relativization.Profile

/-!
# German relativization profile

Typological-summary `RelativizationProfile` for German (ISO `deu`).
-/

namespace Fragments.German

/-- German relativization: relative pronoun *der/die/das* on both
    subjects and obliques; postnominal RC; all AH positions
    relativizable. -/
def relativization : Core.Relativization.RelativizationProfile :=
  { subjStrategy := .relativePronoun
  , oblStrategy := .relativePronoun
  , rcPosition := .postNominal
  , lowestRelativizable := .objComparison
  , notes := "Relative pronoun der/die/das; all AH positions relativizable" }

end Fragments.German
