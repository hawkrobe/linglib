import Linglib.Syntax.RelativeClause.WALS

/-!
# German relativization profile

Typological-summary `RelativeClause.Profile` for German (ISO `deu`).
-/

namespace German

/-- German relativization: relative pronoun *der/die/das* on both
    subjects and obliques; postnominal RC; all AH positions
    relativizable. -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .relativePronoun
  , oblStrategy := .relativePronoun
  , rcPosition := .postNominal
  , lowestRelativizable := .objComparison
  , notes := "Relative pronoun der/die/das; all AH positions relativizable" }

end German
