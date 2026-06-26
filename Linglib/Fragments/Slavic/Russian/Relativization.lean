import Linglib.Syntax.RelativeClause.WALS

/-!
# Russian relativization profile

Typological-summary `RelativeClause.Profile` for Russian (ISO `rus`).
-/

namespace Russian

/-- Russian relativization: declining relative pronoun *kotoryj*; all
    AH positions; postnominal RC. -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .relativePronoun
  , oblStrategy := .relativePronoun
  , rcPosition := .postNominal
  , lowestRelativizable := .objComparison
  , notes := "Rel pronoun kotoryj (declines); all AH positions" }

end Russian
