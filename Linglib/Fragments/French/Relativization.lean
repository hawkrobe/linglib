import Linglib.Syntax.RelativeClause.WALS

/-!
# French relativization profile

Typological-summary `RelativeClause.Profile` for French (ISO `fra`).
-/

namespace French

/-- French relativization: relative pronoun system *qui* (SU), *que* (DO),
    *dont* (GEN), *lequel* (OBL); covers all AH positions; postnominal RC. -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .relativePronoun
  , oblStrategy := .relativePronoun
  , rcPosition := .postNominal
  , lowestRelativizable := .objComparison
  , notes := "Rel pronoun system: qui (SU), que (DO), dont (GEN), "
          ++ "lequel (OBL); all AH positions" }

end French
