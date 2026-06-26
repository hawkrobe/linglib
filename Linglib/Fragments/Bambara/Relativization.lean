import Linglib.Syntax.RelativeClause.WALS

/-!
# Bambara relativization profile

Typological-summary `RelativeClause.Profile` for Bambara (ISO `bam`).
-/

namespace Bambara

/-- Bambara relativization: internally-headed RC; non-reduction
    strategy; relativization limited to subject and direct object on AH;
    obliques not relativizable. -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .nonReduction
  , oblStrategy := .notRelativizable
  , rcPosition := .internallyHeaded
  , lowestRelativizable := .directObject
  , notes := "Internally-headed RC; non-reduction strategy; "
          ++ "limited to subject and direct object on AH" }

end Bambara
