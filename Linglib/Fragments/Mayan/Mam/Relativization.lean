import Linglib.Syntax.RelativeClause.WALS

/-!
# Mam relativization profile
[elkins-torrence-brown-2026]

Typological-summary `RelativeClause.Profile` for Mam (ISO `mam`).
-/

namespace Mam

/-- Mam relativization: gap on subjects (with Agent Focus morphology);
    *=(y)a'* clitic marks oblique extraction; postnominal RC; Mayan. -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .gap
  , oblStrategy := .gap
  , rcPosition := .postNominal
  , lowestRelativizable := .oblique
  , notes := "Agent Focus for subject extraction; =(y)a' marks oblique "
          ++ "extraction; Mayan; [elkins-torrence-brown-2026]" }

end Mam
