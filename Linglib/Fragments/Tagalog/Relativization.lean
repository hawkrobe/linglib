import Linglib.Syntax.RelativeClause.WALS

/-!
# Tagalog relativization profile

Typological-summary `RelativeClause.Profile` for Tagalog (ISO `tgl`).
-/

namespace Tagalog

/-- Tagalog relativization: gap on subjects (*ang*-phrase only); voice
    alternation required for non-subject relativization; linker *na/ng*;
    obliques not directly relativizable. -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .gap
  , oblStrategy := .notRelativizable
  , rcPosition := .postNominal
  , lowestRelativizable := .subject
  , notes := "Gap on subjects (ang-phrase only); voice alternation for "
          ++ "non-subject relativization; linker na/ng" }

end Tagalog
