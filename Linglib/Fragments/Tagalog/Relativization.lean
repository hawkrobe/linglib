import Linglib.Typology.Relativization.Defs

/-!
# Tagalog relativization profile

Typological-summary `RelativizationProfile` for Tagalog (ISO `tgl`).
-/

namespace Fragments.Tagalog

/-- Tagalog relativization: gap on subjects (*ang*-phrase only); voice
    alternation required for non-subject relativization; linker *na/ng*;
    obliques not directly relativizable. -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .gap
  , oblStrategy := .notRelativizable
  , rcPosition := .postNominal
  , lowestRelativizable := .subject
  , notes := "Gap on subjects (ang-phrase only); voice alternation for "
          ++ "non-subject relativization; linker na/ng" }

end Fragments.Tagalog
