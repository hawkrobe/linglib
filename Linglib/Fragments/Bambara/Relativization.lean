import Linglib.Typology.Relativization.Defs

/-!
# Bambara relativization profile

Typological-summary `RelativizationProfile` for Bambara (ISO `bam`).
-/

namespace Fragments.Bambara

/-- Bambara relativization: internally-headed RC; non-reduction
    strategy; relativization limited to subject and direct object on AH;
    obliques not relativizable. -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .nonReduction
  , oblStrategy := .notRelativizable
  , rcPosition := .internallyHeaded
  , lowestRelativizable := .directObject
  , notes := "Internally-headed RC; non-reduction strategy; "
          ++ "limited to subject and direct object on AH" }

end Fragments.Bambara
