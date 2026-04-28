import Linglib.Typology.Relativization.Defs

/-!
# Mam relativization profile
@cite{elkins-torrence-brown-2026}

Typological-summary `RelativizationProfile` for Mam (ISO `mam`).
-/

namespace Fragments.Mayan.Mam

/-- Mam relativization: gap on subjects (with Agent Focus morphology);
    *=(y)a'* clitic marks oblique extraction; postnominal RC; Mayan. -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .gap
  , oblStrategy := .gap
  , rcPosition := .postNominal
  , lowestRelativizable := .oblique
  , notes := "Agent Focus for subject extraction; =(y)a' marks oblique "
          ++ "extraction; Mayan; @cite{elkins-torrence-brown-2026}" }

end Fragments.Mayan.Mam
