import Linglib.Core.Typology.LanguageProfile

/-!
# Mam (SJO) typological profile

Aggregate WALS-style typological profile for Mam (ISO 639-3 `mam`).
@cite{elkins-torrence-brown-2026}.
-/

namespace Fragments.Mayan.Mam

open Core.Typology in
/-- Mam (SJO): VOS Mayan; ergative-absolutive; Agent-Focus extraction. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "mam" "Mam (SJO)"
    |>.withRelativization
        { subjStrategy := .gap
        , oblStrategy := .gap
        , rcPosition := .postNominal
        , lowestRelativizable := .oblique
        , notes := "Agent Focus for subject extraction; =(y)a' marks oblique "
                ++ "extraction; Mayan; @cite{elkins-torrence-brown-2026}" }

end Fragments.Mayan.Mam
