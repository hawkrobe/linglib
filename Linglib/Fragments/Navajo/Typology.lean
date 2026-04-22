import Linglib.Core.Typology.LanguageProfile

/-!
# Navajo typological profile

Aggregate WALS-style typological profile for Navajo (ISO 639-3 `nav`).

This is the only Navajo fragment in linglib at present.
-/

namespace Fragments.Navajo

open Core.Typology in
/-- Navajo: SOV, Athabaskan; pre-nominal RC; gap on SU/DO with limited
    relativization on lower AH positions. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "nav" "Navajo"
    |>.withRelativization
        { subjStrategy := .gap
        , oblStrategy := .notRelativizable
        , rcPosition := .preNominal
        , lowestRelativizable := .directObject
        , notes := "Gap on subject/DO; limited relativization on lower AH "
                ++ "positions; pre-nominal RC; SOV language" }

end Fragments.Navajo
