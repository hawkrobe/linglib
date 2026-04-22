import Linglib.Core.Typology.LanguageProfile

/-!
# Malagasy typological profile

Aggregate WALS-style typological profile for Malagasy (ISO 639-3 `mlg`).
-/

namespace Fragments.Malagasy

open Core.Typology in
/-- Malagasy: VOS, prepositional; subject-only relativization. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "mlg" "Malagasy"
    |>.withRelativization
        { subjStrategy := .gap
        , oblStrategy := .notRelativizable
        , rcPosition := .postNominal
        , lowestRelativizable := .subject
        , notes := "Gap on subject only; voice alternation needed for "
                ++ "non-subject relativization; Austronesian pattern" }

end Fragments.Malagasy
