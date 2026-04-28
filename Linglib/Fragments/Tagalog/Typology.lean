import Linglib.Typology.LanguageProfile

/-!
# Tagalog typological profile

Aggregate WALS-style typological profile for Tagalog (ISO 639-3 `tgl`).
-/

namespace Fragments.Tagalog

open Typology in
/-- Tagalog: predicate-initial, voice-marking; subject-only relativization. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "tgl" "Tagalog"
    |>.withRelativization
        { subjStrategy := .gap
        , oblStrategy := .notRelativizable
        , rcPosition := .postNominal
        , lowestRelativizable := .subject
        , notes := "Gap on subjects (ang-phrase only); voice alternation for "
                ++ "non-subject relativization; linker na/ng" }

end Fragments.Tagalog
