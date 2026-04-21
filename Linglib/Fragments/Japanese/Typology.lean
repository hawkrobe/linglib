import Linglib.Core.Typology.LanguageProfile
import Linglib.Fragments.Japanese.Morph

/-!
# Japanese typological profile

Aggregate WALS-style typological profile for Japanese (ISO 639-3 `jpn`).
-/

namespace Fragments.Japanese

open Core.Typology in
/-- Japanese: SOV, postpositional, canonical head-final. -/
def typology : LanguageProfile :=
  LanguageProfile.empty "jpn" "Japanese"
    |>.withWordOrderFromWALS
    |>.withAdpositionFromWALS
    |>.withMorph morphProfile

end Fragments.Japanese
